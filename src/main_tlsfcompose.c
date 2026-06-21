/// tlsfcompose — a self-contained decomposed-synthesis plan.
///
/// Runs cover -> recognize -> certify -> compose, then emits everything needed
/// to synthesize the whole spec by decomposition: the exact *combinational*
/// controllers it already certified (`o := value`), and the rest of the spec as
/// independent residual clusters (output-disjoint, so `E -> AND Gi == AND
/// (E -> Gi)`), one LTL job each.  With --output-dir it also writes a
/// compose.sh that runs `ltlsynt` per cluster.  The spec is realizable iff
/// every cluster is; a full controller is the emitted controllers plus one per
/// cluster.
///
/// Text plans do not spawn processes: backend calls live in compose.sh.
/// `--aiger` runs the selected synthesis backend immediately for each cluster.

// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/aiger.h"
#include "tlsf/ast.h"
#include "tlsf/build_info.h"
#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/gr.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/recognize.h"
#include "tlsf/residual.h"
#include "tlsf/residual_plan.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include "compose_internal.h"
#include "compose_route.h"

#include <ctype.h>
#include <fcntl.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Decomposed-synthesis plan: certified controllers + residual "
      "clusters.\n"
      "  --split                      decompose constraints first\n"
      "  --aiger                      emit one merged controller (AIGER aag)"
      " via OxiDD + ltlsynt backends\n"
      "  --ltlsynt PATH               ltlsynt to use for --aiger (default: "
      "$LTLSYNT or PATH)\n"
      "  --experimental-bounded N     enable bounded-liveness heuristic with "
      "step bound N\n"
      "  --route-stats                print residual-cluster route diagnostics "
      "and exit\n"
      "  --verify PROG                self-verify each OxiDD-synthesized "
      "controller (PROG --aiger F --formula L; exit 1 = violation) and fall "
      "back to ltlsynt ($TLSFCOMPOSE_VERIFY)\n"
      "  --format ltlxba|ltl          output dialect (default ltlxba)\n"
      "  --output-dir DIR             write controllers.txt, cluster.<k>"
      ".ltl, compose.sh\n"
      "  --overwrite-semantics VALUE  replace SEMANTICS\n"
      "  --overwrite-target VALUE     replace TARGET\n"
      "  --param NAME=VALUE           override a parameter (repeatable)\n"
      "  --output FILE                write the plan to FILE (default "
      "stdout)\n"
      "  --version, --help\n",
      prog);
}

static const char *route_kind_name(ComposeRouteKind kind) {
  switch (kind) {
  case ROUTE_OUTPUT_FREE_LTLSYNT:
    return "output-free";
  case ROUTE_DIRECT_SAFETY:
    return "direct-safety";
  case ROUTE_STRICT_SAFETY:
    return "strict-safety";
  case ROUTE_WR_SAFETY:
    return "wr-safety";
  case ROUTE_BOUNDED_EXPERIMENTAL:
    return "bounded-experimental";
  case ROUTE_GR1:
    return "gr1";
  case ROUTE_LTLSYNT:
    return "ltlsynt";
  default:
    return "unknown";
  }
}

static const char *route_stats_reason(const ComposeRoute *route, bool finite,
                                      char *buf, size_t buf_sz) {
  switch (route->kind) {
  case ROUTE_OUTPUT_FREE_LTLSYNT:
    snprintf(buf, buf_sz, "output-free guarantee check");
    break;
  case ROUTE_DIRECT_SAFETY:
  case ROUTE_STRICT_SAFETY:
  case ROUTE_WR_SAFETY:
  case ROUTE_GR1:
    snprintf(buf, buf_sz, "selected exact fast path");
    break;
  case ROUTE_BOUNDED_EXPERIMENTAL:
    snprintf(buf, buf_sz, "selected explicit experimental bounded path");
    break;
  case ROUTE_LTLSYNT:
  default:
    (void)cluster_ltlsynt_reason(&route->shape, finite, buf, buf_sz);
    break;
  }
  return buf;
}

static bool emit_route_stats(FILE *out, TlsfSpec *spec, ConstraintCover *cov,
                             const ResidualPlan *rplan, bool finite,
                             uint32_t bound_k, bool *seen) {
  fprintf(out, "cluster\touts\tins\tnodes\tgr_level\thas_liveness\thas_wr\t"
               "has_release\troute\tbackend\treason\n");
  for (uint32_t k = 0; k < rplan->nclusters; k++) {
    bool output_free = rplan->keys[k] == cov->aps.count;
    Node *root = residual_plan_build_cluster(spec, cov, rplan, rplan->keys[k],
                                             /*all=*/false,
                                             /*prune=*/!output_free, seen);
    if (!root) {
      fprintf(stderr, "tlsfcompose: out of memory\n");
      return false;
    }
    ComposeRoute route;
    if (output_free) {
      route = (ComposeRoute){
          .kind = ROUTE_OUTPUT_FREE_LTLSYNT,
          .uses_oxidd = false,
          .exact = true,
          .label = "ltlsynt",
          .shape = cluster_shape(spec, root),
          .root = root,
      };
    } else {
      (void)compose_route_select(spec, root, finite, bound_k, &route);
    }
    char reason[192];
    fprintf(out, "%u\t", k);
    residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
    fprintf(out, "\t");
    residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
    fprintf(out, "\t%u\t%d\t%d\t%d\t%d\t%s\t%s\t%s\n", ast_node_count(root),
            route.shape.gr_level, route.shape.has_liveness ? 1 : 0,
            route.shape.has_weak_until ? 1 : 0, route.shape.has_release ? 1 : 0,
            route_kind_name(route.kind), route.label ? route.label : "ltlsynt",
            route_stats_reason(&route, finite, reason, sizeof reason));
  }
  return true;
}

static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsfcompose: bad --param '%s'\n", s);
    return false;
  }
  size_t nlen = (size_t)(eq - s);
  char *name = malloc(nlen + 1);
  if (!name)
    return false;
  memcpy(name, s, nlen);
  name[nlen] = '\0';
  char *end;
  long long val = strtoll(eq + 1, &end, 10);
  if (*end != '\0') {
    fprintf(stderr, "tlsfcompose: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

static void compose_sh_header(FILE *sh) {
  fprintf(sh,
          "#!/bin/sh\n"
          "# Generated by tlsfcompose: synthesize each residual cluster with\n"
          "# ltlsynt.  controllers.txt holds the combinational part (already\n"
          "# solved, exact).  The spec is realizable iff every cluster is.\n"
          "dir=$(CDPATH= cd -- \"$(dirname -- \"$0\")\" && pwd)\n"
          "ok=1\n"
          "run() {\n"
          "  ltl=$(grep -v '^c ' \"$dir/$1\")\n"
          "  if ltlsynt --ins=\"$2\" --outs=\"$3\" --formula=\"$ltl\" "
          "--realizability >/dev/null 2>&1; then\n"
          "    echo \"$1: REALIZABLE\"\n"
          "  else\n"
          "    echo \"$1: UNREALIZABLE\"; ok=0\n"
          "  fi\n"
          "}\n");
}

int main(int argc, char *argv[]) {
  bool split = false, aiger = false, route_stats = false;
  LtlFormat fmt = LTL_FMT_LTLXBA;
  const char *input_file = nullptr, *output_file = nullptr, *out_dir = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr, *ltlsynt_path = nullptr;
  const char *verify_path = nullptr;
  unsigned long bound_opt = 0; // 0 = bounded-liveness heuristic disabled
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfcompose: %s requires an argument\n",    \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--aiger") == 0) {
      aiger = true;
    } else if (strcmp(a, "--ltlsynt") == 0) {
      ltlsynt_path = NEED_ARG();
    } else if (strcmp(a, "--verify") == 0) {
      verify_path = NEED_ARG();
    } else if (strcmp(a, "--experimental-bounded") == 0) {
      const char *v = NEED_ARG();
      char *end;
      bound_opt = strtoul(v, &end, 10);
      if (*end != '\0' || bound_opt == 0) {
        fprintf(stderr,
                "tlsfcompose: --experimental-bounded expects a positive "
                "integer\n");
        return 1;
      }
    } else if (strcmp(a, "--route-stats") == 0) {
      route_stats = true;
    } else if (strcmp(a, "--output-dir") == 0) {
      out_dir = NEED_ARG();
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "ltlxba"))
        fmt = LTL_FMT_LTLXBA;
      else if (!strcmp(v, "ltl"))
        fmt = LTL_FMT_LTL;
      else {
        fprintf(stderr, "tlsfcompose: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfcompose: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfcompose %s oxidd=%s research=%s simd=%s\n",
             TLSF_PROJECT_VERSION, tlsf_build_oxidd(), tlsf_build_research(),
             tlsf_build_simd());
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfcompose: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfcompose: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsfcompose");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfcompose");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfcompose: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfcompose: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (!spec_validate_semantics(spec, "tlsfcompose")) {
    spec_free(spec);
    return 1;
  }
  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  ConstraintCover *cov = cover_build(spec, split);
  if (!cov) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    spec_free(spec);
    return 1;
  }
  recognize_all(cov);
  Csnf *csnf = templates_certify(cov, TPL_ALL, true);
  CsnfComposition *comp = csnf ? csnf_compose(csnf) : nullptr;
  if (!csnf || !comp) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  FILE *out = cli_open_output(output_file, "tlsfcompose");
  if (!out) {
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  uint32_t A = cov->aps.count;
  bool finite = semantics_is_finite(spec->info.semantics);
  int rc = 0;

  ResidualPlanOptions ropts = {.skip_local_aiger = aiger,
                               .simplify_weak = true};
  ResidualPlan *rplan = residual_plan_build(spec, cov, csnf, comp, ropts);
  if (!rplan) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }
  uint32_t K = rplan->nclusters;
  bool *seen = calloc(A ? A : 1, sizeof(bool));
  if (!seen) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    residual_plan_free(rplan);
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  if (route_stats) {
    uint32_t bound_k = (uint32_t)bound_opt;
    rc = emit_route_stats(out, spec, cov, rplan, finite, bound_k, seen) ? 0 : 1;
    free(seen);
    residual_plan_free(rplan);
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return rc;
  }

  // --aiger: synthesize each cluster with ltlsynt and merge with the
  // combinational controllers into one AIGER controller over the full
  // interface.
  if (aiger) {
    const char *env = getenv("LTLSYNT");
    const char *prog = ltlsynt_path    ? ltlsynt_path
                       : (env && *env) ? env
                                       : "ltlsynt";
    // Optional self-verification: when set, each OxiDD-synthesized cluster
    // controller is model-checked against the cluster spec and, if it provably
    // violates it, discarded in favour of the ltlsynt fallback.
    const char *verify_env = getenv("TLSFCOMPOSE_VERIFY");
    const char *verifier = verify_path                   ? verify_path
                           : (verify_env && *verify_env) ? verify_env
                                                         : nullptr;
    uint32_t bound_k = (uint32_t)bound_opt;
    // Persistent BDD manager: one allocation shared across all clusters,
    // amortising oxidd_bdd_manager_new overhead on multi-cluster specs.
    // Variables accumulate with per-cluster base offsets; GC reclaims dead
    // nodes between clusters.  Cap at 1<<22 (4M nodes / ~96-160MB RSS).
    oxidd_session_init(1u << 22, 1u << 22);

    Aig *g = aig_new();
    for (uint32_t o = 0; o < A; o++) // all declared and residual env inputs
      if (residual_signal_matches(cov, o, AP_FLAG_INPUT))
        (void)aig_input(g, ap_table_name(&cov->aps, o));

    // Clusters first (so a decoder reading a synthesized output resolves).
    for (uint32_t k = 0; k < K && rc == 0; k++) {
      if (rplan->keys[k] == A) {
        // Output-free cluster: input-only system guarantees with no controller
        // to emit.  These are NOT trivially satisfiable -- the system meets
        // them only if the assumptions entail them -- so check realizability
        // rather than dropping the cluster.  Dropping is unsound: e.g.
        // G(o && a) splits into G(o) and the input-only G(a); skipping G(a)
        // reports a genuinely unrealizable spec as realizable.  In isolation
        // the system has full control of any outputs this cluster references
        // via assumptions, so UNREALIZABLE here soundly implies the whole spec
        // is unrealizable.  We use only the verdict: any referenced outputs are
        // driven by their owning clusters, so nothing is merged.
        Node *ofree = residual_plan_build_cluster(
            spec, cov, rplan, A, /*all=*/false, /*prune=*/false, seen);
        if (!ofree) {
          rc = 1;
          break;
        }
        int of_unreal = 0;
        Aig *of_sub = run_ltlsynt_cluster(prog, cov, seen, ofree, fmt, finite,
                                          &of_unreal);
        if (getenv("TLSFCOMPOSE_DEBUG"))
          fprintf(stderr, "tlsfcompose: output-free cluster checked (%s)\n",
                  of_unreal ? "UNREALIZABLE"
                  : of_sub  ? "realizable"
                            : "realizable/unknown");
        if (of_unreal) {
          fprintf(stderr, "tlsfcompose: output-free guarantee cluster is "
                          "UNREALIZABLE (ltlsynt)\n");
          rc = 1;
        }
        aig_free(of_sub);
        continue;
      }
      Node *root =
          residual_plan_build_cluster(spec, cov, rplan, rplan->keys[k],
                                      /*all=*/false, /*prune=*/true, seen);
      if (!root) {
        rc = 1;
        break;
      }
      int unreal = 0;
      ComposeRoute route;
      (void)compose_route_select(spec, root, finite, bound_k, &route);
      bool use_oxidd = false;
      const char *backend = nullptr;
      Aig *sub = compose_route_solve(&route, prog, cov, seen, fmt, finite,
                                     &unreal, &use_oxidd, &backend);
      // Self-verification gate: a synthesized controller must satisfy the
      // ORIGINAL cluster spec (`root`, not a bounded/strict surrogate).  If it
      // provably violates it, discard it and fall back to ltlsynt, so a
      // recognizer/encoder bug becomes a sound fallback rather than a wrong
      // controller.  Inconclusive checks (verifier error/OOM) keep the result.
      if (verifier && use_oxidd && sub &&
          controller_violates_spec(verifier, sub, root, fmt, finite)) {
        fprintf(stderr,
                "tlsfcompose: cluster %u controller failed self-verification "
                "(%s); falling back to ltlsynt\n",
                k, backend);
        aig_free(sub);
        sub = nullptr;
        unreal = 0;
        use_oxidd = false;
        backend = "ltlsynt fallback (self-verification)";
        sub = run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
      }
      if (getenv("TLSFCOMPOSE_DEBUG"))
        fprintf(stderr, "tlsfcompose: cluster %u nodes=%u routed to %s\n", k,
                ast_node_count(root), backend);
      if (unreal) {
        fprintf(stderr, "tlsfcompose: cluster %u is UNREALIZABLE (%s)\n", k,
                backend);
        rc = 1;
      } else if (!sub) {
        char reason[192];
        const char *detail =
            use_oxidd ? "OxiDD returned no usable strategy"
                      : cluster_ltlsynt_reason(&route.shape, finite, reason,
                                               sizeof reason);
        fprintf(stderr,
                "tlsfcompose: synthesis backend failed for cluster %u (%s: "
                "%s)\n",
                k, backend, detail);
        rc = 1;
      } else if (!aig_merge(g, sub)) {
        fprintf(stderr, "tlsfcompose: AIGER merge failed for cluster %u\n", k);
        rc = 1;
      }
      aig_free(sub);
    }
    // Combinational controllers: ground their values, compile, drive outputs.
    for (uint32_t k = 0; k < comp->nelim && rc == 0; k++) {
      const Node *v =
          residual_apply_elims(spec->arena, comp->elim[k].value, comp, cov);
      uint32_t lit = aig_compile(g, v);
      if (lit == UINT32_MAX) {
        fprintf(stderr, "tlsfcompose: cannot encode controller for %s\n",
                ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output));
        rc = 1;
        break;
      }
      aig_set_output(
          g, ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output), lit);
    }
    if (rc == 0 && !csnf_emit_local_aiger(csnf, comp, g)) {
      fprintf(stderr, "tlsfcompose: cannot encode local template controller\n");
      rc = 1;
    }
    // Any unconstrained output: drive to false.
    for (uint32_t o = 0; o < A && rc == 0; o++)
      if ((ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT) &&
          aig_lookup(g, ap_table_name(&cov->aps, o)) == UINT32_MAX)
        aig_set_output(g, ap_table_name(&cov->aps, o), AIG_FALSE);

    if (rc == 0)
      aig_write_aag(out, g);
    aig_free(g);
    oxidd_session_free();
    free(seen);
    residual_plan_free(rplan);
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return rc;
  }

  fprintf(out, "c compose: controllers=%u clusters=%u\n", comp->nelim, K);

  // Combinational controllers (exact): o := value.
  FILE *ctlf = nullptr;
  if (out_dir) {
    char path[4096];
    snprintf(path, sizeof path, "%s/controllers.txt", out_dir);
    ctlf = fopen(path, "w");
    if (!ctlf) {
      fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
      rc = 1;
    }
  }
  for (uint32_t k = 0; k < comp->nelim && rc == 0; k++) {
    const char *oname =
        ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output);
    FILE *dst = ctlf ? ctlf : out;
    fprintf(dst, "ctl %s := ", oname);
    print_ltl(dst, comp->elim[k].value, fmt, /*full_parens=*/false, finite,
              /*lower_atoms=*/false);
  }
  if (ctlf)
    fclose(ctlf);

  // compose.sh driver (only with --output-dir).
  FILE *shf = nullptr;
  if (out_dir && rc == 0) {
    char path[4096];
    snprintf(path, sizeof path, "%s/compose.sh", out_dir);
    shf = fopen(path, "w");
    if (!shf) {
      fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
      rc = 1;
    } else {
      compose_sh_header(shf);
    }
  }

  for (uint32_t k = 0, ck = 0; k < K && rc == 0; k++) {
    // Output-free (input-only) guarantee clusters carry no controller, but they
    // are NOT trivially realizable -- emit them too so compose.sh's per-cluster
    // realizability check covers them (built with all assumptions, prune=false,
    // so coupling assumptions that mention other clusters' outputs survive).
    bool output_free = rplan->keys[k] == A;
    Node *root = residual_plan_build_cluster(spec, cov, rplan, rplan->keys[k],
                                             /*all=*/false,
                                             /*prune=*/!output_free, seen);
    if (!root) {
      rc = 1;
      break;
    }
    if (out_dir) {
      char path[4096];
      snprintf(path, sizeof path, "%s/cluster.%u.ltl", out_dir, ck);
      FILE *cf = fopen(path, "w");
      if (!cf) {
        fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
        rc = 1;
        break;
      }
      fprintf(cf, "c outs=");
      residual_print_signals(cf, cov, seen, AP_FLAG_OUTPUT);
      fprintf(cf, "\nc ins=");
      residual_print_signals(cf, cov, seen, AP_FLAG_INPUT);
      fprintf(cf, "\n");
      print_ltl(cf, root, fmt, false, finite, /*lower_atoms=*/false);
      fclose(cf);
      fprintf(shf, "run cluster.%u.ltl \"", ck);
      residual_print_signals(shf, cov, seen, AP_FLAG_INPUT);
      fprintf(shf, "\" \"");
      residual_print_signals(shf, cov, seen, AP_FLAG_OUTPUT);
      fprintf(shf, "\"\n");
      fprintf(out, "c cluster %u file=cluster.%u.ltl outs=", ck, ck);
      residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, " ins=");
      residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
    } else {
      fprintf(out, "c cluster %u outs=", ck);
      residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, " ins=");
      residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
      print_ltl(out, root, fmt, false, finite, /*lower_atoms=*/false);
    }
    ck++;
  }
  if (shf) {
    fprintf(shf, "[ \"$ok\" = 1 ] && echo \"SPEC REALIZABLE\" || echo \"SPEC "
                 "UNREALIZABLE\"\n");
    fclose(shf);
  }
  fprintf(out, "c realizable iff every cluster is realizable (controllers are "
               "exact)\n");

  free(seen);
  residual_plan_free(rplan);
  if (rc)
    fprintf(stderr, "tlsfcompose: failed (OOM or I/O)\n");
  if (output_file)
    fclose(out);
  csnf_composition_free(comp);
  csnf_free(csnf);
  spec_free(spec);
  return rc;
}
