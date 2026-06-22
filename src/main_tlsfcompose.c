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
#include "tlsf/liveness_class.h"
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

typedef enum {
  PREPROCESS_ALWAYS,
  PREPROCESS_PROFITABLE,
  PREPROCESS_OFF,
  PREPROCESS_DIAGNOSE,
} PreprocessPolicy;

typedef enum {
  FALLBACK_CLUSTERS,
  FALLBACK_MONOLITHIC,
  FALLBACK_AUTO,
} FallbackMode;

typedef struct {
  uint32_t n_oxidd_clusters;
  uint32_t n_exact_oxidd_clusters;
  uint32_t n_fallback_clusters;
  uint64_t total_nodes;
  uint64_t oxidd_nodes;
  uint64_t fallback_nodes;
  uint32_t max_outputs_any_cluster;
  uint32_t max_outputs_fallback;
  bool profitable_use_oxidd;
} RoutePolicyStats;

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
      "  --preprocess-policy MODE     OxiDD routing policy: always, "
      "profitable, off, diagnose (default profitable)\n"
      "  --fallback-mode MODE         fallback policy: clusters, monolithic, "
      "auto (default clusters)\n"
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

static bool parse_preprocess_policy(const char *s, PreprocessPolicy *out) {
  if (!strcmp(s, "always")) {
    *out = PREPROCESS_ALWAYS;
  } else if (!strcmp(s, "profitable")) {
    *out = PREPROCESS_PROFITABLE;
  } else if (!strcmp(s, "off")) {
    *out = PREPROCESS_OFF;
  } else if (!strcmp(s, "diagnose")) {
    *out = PREPROCESS_DIAGNOSE;
  } else {
    return false;
  }
  return true;
}

static bool parse_fallback_mode(const char *s, FallbackMode *out) {
  if (!strcmp(s, "clusters")) {
    *out = FALLBACK_CLUSTERS;
  } else if (!strcmp(s, "monolithic")) {
    *out = FALLBACK_MONOLITHIC;
  } else if (!strcmp(s, "auto")) {
    *out = FALLBACK_AUTO;
  } else {
    return false;
  }
  return true;
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
  case ROUTE_RESPONSE_MONITOR_GR1:
    return "response-monitor-gr1";
  case ROUTE_EVENTUAL_MONITOR_GR1:
    return "eventual-monitor-gr1";
  case ROUTE_UNTIL_MONITOR_GR1:
    return "until-monitor-gr1";
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
  if (route->reason_override) {
    snprintf(buf, buf_sz, "%s", route->reason_override);
    return buf;
  }
  switch (route->kind) {
  case ROUTE_OUTPUT_FREE_LTLSYNT:
    snprintf(buf, buf_sz, "output-free guarantee check");
    break;
  case ROUTE_DIRECT_SAFETY:
  case ROUTE_STRICT_SAFETY:
  case ROUTE_WR_SAFETY:
  case ROUTE_RESPONSE_MONITOR_GR1:
  case ROUTE_EVENTUAL_MONITOR_GR1:
  case ROUTE_UNTIL_MONITOR_GR1:
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

static uint32_t count_seen_aps(const ConstraintCover *cov, const bool *seen,
                               uint32_t flag) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < cov->aps.count; i++) {
    if (seen[i] && (ap_table_flags(&cov->aps, i) & flag))
      count++;
  }
  return count;
}

static size_t formula_bytes(const Node *root, LtlFormat fmt, bool finite) {
  char *buf = nullptr;
  size_t len = 0;
  FILE *ms = open_memstream(&buf, &len);
  if (!ms)
    return 0;
  print_ltl(ms, root, fmt, /*full_parens=*/false, finite,
            /*lower_atoms=*/false);
  fclose(ms);
  free(buf);
  return len;
}

static void output_free_route(TlsfSpec *spec, const Node *root,
                              ComposeRoute *out) {
  *out = (ComposeRoute){
      .kind = ROUTE_OUTPUT_FREE_LTLSYNT,
      .uses_oxidd = false,
      .exact = true,
      .label = "ltlsynt",
      .shape = cluster_shape(spec, root),
      .root = root,
  };
}

static void route_policy_stats_add(RoutePolicyStats *stats,
                                   const ComposeRoute *route, uint32_t nodes,
                                   uint32_t n_outputs) {
  stats->total_nodes += nodes;
  if (n_outputs > stats->max_outputs_any_cluster)
    stats->max_outputs_any_cluster = n_outputs;

  if (route->uses_oxidd) {
    stats->n_oxidd_clusters++;
    if (route->exact)
      stats->n_exact_oxidd_clusters++;
    stats->oxidd_nodes += nodes;
  } else {
    stats->n_fallback_clusters++;
    stats->fallback_nodes += nodes;
    if (n_outputs > stats->max_outputs_fallback)
      stats->max_outputs_fallback = n_outputs;
  }
}

static void route_policy_stats_finalize(RoutePolicyStats *stats) {
  if (stats->n_fallback_clusters == 0) {
    stats->profitable_use_oxidd = true;
  } else if (stats->max_outputs_fallback < stats->max_outputs_any_cluster) {
    stats->profitable_use_oxidd = true;
  } else {
    uint64_t denom = stats->total_nodes ? stats->total_nodes : 1;
    stats->profitable_use_oxidd = stats->oxidd_nodes * 5 >= denom;
  }
}

static void force_ltlsynt_policy_route(ComposeRoute *route, const char *label,
                                       const char *reason) {
  route->kind = ROUTE_LTLSYNT;
  route->uses_oxidd = false;
  route->exact = true;
  route->label = label;
  route->reason_override = reason;
}

static void apply_preprocess_policy(ComposeRoute *route, PreprocessPolicy policy,
                                    const RoutePolicyStats *stats) {
  if (!route->uses_oxidd)
    return;
  if (policy == PREPROCESS_OFF) {
    force_ltlsynt_policy_route(route, "ltlsynt fallback (policy off)",
                               "preprocess policy off");
  } else if (policy == PREPROCESS_PROFITABLE &&
             stats && !stats->profitable_use_oxidd) {
    force_ltlsynt_policy_route(
        route, "ltlsynt fallback (policy profitable)",
        "preprocess policy profitable skipped OxiDD");
  }
}

static bool preprocess_policy_skips_oxidd(PreprocessPolicy policy,
                                          const RoutePolicyStats *stats) {
  if (policy == PREPROCESS_OFF)
    return true;
  return policy == PREPROCESS_PROFITABLE && stats &&
         !stats->profitable_use_oxidd;
}

static uint32_t effective_exact_oxidd_clusters(
    PreprocessPolicy policy, const RoutePolicyStats *stats) {
  if (!stats)
    return 0;
  return preprocess_policy_skips_oxidd(policy, stats)
             ? 0
             : stats->n_exact_oxidd_clusters;
}

static uint32_t effective_fallback_clusters(PreprocessPolicy policy,
                                            const RoutePolicyStats *stats) {
  if (!stats)
    return 0;
  return stats->n_fallback_clusters +
         (preprocess_policy_skips_oxidd(policy, stats) ? stats->n_oxidd_clusters
                                                       : 0);
}

static uint32_t effective_max_outputs_fallback(PreprocessPolicy policy,
                                               const RoutePolicyStats *stats) {
  if (!stats)
    return 0;
  return preprocess_policy_skips_oxidd(policy, stats)
             ? stats->max_outputs_any_cluster
             : stats->max_outputs_fallback;
}

static bool fallback_mode_uses_monolithic(FallbackMode mode,
                                          PreprocessPolicy policy,
                                          const RoutePolicyStats *stats) {
  if (mode == FALLBACK_CLUSTERS)
    return false;
  if (mode == FALLBACK_MONOLITHIC)
    return true;
  if (!stats)
    return false;
  return effective_exact_oxidd_clusters(policy, stats) == 0 &&
         effective_fallback_clusters(policy, stats) > 1 &&
         effective_max_outputs_fallback(policy, stats) ==
             stats->max_outputs_any_cluster;
}

static bool compute_route_policy_stats(TlsfSpec *spec, ConstraintCover *cov,
                                       const ResidualPlan *rplan, bool finite,
                                       uint32_t bound_k, bool *seen,
                                       RoutePolicyStats *stats) {
  *stats = (RoutePolicyStats){0};
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
    if (output_free)
      output_free_route(spec, root, &route);
    else
      (void)compose_route_select(spec, root, finite, bound_k, &route);

    route_policy_stats_add(stats, &route, ast_node_count(root),
                           count_seen_aps(cov, seen, AP_FLAG_OUTPUT));
  }
  route_policy_stats_finalize(stats);
  return true;
}

static void print_policy_diagnosis(const RoutePolicyStats *stats) {
  fprintf(stderr,
          "tlsfcompose: preprocess-policy diagnose: profitable would %s OxiDD "
          "clusters (n_oxidd_clusters=%u n_exact_oxidd_clusters=%u "
          "n_fallback_clusters=%u oxidd_nodes=%llu fallback_nodes=%llu "
          "total_nodes=%llu max_outputs_fallback=%u "
          "max_outputs_any_cluster=%u)\n",
          stats->profitable_use_oxidd ? "keep" : "skip",
          stats->n_oxidd_clusters, stats->n_exact_oxidd_clusters,
          stats->n_fallback_clusters, (unsigned long long)stats->oxidd_nodes,
          (unsigned long long)stats->fallback_nodes,
          (unsigned long long)stats->total_nodes,
          stats->max_outputs_fallback, stats->max_outputs_any_cluster);
}

static bool emit_route_stats(FILE *out, TlsfSpec *spec, ConstraintCover *cov,
                             const ResidualPlan *rplan, bool finite,
                             uint32_t bound_k, bool *seen, LtlFormat fmt,
                             const char *input_file, PreprocessPolicy policy,
                             const RoutePolicyStats *policy_stats) {
  (void)input_file;
  fprintf(out,
          "spec\tcluster_id\tn_inputs\tn_outputs\tformula_nodes\t"
          "formula_bytes\tgr_level\thas_liveness\thas_weak_until\t"
          "has_release\tliveness_class\tn_response\tn_recurrence\t"
          "n_eventual\tn_until\thas_nested_temporal\troute\tbackend\texact\t"
          "uses_oxidd\treason\n");
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
    if (output_free)
      output_free_route(spec, root, &route);
    else {
      (void)compose_route_select(spec, root, finite, bound_k, &route);
      apply_preprocess_policy(&route, policy, policy_stats);
    }
    char reason[192];
    LivenessSummary live = liveness_classify(root);
    fprintf(out,
            "\t%u\t%u\t%u\t%u\t%zu\t%d\t%d\t%d\t%d\t%s\t%u\t%u\t%u\t%u\t%d\t"
            "%s\t%s\t%d\t%d\t%s\n",
            k, count_seen_aps(cov, seen, AP_FLAG_INPUT),
            count_seen_aps(cov, seen, AP_FLAG_OUTPUT), ast_node_count(root),
            formula_bytes(root, fmt, finite), route.shape.gr_level,
            route.shape.has_liveness ? 1 : 0,
            route.shape.has_weak_until ? 1 : 0,
            route.shape.has_release ? 1 : 0,
            liveness_class_name(live.kind), live.n_response,
            live.n_recurrence, live.n_eventual, live.n_until,
            live.has_nested_temporal ? 1 : 0, route_kind_name(route.kind),
            route.label ? route.label : "ltlsynt", route.exact ? 1 : 0,
            route.uses_oxidd ? 1 : 0,
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
  PreprocessPolicy preprocess_policy = PREPROCESS_PROFITABLE;
  FallbackMode fallback_mode = FALLBACK_CLUSTERS;
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
    } else if (strcmp(a, "--preprocess-policy") == 0) {
      const char *v = NEED_ARG();
      if (!parse_preprocess_policy(v, &preprocess_policy)) {
        fprintf(stderr,
                "tlsfcompose: unknown --preprocess-policy '%s' "
                "(expected always, profitable, off, diagnose)\n",
                v);
        return 1;
      }
    } else if (strcmp(a, "--fallback-mode") == 0) {
      const char *v = NEED_ARG();
      if (!parse_fallback_mode(v, &fallback_mode)) {
        fprintf(stderr,
                "tlsfcompose: unknown --fallback-mode '%s' "
                "(expected clusters, monolithic, auto)\n",
                v);
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
    RoutePolicyStats policy_stats;
    if (!compute_route_policy_stats(spec, cov, rplan, finite, bound_k, seen,
                                    &policy_stats)) {
      rc = 1;
    } else {
      if (preprocess_policy == PREPROCESS_DIAGNOSE)
        print_policy_diagnosis(&policy_stats);
      rc = emit_route_stats(out, spec, cov, rplan, finite, bound_k, seen, fmt,
                            input_file, preprocess_policy, &policy_stats)
               ? 0
               : 1;
    }
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
    RoutePolicyStats policy_stats = {0};
    const RoutePolicyStats *policy_stats_ptr = nullptr;
    bool need_policy_stats = preprocess_policy == PREPROCESS_PROFITABLE ||
                             preprocess_policy == PREPROCESS_DIAGNOSE ||
                             fallback_mode == FALLBACK_AUTO;
    if (need_policy_stats) {
      if (!compute_route_policy_stats(spec, cov, rplan, finite, bound_k, seen,
                                      &policy_stats)) {
        free(seen);
        residual_plan_free(rplan);
        if (output_file)
          fclose(out);
        csnf_composition_free(comp);
        csnf_free(csnf);
        spec_free(spec);
        return 1;
      }
      policy_stats_ptr = &policy_stats;
      if (preprocess_policy == PREPROCESS_DIAGNOSE)
        print_policy_diagnosis(&policy_stats);
    }
    bool use_monolithic_fallback =
        K > 0 && fallback_mode_uses_monolithic(fallback_mode, preprocess_policy,
                                               policy_stats_ptr);
    bool oxidd_session_started = false;
    // Persistent BDD manager: one allocation shared across all clusters,
    // amortising oxidd_bdd_manager_new overhead on multi-cluster specs.
    // Variables accumulate with per-cluster base offsets; GC reclaims dead
    // nodes between clusters.  Cap at 1<<21 (2M nodes) to keep peak RSS low
    // while still covering the measured self-contained OxiDD corpus.
    if (!use_monolithic_fallback) {
      oxidd_session_init(1u << 21, 1u << 21);
      oxidd_session_started = true;
    }

    Aig *g = aig_new();
    for (uint32_t o = 0; o < A; o++) // all declared and residual env inputs
      if (residual_signal_matches(cov, o, AP_FLAG_INPUT))
        (void)aig_input(g, ap_table_name(&cov->aps, o));

    if (use_monolithic_fallback) {
      Node *root =
          residual_plan_build_cluster(spec, cov, rplan, 0, /*all=*/true,
                                      /*prune=*/true, seen);
      if (!root) {
        rc = 1;
      } else {
        int unreal = 0;
        Aig *sub =
            run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
        if (getenv("TLSFCOMPOSE_DEBUG"))
          fprintf(stderr, "tlsfcompose: residual routed to monolithic %s\n",
                  prog);
        if (unreal) {
          fprintf(stderr,
                  "tlsfcompose: monolithic fallback is UNREALIZABLE "
                  "(ltlsynt)\n");
          rc = 1;
        } else if (!sub) {
          if (fallback_mode == FALLBACK_AUTO) {
            fprintf(stderr,
                    "tlsfcompose: monolithic fallback failed (ltlsynt); "
                    "retrying per-cluster fallback\n");
            use_monolithic_fallback = false;
            oxidd_session_init(1u << 21, 1u << 21);
            oxidd_session_started = true;
          } else {
            fprintf(stderr,
                    "tlsfcompose: monolithic fallback failed (ltlsynt)\n");
            rc = 1;
          }
        } else if (!aig_merge(g, sub)) {
          fprintf(stderr, "tlsfcompose: AIGER merge failed for monolithic "
                          "fallback\n");
          rc = 1;
        }
        aig_free(sub);
      }
    }

    // Clusters first (so a decoder reading a synthesized output resolves).
    for (uint32_t k = 0; !use_monolithic_fallback && k < K && rc == 0; k++) {
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
      apply_preprocess_policy(&route, preprocess_policy, policy_stats_ptr);
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
    if (oxidd_session_started)
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
