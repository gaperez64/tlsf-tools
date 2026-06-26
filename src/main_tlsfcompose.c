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

// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/aiger.h"
#include "tlsf/ast.h"
#include "tlsf/build_info.h"
#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/decompose.h"
#include "tlsf/expand.h"
#include "tlsf/gr.h"
#include "tlsf/liveness_class.h"
#include "tlsf/precheck_unreal.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/recognize.h"
#include "tlsf/residual.h"
#include "tlsf/residual_plan.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include "compose_internal.h"
#include "compose_route.h"
#include "decompose_internal.h"

#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  PREPROCESS_ALWAYS,
  PREPROCESS_PROFITABLE,
  PREPROCESS_OFF,
  PREPROCESS_DIAGNOSE,
} PreprocessPolicy;

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
      "  --merge FILE.aag...          merge AIGER strategies and write one "
      ".aag\n"
      "  --realizability              fast verdict oracle: print REALIZABLE / "
      "UNREALIZABLE / UNKNOWN via the boolean-fragment pre-checks (exit 0/1/2; "
      "no plan or controller).  Pair with --split.\n"
      "  --lowercase                  lowercase emitted cluster formulas and "
      "interfaces\n"
      "  --pre-normalize SCHEDULE     pre-expansion normalization (opt-in)\n"
      "  --match-normalize SCHEDULE   recognition normalization, e.g. "
      "match-safe:1 (opt-in)\n"
      "  --experimental-bounded N     enable bounded-liveness heuristic with "
      "step bound N in route diagnostics\n"
      "  --preprocess-policy MODE     route diagnostic policy: always, "
      "profitable, off, diagnose (default profitable)\n"
      "  --route-stats                print residual-cluster route diagnostics "
      "and exit\n"
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
  case ROUTE_RESPONSE_MONITOR_GR1:
  case ROUTE_EVENTUAL_MONITOR_GR1:
  case ROUTE_UNTIL_MONITOR_GR1:
  case ROUTE_GR1:
    snprintf(buf, buf_sz, "selected exact fast path");
    break;
  case ROUTE_WR_SAFETY:
    snprintf(buf, buf_sz,
             "selected over-approx fast path (W/R safety; verified)");
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

static void apply_preprocess_policy(ComposeRoute *route,
                                    PreprocessPolicy policy,
                                    const RoutePolicyStats *stats) {
  if (!route->uses_oxidd)
    return;
  if (policy == PREPROCESS_OFF) {
    force_ltlsynt_policy_route(route, "ltlsynt fallback (policy off)",
                               "preprocess policy off");
  } else if (policy == PREPROCESS_PROFITABLE && stats &&
             !stats->profitable_use_oxidd) {
    force_ltlsynt_policy_route(route, "ltlsynt fallback (policy profitable)",
                               "preprocess policy profitable skipped OxiDD");
  }
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
          (unsigned long long)stats->total_nodes, stats->max_outputs_fallback,
          stats->max_outputs_any_cluster);
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
            route.shape.has_weak_until ? 1 : 0, route.shape.has_release ? 1 : 0,
            liveness_class_name(live.kind), live.n_response, live.n_recurrence,
            live.n_eventual, live.n_until, live.has_nested_temporal ? 1 : 0,
            route_kind_name(route.kind), route.label ? route.label : "ltlsynt",
            route.exact ? 1 : 0, route.uses_oxidd ? 1 : 0,
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
          "# ltlsynt unless cluster.N.aag was already solved in process.\n"
          "# controllers.txt holds the combinational part (already solved,\n"
          "# exact).  The spec is realizable iff every cluster is.\n"
          "dir=$(CDPATH= cd -- \"$(dirname -- \"$0\")\" && pwd)\n"
          "ok=1\n"
          "run() {\n"
          "  base=${1%%.ltl}\n"
          "  if [ -f \"$dir/$base.aag\" ]; then\n"
          "    echo \"$base.aag: SOLVED\"\n"
          "    return\n"
          "  fi\n"
          // Pass the formula via a file (-F), not --formula= on the command
          // line: large clusters exceed the shell/exec argument limit (E2BIG).
          "  f=$(mktemp)\n"
          "  grep -v '^c ' \"$dir/$1\" > \"$f\"\n"
          "  if ltlsynt --ins=\"$2\" --outs=\"$3\" -F \"$f\" "
          "--realizability >/dev/null 2>&1; then\n"
          "    echo \"$1: REALIZABLE\"\n"
          "  else\n"
          "    echo \"$1: UNREALIZABLE\"; ok=0\n"
          "  fi\n"
          "  rm -f \"$f\"\n"
          "}\n");
}

static void fputs_maybe_lower(FILE *out, const char *s, bool lower) {
  if (!lower) {
    fputs(s, out);
    return;
  }
  for (const char *p = s; *p; p++)
    fputc(tolower((unsigned char)*p), out);
}

static void print_string_list(FILE *out, char *const *items, uint32_t count) {
  for (uint32_t i = 0; i < count; i++)
    fprintf(out, "%s%s", i ? "," : "", items[i]);
}

static TlsfDecomposeFormat decompose_format_from_ltl(LtlFormat fmt) {
  return fmt == LTL_FMT_LTL ? TLSF_DECOMPOSE_FORMAT_LTL
                            : TLSF_DECOMPOSE_FORMAT_LTLXBA;
}

static int merge_aiger_files(char *const *files, uint32_t count,
                             const char *output_file) {
  if (count == 0) {
    fprintf(stderr, "tlsfcompose: --merge requires at least one .aag file\n");
    return 1;
  }
  Aig *merged = nullptr;
  int rc = 0;
  for (uint32_t i = 0; i < count && rc == 0; i++) {
    FILE *fp = fopen(files[i], "r");
    if (!fp) {
      fprintf(stderr, "tlsfcompose: cannot read %s\n", files[i]);
      rc = 1;
      break;
    }
    Aig *sub = aig_read_aag(fp);
    fclose(fp);
    if (!sub) {
      fprintf(stderr, "tlsfcompose: invalid AIGER file %s\n", files[i]);
      rc = 1;
      break;
    }
    if (!merged) {
      merged = sub;
    } else if (!aig_merge(merged, sub)) {
      fprintf(stderr, "tlsfcompose: AIGER merge failed for %s\n", files[i]);
      aig_free(sub);
      rc = 1;
    } else {
      aig_free(sub);
    }
  }
  if (rc == 0) {
    FILE *out = cli_open_output(output_file, "tlsfcompose");
    if (!out) {
      rc = 1;
    } else {
      aig_write_aag(out, merged);
      if (output_file)
        fclose(out);
    }
  }
  aig_free(merged);
  return rc;
}

static char *strdup_lowercase(const char *s) {
  size_t n = strlen(s);
  char *out = malloc(n + 1);
  if (!out)
    return nullptr;
  for (size_t i = 0; i < n; i++)
    out[i] = (char)tolower((unsigned char)s[i]);
  out[n] = '\0';
  return out;
}

static bool lowercase_aig_signals(Aig *g, ConstraintCover *cov) {
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    const char *orig = ap_table_name(&cov->aps, a);
    char *lower = strdup_lowercase(orig);
    if (!lower)
      return false;
    if (strcmp(orig, lower) != 0)
      aig_rename_signal(g, orig, lower);
    free(lower);
  }
  return true;
}

static bool emit_certified_aiger(FILE *out, TlsfSpec *spec,
                                 ConstraintCover *cov, const Csnf *csnf,
                                 const CsnfComposition *comp, bool lowercase) {
  Aig *g = aig_new();
  if (!g)
    return false;
  uint32_t A = cov->aps.count;
  for (uint32_t o = 0; o < A; o++)
    if (residual_signal_matches(cov, o, AP_FLAG_INPUT))
      (void)aig_input(g, ap_table_name(&cov->aps, o));

  bool ok = true;
  for (uint32_t k = 0; k < comp->nelim && ok; k++) {
    const Node *v =
        residual_apply_elims(spec->arena, comp->elim[k].value, comp, cov);
    uint32_t lit = aig_compile(g, v);
    if (lit == UINT32_MAX) {
      ok = false;
      break;
    }
    aig_set_output(
        g, ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output), lit);
  }
  if (ok)
    ok = csnf_emit_local_aiger(csnf, comp, g);
  for (uint32_t o = 0; o < A && ok; o++)
    if ((ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT) &&
        !aig_has_output(g, ap_table_name(&cov->aps, o)))
      aig_set_output(g, ap_table_name(&cov->aps, o), AIG_FALSE);
  if (ok && lowercase)
    ok = lowercase_aig_signals(g, cov);
  if (ok)
    aig_write_aag(out, g);
  aig_free(g);
  return ok;
}

static bool emit_oxidd_cluster_aiger(
    const char *out_dir, uint32_t k, TlsfSpec *spec, ConstraintCover *cov,
    const ResidualPlan *rplan, bool finite, uint32_t bound_k,
    PreprocessPolicy policy, const RoutePolicyStats *policy_stats, bool *seen,
    bool lowercase, bool *solved, const char **backend_label) {
  *solved = false;
  if (backend_label)
    *backend_label = nullptr;
  if (!out_dir || rplan->keys[k] == cov->aps.count)
    return true;

  Node *root = residual_plan_build_cluster(spec, cov, rplan, rplan->keys[k],
                                           /*all=*/false, /*prune=*/true,
                                           seen);
  if (!root) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    return false;
  }

  ComposeRoute route;
  (void)compose_route_select(spec, root, finite, bound_k, &route);
  apply_preprocess_policy(&route, policy, policy_stats);
  if (!route.uses_oxidd)
    return true;

  int unreal = 0;
  bool trusted_unreal = false;
  const char *backend = nullptr;
  Aig *sub = compose_route_try_oxidd(&route, cov, seen, &unreal,
                                     &trusted_unreal, &backend);
  if (!sub && trusted_unreal) {
    fprintf(stderr,
            "tlsfcompose: cluster %u is UNREALIZABLE (%s; trusted "
            "one-sided OxiDD verdict)\n",
            k, backend ? backend : "OxiDD");
    return false;
  }
  if (!sub)
    return true;
  if (lowercase && !lowercase_aig_signals(sub, cov)) {
    aig_free(sub);
    return false;
  }

  char path[4096];
  snprintf(path, sizeof path, "%s/cluster.%u.aag", out_dir, k);
  FILE *af = fopen(path, "w");
  if (!af) {
    fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
    aig_free(sub);
    return false;
  }
  aig_write_aag(af, sub);
  fclose(af);
  aig_free(sub);
  *solved = true;
  if (backend_label)
    *backend_label = backend ? backend : "OxiDD";
  (void)unreal;
  return true;
}

int main(int argc, char *argv[]) {
  bool split = false, route_stats = false;
  bool realizability = false;
  bool lowercase = false, merge_mode = false;
  LtlFormat fmt = LTL_FMT_LTLXBA;
  const char *input_file = nullptr, *output_file = nullptr, *out_dir = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  const char *pre_norm = nullptr, *match_norm = nullptr;
  unsigned long bound_opt = 0; // 0 = bounded-liveness heuristic disabled
  PreprocessPolicy preprocess_policy = PREPROCESS_PROFITABLE;
  ParamOverride overrides[64];
  size_t n_overrides = 0;
  char **merge_files = calloc((size_t)argc ? (size_t)argc : 1, sizeof *merge_files);
  uint32_t n_merge_files = 0;
  if (!merge_files) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    return 1;
  }

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfcompose: %s requires an argument\n",    \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--merge") == 0) {
      merge_mode = true;
    } else if (strcmp(a, "--realizability") == 0) {
      realizability = true;
    } else if (strcmp(a, "--lowercase") == 0) {
      lowercase = true;
    } else if (strcmp(a, "--pre-normalize") == 0) {
      pre_norm = NEED_ARG();
    } else if (strcmp(a, "--match-normalize") == 0) {
      match_norm = NEED_ARG();
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
      free(merge_files);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      free(merge_files);
      return 0;
    } else if (a[0] != '-') {
      if (merge_mode) {
        merge_files[n_merge_files++] = argv[i];
        continue;
      }
      if (input_file) {
        fprintf(stderr, "tlsfcompose: multiple input files not supported\n");
        free(merge_files);
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfcompose: unknown option '%s'\n", a);
      usage(argv[0]);
      free(merge_files);
      return 1;
    }
  }
#undef NEED_ARG

  if (merge_mode) {
    int mrc = merge_aiger_files(merge_files, n_merge_files, output_file);
    free(merge_files);
    return mrc;
  }
  free(merge_files);

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
  bool norm_finite = semantics_is_finite(spec->info.semantics);
  if (pre_norm) {
    TlsfNormSchedule sch;
    TlsfNormOptions o;
    tlsf_norm_options_default(&o, TLSF_NORM_PHASE_PRE_EXPAND);
    o.finite_word = norm_finite;
    TlsfNormRejectReason rr;
    if (!tlsf_norm_parse_schedule(spec->arena, pre_norm, "tlsfcompose", &sch)) {
      spec_free(spec);
      return 1;
    }
    o.schedule = sch;
    if (!tlsf_norm_schedule_check(&sch, &o, "tlsfcompose", &rr)) {
      spec_free(spec);
      return 1;
    }
    tlsf_prenorm_spec(spec, &o, nullptr);
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

  // Verdict-trust class TRUST_OVER (see precheck_unreal.h): a sound,
  // OVER-approximation UNREALIZABLE pre-check over the boolean fragment.  It
  // refutes a weakening of the spec (drops temporal guarantees, keeps every
  // assumption, bails on any temporal assumption), so its UNREALIZABLE is
  // trustworthy and it never claims REALIZABLE.  Fires before the heavy
  // recognize/certify/residual stages, matching ltlsynt's whole-formula fast
  // path for trivially unrealizable inputs.
  if (precheck_trivially_unreal(cov)) {
    if (route_stats)
      fprintf(stderr, "route-stats: unreal_precheck=1 "
                      "(boolean fragment; over-approx, trusted UNREAL)\n");
    fprintf(stderr, "tlsfcompose: spec is UNREALIZABLE "
                    "(boolean-fragment pre-check; over-approx, trusted)\n");
    spec_free(spec);
    return 1;
  }

  // --realizability: a fast verdict oracle.  The always-on UNREAL pre-check
  // above already settled UNREALIZABLE; here the dual TRUST_UNDER REALIZABLE
  // pre-check (a memoryless Mealy Skolem controller of the conjoined boolean
  // guarantees; see precheck_unreal.h) settles REALIZABLE, else UNKNOWN.  It is
  // gated behind the flag because, unlike UNREAL, it yields only a verdict —
  // not the plan or AIGER controller the default modes emit — so
  // short-circuiting those would drop their deliverable.
  if (realizability) {
    if (precheck_trivially_real(cov)) {
      if (route_stats)
        fprintf(stderr, "route-stats: real_precheck=1 "
                        "(boolean fragment; under-approx, trusted REAL)\n");
      fprintf(stderr, "tlsfcompose: spec is REALIZABLE "
                      "(boolean-fragment pre-check; under-approx, trusted)\n");
      spec_free(spec);
      return 0;
    }
    fprintf(
        stderr,
        "tlsfcompose: realizability UNKNOWN (fast pre-checks inconclusive)\n");
    spec_free(spec);
    return 2;
  }

  // Match normalization (opt-in) rewrites match_formula only; residual/routing
  // and the self-verification gate still use the original formula, so a wrong
  // normalization stays sound (it can only fail to recognize, never mis-solve).
  if (!cover_match_normalize(cov, match_norm, norm_finite, "tlsfcompose",
                             nullptr)) {
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

  ResidualPlanOptions ropts = {.skip_local_aiger = out_dir != nullptr,
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

  uint32_t bound_k = (uint32_t)bound_opt;
  RoutePolicyStats policy_stats = {0};
  const RoutePolicyStats *policy_stats_ptr = nullptr;
  bool need_policy_stats =
      route_stats ||
      (out_dir && (preprocess_policy == PREPROCESS_PROFITABLE ||
                   preprocess_policy == PREPROCESS_DIAGNOSE));
  if (need_policy_stats) {
    if (!compute_route_policy_stats(spec, cov, rplan, finite, bound_k, seen,
                                    &policy_stats))
      rc = 1;
    else
      policy_stats_ptr = &policy_stats;
  }

  if (preprocess_policy == PREPROCESS_DIAGNOSE && policy_stats_ptr)
    print_policy_diagnosis(policy_stats_ptr);

  if (route_stats) {
    if (rc == 0)
      rc = emit_route_stats(out, spec, cov, rplan, finite, bound_k, seen, fmt,
                            input_file, preprocess_policy, policy_stats_ptr)
               ? 0
               : 1;
    free(seen);
    residual_plan_free(rplan);
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return rc;
  }

  TlsfDecomposeOptions dopts = {
      .split = split,
      .lowercase = lowercase,
      .format = decompose_format_from_ltl(fmt),
  };
  TlsfDecomposeResult *dres =
      tlsf_decompose_result_from_plan(spec, cov, csnf, comp, rplan, &dopts);
  if (!dres)
    rc = 1;

  if (rc == 0)
    fprintf(out, "c compose: controllers=%u clusters=%u\n", comp->nelim,
            dres->n_clusters);

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
    fputs("ctl ", dst);
    fputs_maybe_lower(dst, oname, lowercase);
    fputs(" := ", dst);
    print_ltl(dst, comp->elim[k].value, fmt, /*full_parens=*/false, finite,
              /*lower_atoms=*/lowercase);
  }
  if (ctlf)
    fclose(ctlf);

  if (out_dir && rc == 0) {
    char path[4096];
    snprintf(path, sizeof path, "%s/controllers.aag", out_dir);
    FILE *caf = fopen(path, "w");
    if (!caf) {
      fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
      rc = 1;
    } else {
      if (!emit_certified_aiger(caf, spec, cov, csnf, comp, lowercase)) {
        fprintf(stderr, "tlsfcompose: cannot encode %s\n", path);
        rc = 1;
      }
      fclose(caf);
    }
  }

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

  bool oxidd_session_started = false;
  if (out_dir && rc == 0 && preprocess_policy != PREPROCESS_OFF) {
    oxidd_session_init(1u << 21, 1u << 21);
    oxidd_session_started = true;
  }

  for (uint32_t k = 0; dres && k < dres->n_clusters && rc == 0; k++) {
    TlsfDecomposeCluster *cluster = &dres->clusters[k];
    if (out_dir) {
      char path[4096];
      snprintf(path, sizeof path, "%s/cluster.%u.ltl", out_dir, k);
      FILE *cf = fopen(path, "w");
      if (!cf) {
        fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
        rc = 1;
        break;
      }
      fprintf(cf, "c outs=");
      print_string_list(cf, cluster->outputs, cluster->n_outputs);
      fprintf(cf, "\nc ins=");
      print_string_list(cf, cluster->inputs, cluster->n_inputs);
      fprintf(cf, "\n%s\n", cluster->ltl);
      fclose(cf);
      bool oxidd_solved = false;
      const char *oxidd_backend = nullptr;
      if (!emit_oxidd_cluster_aiger(out_dir, k, spec, cov, rplan, finite,
                                    bound_k, preprocess_policy,
                                    policy_stats_ptr, seen, lowercase,
                                    &oxidd_solved, &oxidd_backend)) {
        rc = 1;
        break;
      }
      fprintf(shf, "run cluster.%u.ltl \"", k);
      print_string_list(shf, cluster->inputs, cluster->n_inputs);
      fprintf(shf, "\" \"");
      print_string_list(shf, cluster->outputs, cluster->n_outputs);
      fprintf(shf, "\"\n");
      fprintf(out, "c cluster %u file=cluster.%u.ltl outs=", k, k);
      print_string_list(out, cluster->outputs, cluster->n_outputs);
      fprintf(out, " ins=");
      print_string_list(out, cluster->inputs, cluster->n_inputs);
      if (oxidd_solved)
        fprintf(out, " aiger=cluster.%u.aag backend=%s", k,
                oxidd_backend ? oxidd_backend : "OxiDD");
      fprintf(out, "\n");
    } else {
      fprintf(out, "c cluster %u outs=", k);
      print_string_list(out, cluster->outputs, cluster->n_outputs);
      fprintf(out, " ins=");
      print_string_list(out, cluster->inputs, cluster->n_inputs);
      fprintf(out, "\n%s\n", cluster->ltl);
    }
  }
  if (shf) {
    fprintf(shf, "[ \"$ok\" = 1 ] && echo \"SPEC REALIZABLE\" || echo \"SPEC "
                 "UNREALIZABLE\"\n");
    fclose(shf);
  }
  if (rc == 0)
    fprintf(out,
            "c realizable iff every cluster is realizable (controllers are "
            "trusted)\n");

  if (oxidd_session_started)
    oxidd_session_free();
  tlsf_decompose_result_free(dres);
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
