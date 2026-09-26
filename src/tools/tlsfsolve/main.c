/// tlsfsolve — in-process AIGER game solver (OxiDD BDD backend).
///
/// Reads an AIGER game (aag format, stdin or FILE) and emits the winning
/// strategy as an aag on stdout, exits 1 with "UNREALIZABLE" on stderr if the
/// controller player loses, or exits 2 if OxiDD/profile resolution fails.
/// Profile resolution determines whether the objective is legacy ordinary
/// output 0, typed AIGER 1.9 bad properties, or the local GR(1) dialect.
///
/// Usage:
///   tlsfsolve [--certificate FILE [--certificate-json FILE]]
///             [--policy FILE [--policy-json FILE]] [GAME]
///   tlsfsolve --help

#include "tlsf/aiger.h"
#include "build_info.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"
#include "oxidd_common.h"

#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  PROFILE_AUTO = 0,
  PROFILE_LEGACY_SAFETY,
  PROFILE_GR1,
  PROFILE_MULTI_SAFETY,
} GameProfile;

static const char *profile_name(GameProfile p) {
  switch (p) {
  case PROFILE_AUTO:
    return "auto";
  case PROFILE_LEGACY_SAFETY:
    return "legacy-safety";
  case PROFILE_GR1:
    return "gr1";
  case PROFILE_MULTI_SAFETY:
    return "multi-safety";
  }
  return "unknown";
}

static bool parse_profile(const char *s, GameProfile *out) {
  if (!strcmp(s, "auto"))
    *out = PROFILE_AUTO;
  else if (!strcmp(s, "legacy-safety"))
    *out = PROFILE_LEGACY_SAFETY;
  else if (!strcmp(s, "gr1"))
    *out = PROFILE_GR1;
  else if (!strcmp(s, "multi-safety"))
    *out = PROFILE_MULTI_SAFETY;
  else
    return false;
  return true;
}

static bool parse_size_value(const char *s, size_t *out) {
  if (!s || *s == '-' || *s == '\0')
    return false;
  errno = 0;
  char *end = nullptr;
  unsigned long long v = strtoull(s, &end, 10);
  if (errno || end == s || *end != '\0' || v == 0 || v > SIZE_MAX)
    return false;
  *out = (size_t)v;
  return true;
}

#ifndef NDEBUG
static bool parse_u32_value(const char *s, uint32_t *out) {
  if (!s || *s == '-' || *s == '\0')
    return false;
  errno = 0;
  char *end = nullptr;
  unsigned long long value = strtoull(s, &end, 10);
  if (errno || end == s || *end != '\0' || value > UINT32_MAX)
    return false;
  *out = (uint32_t)value;
  return true;
}
#endif

static bool parse_var_order(const char *s, OxiddVarOrder *out) {
  if (!strcmp(s, "input-first"))
    *out = OXIDD_VAR_ORDER_INPUT_FIRST;
  else if (!strcmp(s, "state-first"))
    *out = OXIDD_VAR_ORDER_STATE_FIRST;
  else if (!strcmp(s, "fanin-dfs"))
    *out = OXIDD_VAR_ORDER_FANIN_DFS;
  else
    return false;
  return true;
}

static const char *option_value(int *i, int argc, char **argv, const char *arg,
                                const char *name) {
  size_t n = strlen(name);
  if (strncmp(arg, name, n) == 0 && arg[n] == '=')
    return arg + n + 1;
  if (strcmp(arg, name) == 0 && *i + 1 < argc)
    return argv[++*i];
  return nullptr;
}

static bool has_controllable_input(const Aig *game) {
  for (uint32_t i = 0; i < aig_num_inputs(game); i++) {
    if (is_controllable(aig_input_name(game, i, nullptr)))
      return true;
  }
  return false;
}

static bool justice_records_are_singleton(const Aig *game) {
  for (uint32_t j = 0; j < aig_num_justice(game); j++) {
    uint32_t n = 0;
    aig_justice_at(game, j, nullptr, &n);
    if (n != 1)
      return false;
  }
  return true;
}

static bool validate_supported_resets(const Aig *game, const char *prog) {
  for (uint32_t j = 0; j < aig_num_latches(game); j++) {
    uint32_t cur, reset;
    aig_latch_at(game, j, &cur, nullptr, &reset);
    if (reset == 0 || reset == 1)
      continue;
    if (reset == cur) {
      fprintf(stderr,
              "%s: unsupported uninitialized latch reset at latch %u "
              "(literal %u)\n",
              prog, j, reset);
    } else {
      fprintf(stderr,
              "%s: unsupported nonconstant latch reset at latch %u "
              "(literal %u)\n",
              prog, j, reset);
    }
    return false;
  }
  return true;
}

static void print_counts(FILE *out, const Aig *game) {
  fprintf(out, "I=%u,L=%u,O=%u,A=%u,B=%u,C=%u,J=%u,F=%u", aig_num_inputs(game),
          aig_num_latches(game), aig_num_outputs(game), aig_num_ands(game),
          aig_num_bad(game), aig_num_constraints(game), aig_num_justice(game),
          aig_num_fairness(game));
}

static bool validate_explicit_profile(const Aig *game, GameProfile p,
                                      const char *prog) {
  uint32_t O = aig_num_outputs(game), B = aig_num_bad(game);
  uint32_t C = aig_num_constraints(game), J = aig_num_justice(game);
  uint32_t F = aig_num_fairness(game);
  bool ok = false;
  switch (p) {
  case PROFILE_LEGACY_SAFETY:
    ok = O == 1 && B == 0 && C == 0 && J == 0 && F == 0;
    break;
  case PROFILE_GR1:
    ok = C == 0 && J > 0 && justice_records_are_singleton(game);
    break;
  case PROFILE_MULTI_SAFETY:
    ok = B > 0 && C == 0 && J == 0 && F == 0;
    break;
  case PROFILE_AUTO:
    ok = false;
    break;
  }
  if (!ok) {
    fprintf(stderr, "%s: --game-profile=%s is incompatible with raw counts ",
            prog, profile_name(p));
    print_counts(stderr, game);
    if (p == PROFILE_GR1 && J > 0 && !justice_records_are_singleton(game))
      fprintf(stderr, " (non-singleton justice records are preserved but not "
                      "supported by this GR(1) solver)");
    fputc('\n', stderr);
  }
  return ok;
}

static bool resolve_profile(const Aig *game, GameProfile requested,
                            GameProfile *resolved, const char *prog) {
  if (requested != PROFILE_AUTO) {
    if (!validate_explicit_profile(game, requested, prog))
      return false;
    *resolved = requested;
    return true;
  }

  uint32_t O = aig_num_outputs(game), B = aig_num_bad(game);
  uint32_t C = aig_num_constraints(game), J = aig_num_justice(game);
  uint32_t F = aig_num_fairness(game);
  if (O == 1 && B == 0 && C == 0 && J == 0 && F == 0) {
    *resolved = PROFILE_LEGACY_SAFETY;
    return true;
  }
  if (C == 0 && J > 0 && has_controllable_input(game) &&
      justice_records_are_singleton(game)) {
    *resolved = PROFILE_GR1;
    return true;
  }

  fprintf(stderr, "%s: cannot infer synthesis game profile from raw counts ",
          prog);
  print_counts(stderr, game);
  if (C > 0) {
    fprintf(stderr, "; invariant constraints are parsed but unsupported as "
                    "synthesis assumptions");
  } else if (B > 0) {
    fprintf(stderr, "; bad state properties require explicit "
                    "--game-profile=multi-safety");
  } else if (J > 0 || F > 0) {
    fprintf(stderr, "; AIGER 1.9 liveness/fairness needs explicit "
                    "--game-profile=gr1 when tlsf-tools game semantics are "
                    "intended");
  } else {
    fprintf(stderr, "; legacy safety requires exactly one ordinary output");
  }
  fputc('\n', stderr);
  return false;
}

#ifndef NDEBUG
#define OXIDD_TRACE_USAGE                                                      \
  "  --oxidd-trace-roots    bounded reachable-node union at built roots\n"     \
  "  --oxidd-trace-gate INDEX\n"                                               \
  "                         selected normalized gate diagnostics\n"            \
  "  --oxidd-trace-node-limit N\n"                                             \
  "                         traversal limit (default: 100000 nodes)\n"         \
  "  --oxidd-trace-scratch BYTES\n"                                            \
  "                         traversal scratch cap (default: 16777216)\n"
#else
#define OXIDD_TRACE_USAGE ""
#endif

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Solve an AIGER safety or GR(1) game with the in-process OxiDD BDD "
      "solver.\n"
      "  FILE   aag game file (default: stdin; use '-' for stdin)\n"
      "  --game-profile=auto|legacy-safety|gr1|multi-safety\n"
      "                         game interpretation (default: auto)\n"
      "  --certificate FILE       export GR(1) certificate as ASCII AIGER\n"
      "  --certificate-json FILE  metadata sidecar (default FILE.json)\n"
      "  --policy FILE            export combinational GR(1) policy AAG\n"
      "  --policy-json FILE       policy mapping sidecar (default FILE.json)\n"
      "  --semantics exact|strict reduction semantics recorded in exports\n"
      "                         (default: exact; strict cannot export UNREAL)\n"
      "  --oxidd-nodes N        BDD node arena capacity, in entries\n"
      "  --oxidd-cache N        BDD apply-cache capacity, in entries\n"
      "                         capacity default: 2^(inputs+latches+6),\n"
      "                         clamped to 1024..4194304 entries\n"
      "  --oxidd-gc auto|pressure\n"
      "                         proactive GC policy (default: auto)\n"
      "  --oxidd-gc-threshold PERCENT\n"
      "                         pressure trigger (default: 80; pressure only)\n"
      "  --oxidd-var-order=input-first|state-first|fanin-dfs\n"
      "                         static BDD order (default: input-first)\n"
      "  --oxidd-order-file PATH\n"
      "                         strict tlsfsolve-order-v1 local permutation\n"
      "  --oxidd-build-plan=gates\n"
      "                         Boolean construction plan (default: "
      "gates)\n" OXIDD_TRACE_USAGE "  --oxidd-transitions eager|demand\n"
      "                         safety construction (default: eager)\n"
      "  --realizability-only   emit only a safety verdict\n"
      "                         (default: synthesize a full strategy)\n"
      "  -v, --verbose          diagnostic trace (default: off; requires\n"
      "                         non-NDEBUG)\n"
      "GC policy 'auto' leaves OxiDD automatic collection enabled. Both GC\n"
      "policies may collect once to retry a failed pure BDD operation.\n"
      "Exit 0: realizable — writes strategy aag to stdout.\n"
      "Exit 1: UNREALIZABLE — writes message to stderr.\n"
      "Exit 2: input, usage, or OxiDD solver failure.\n"
      "  --version, --help\n",
      prog);
}
#undef OXIDD_TRACE_USAGE

int main(int argc, char **argv) {
  const char *path = nullptr;
  const char *certificate_path = nullptr;
  const char *certificate_json_path = nullptr;
  const char *policy_path = nullptr;
  const char *policy_json_path = nullptr;
  Gr1CertificateSemantics certificate_semantics =
      GR1_CERTIFICATE_SEMANTICS_EXACT;
  char *default_certificate_json = nullptr;
  char *default_policy_json = nullptr;
  GameProfile requested_profile = PROFILE_AUTO, resolved_profile = PROFILE_AUTO;
  OxiddSolveOptions opts = oxidd_solve_options_default();
  OxiddFailure failure = {0};
  bool named_order = false;
  opts.failure = &failure;
  for (int i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "--realizability-only")) {
      opts.realizability_only = true;
      continue;
    }
    if (!strcmp(arg, "--help") || !strcmp(arg, "-h")) {
      usage(argv[0]);
      return 0;
    }
#ifndef NDEBUG
    if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose")) {
      opts.verbosity++;
      continue;
    }
    if (!strcmp(arg, "-vv")) {
      opts.verbosity += 2;
      continue;
    }
#else
    if (!strcmp(arg, "-v") || !strcmp(arg, "-vv") ||
        !strcmp(arg, "--verbose")) {
      fprintf(stderr,
              "%s: verbose diagnostics compiled out; rebuild with "
              "-Db_ndebug=false\n",
              argv[0]);
      return 2;
    }
#endif
    if (!strcmp(arg, "--version")) {
      printf("tlsfsolve %s oxidd=%s research=%s simd=%s diagnostics=%s "
             "oxidd_patch=%s\n",
             TLSF_PROJECT_VERSION, tlsf_build_oxidd(), tlsf_build_research(),
             tlsf_build_simd(),
#ifndef NDEBUG
             "yes",
#else
             "no",
#endif
             tlsf_build_oxidd_patch());
      return 0;
    }
    const char *val = option_value(&i, argc, argv, arg, "--certificate");
    if (val || !strcmp(arg, "--certificate")) {
      if (!val || !*val || !strcmp(val, "-")) {
        fprintf(stderr, "%s: --certificate requires a non-stdout FILE\n",
                argv[0]);
        usage(argv[0]);
        return 2;
      }
      certificate_path = val;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--certificate-json");
    if (val || !strcmp(arg, "--certificate-json")) {
      if (!val || !*val || !strcmp(val, "-")) {
        fprintf(stderr, "%s: --certificate-json requires a non-stdout FILE\n",
                argv[0]);
        usage(argv[0]);
        return 2;
      }
      certificate_json_path = val;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--policy");
    if (val || !strcmp(arg, "--policy")) {
      if (!val || !*val || !strcmp(val, "-")) {
        fprintf(stderr, "%s: --policy requires a non-stdout FILE\n", argv[0]);
        usage(argv[0]);
        return 2;
      }
      policy_path = val;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--policy-json");
    if (val || !strcmp(arg, "--policy-json")) {
      if (!val || !*val || !strcmp(val, "-")) {
        fprintf(stderr, "%s: --policy-json requires a non-stdout FILE\n",
                argv[0]);
        usage(argv[0]);
        return 2;
      }
      policy_json_path = val;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--semantics");
    if (val || !strcmp(arg, "--semantics")) {
      if (!val || !strcmp(val, "exact")) {
        certificate_semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
      } else if (!strcmp(val, "strict")) {
        certificate_semantics = GR1_CERTIFICATE_SEMANTICS_STRICT;
      } else {
        fprintf(stderr, "%s: bad --semantics '%s'\n", argv[0], val ? val : "");
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--game-profile");
    if (val) {
      if (!parse_profile(val, &requested_profile)) {
        fprintf(stderr, "%s: bad --game-profile '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-var-order");
    if (val) {
      if (opts.order_file || !parse_var_order(val, &opts.var_order)) {
        fprintf(stderr, "%s: bad or conflicting --oxidd-var-order '%s'\n",
                argv[0], val);
        return 2;
      }
      named_order = true;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-order-file");
    if (val) {
      if (named_order || opts.order_file || !*val) {
        fprintf(stderr, "%s: bad or conflicting --oxidd-order-file '%s'\n",
                argv[0], val);
        return 2;
      }
      opts.order_file = val;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-build-plan");
    if (val) {
      if (strcmp(val, "gates")) {
        fprintf(stderr, "%s: bad --oxidd-build-plan '%s'\n", argv[0], val);
        return 2;
      }
      opts.build_plan = OXIDD_BUILD_GATES;
      continue;
    }
#ifndef NDEBUG
    if (!strcmp(arg, "--oxidd-trace-roots")) {
      opts.trace_roots = true;
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-trace-gate");
    if (val) {
      if (!parse_u32_value(val, &opts.trace_gate)) {
        fprintf(stderr, "%s: bad --oxidd-trace-gate '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-trace-node-limit");
    if (val) {
      if (!parse_size_value(val, &opts.trace_node_limit)) {
        fprintf(stderr, "%s: bad --oxidd-trace-node-limit '%s'\n", argv[0],
                val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-trace-scratch");
    if (val) {
      if (!parse_size_value(val, &opts.trace_scratch_bytes)) {
        fprintf(stderr, "%s: bad --oxidd-trace-scratch '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
#endif
    val = option_value(&i, argc, argv, arg, "--oxidd-transitions");
    if (val) {
      if (strcmp(val, "eager") && strcmp(val, "demand")) {
        fprintf(stderr, "%s: bad --oxidd-transitions '%s'\n", argv[0], val);
        return 2;
      }
      opts.demand_transitions = !strcmp(val, "demand");
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-nodes");
    if (val) {
      if (!parse_size_value(val, &opts.node_cap)) {
        fprintf(stderr, "%s: bad --oxidd-nodes '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-cache");
    if (val) {
      if (!parse_size_value(val, &opts.cache_cap)) {
        fprintf(stderr, "%s: bad --oxidd-cache '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-gc");
    if (val) {
      if (!strcmp(val, "auto")) {
        opts.gc_mode = OXIDD_GC_AUTO;
      } else if (!strcmp(val, "pressure")) {
        opts.gc_mode = OXIDD_GC_PRESSURE;
      } else {
        fprintf(stderr, "%s: bad --oxidd-gc '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-gc-threshold");
    if (val) {
      size_t parsed = 0;
      if (!parse_size_value(val, &parsed) || parsed > 100) {
        fprintf(stderr, "%s: bad --oxidd-gc-threshold '%s'\n", argv[0], val);
        return 2;
      }
      opts.gc_threshold_percent = (unsigned)parsed;
      continue;
    }
    if (!strcmp(arg, "-")) {
      path = nullptr;
    } else if (arg[0] != '-') {
      if (path) {
        fprintf(stderr, "%s: more than one input file\n", argv[0]);
        return 2;
      }
      path = arg;
    } else {
      fprintf(stderr, "%s: unknown option '%s'\n", argv[0], arg);
      usage(argv[0]);
      return 2;
    }
  }
  if (certificate_json_path && !certificate_path) {
    fprintf(stderr, "%s: --certificate-json requires --certificate FILE\n",
            argv[0]);
    usage(argv[0]);
    return 2;
  }
  if (policy_json_path && !policy_path) {
    fprintf(stderr, "%s: --policy-json requires --policy FILE\n", argv[0]);
    usage(argv[0]);
    return 2;
  }
  if (certificate_path && !certificate_json_path) {
    size_t n = strlen(certificate_path) + sizeof ".json";
    default_certificate_json = malloc(n);
    if (!default_certificate_json) {
      fprintf(stderr, "%s: cannot allocate certificate sidecar path\n",
              argv[0]);
      return 2;
    }
    snprintf(default_certificate_json, n, "%s.json", certificate_path);
    certificate_json_path = default_certificate_json;
  }
  if (policy_path && !policy_json_path) {
    size_t n = strlen(policy_path) + sizeof ".json";
    default_policy_json = malloc(n);
    if (!default_policy_json) {
      fprintf(stderr, "%s: cannot allocate policy sidecar path\n", argv[0]);
      free(default_certificate_json);
      return 2;
    }
    snprintf(default_policy_json, n, "%s.json", policy_path);
    policy_json_path = default_policy_json;
  }

  FILE *in = path ? fopen(path, "r") : stdin;
  if (!in) {
    perror(path);
    free(default_certificate_json);
    free(default_policy_json);
    return 2;
  }

  Aig *game = aig_read_aag(in);
  if (path)
    fclose(in);
  if (!game) {
    fprintf(stderr, "%s: failed to parse aag game\n", argv[0]);
    free(default_certificate_json);
    free(default_policy_json);
    return 2;
  }

  if (!resolve_profile(game, requested_profile, &resolved_profile, argv[0]) ||
      !validate_supported_resets(game, argv[0])) {
    aig_free(game);
    free(default_certificate_json);
    free(default_policy_json);
    return 2;
  }
  if (resolved_profile == PROFILE_GR1) {
    char reason[128];
    if (!tlsf_gr1_validate_game(game, reason, sizeof reason)) {
      fprintf(stderr, "%s: %s\n", argv[0], reason);
      aig_free(game);
      free(default_certificate_json);
      free(default_policy_json);
      return 2;
    }
  }

  oxidd_trace(&opts, "resolve_profile", "game",
              ",\"profile_requested\":\"%s\",\"profile\":\"%s\","
              "\"outputs\":%u,\"bad\":%u,\"constraints\":%u,"
              "\"justice\":%u,\"fairness\":%u,\"controllable_input\":%s",
              profile_name(requested_profile), profile_name(resolved_profile),
              aig_num_outputs(game), aig_num_bad(game),
              aig_num_constraints(game), aig_num_justice(game),
              aig_num_fairness(game),
              has_controllable_input(game) ? "true" : "false");

  if (resolved_profile == PROFILE_MULTI_SAFETY ||
      (resolved_profile == PROFILE_GR1 &&
       (aig_num_bad(game) > 0 || aig_num_outputs(game) != 1))) {
    opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR;
  } else {
    opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT;
    opts.safety_output_index = 0;
  }

  int unreal = 0;
  if ((certificate_path || policy_path) && resolved_profile != PROFILE_GR1) {
    fprintf(
        stderr,
        "%s: certificate/policy export requires a GR(1) game with justice\n",
        argv[0]);
    aig_free(game);
    free(default_certificate_json);
    free(default_policy_json);
    return 2;
  }
  Gr1CertificateOptions certificate = {

      .aag_path = certificate_path,
      .json_path = certificate_json_path,
      .policy_aag_path = policy_path,
      .policy_json_path = policy_json_path,
      .semantics = certificate_semantics,
  };
  Aig *strat = nullptr;
  if (resolved_profile == PROFILE_GR1) {
    if (opts.demand_transitions || opts.realizability_only) {
      fprintf(stderr, "tlsfsolve: demand transitions and verdict-only require "
                      "a safety profile\n");
      aig_free(game);
      free(default_certificate_json);
      free(default_policy_json);
      return 2;
    }
    strat = certificate_path || policy_path
                ? solve_gr1_oxidd_ex_with_certificate(game, &unreal, &opts,
                                                      &certificate)
                : solve_gr1_oxidd_ex(game, &unreal, &opts);
  } else {
    OxiddSolveResult result = solve_safety_oxidd_result(game, &opts);
    strat = result.strategy;
    unreal = result.status == OXIDD_SOLVE_UNREALIZABLE;
    if (result.status == OXIDD_SOLVE_REALIZABLE && opts.realizability_only) {
      fprintf(stderr, "REALIZABLE\n");
      free(default_certificate_json);
      free(default_policy_json);
      return 0;
    }
  }

  if (!strat) {
    if (certificate.failed) {
      fprintf(stderr, "%s: %s\n", argv[0], certificate.error);
      free(default_certificate_json);
      free(default_policy_json);
      return 2;
    }
    if (unreal) {
      fprintf(stderr, "UNREALIZABLE\n");
      free(default_certificate_json);
      free(default_policy_json);
      return 1;
    }
    fprintf(stderr, "tlsfsolve: OxiDD solver failed\n");
    if (failure.kind != OXIDD_FAILURE_NONE)
      fprintf(
          stderr,
          "tlsfsolve: failure kind=%u phase=%s operation=%s id=%zu index=%u\n",
          (unsigned)failure.kind, failure.phase, failure.operation,
          failure.operation_id, failure.index);
    if (failure.kind == OXIDD_FAILURE_BDD || failure.kind == OXIDD_FAILURE_HOST)
      fprintf(stderr,
              "tlsfsolve: allocation failure: rebuild with diagnostics "
              "(-Db_ndebug=false),\n"
              "tlsfsolve: rerun with scripts/diagnose_tlsfsolve.py, and attach "
              "its bundle\n"
              "tlsfsolve: to a bug report; see "
              "docs/tlsfsolve-diagnostics.md\n");
    free(default_certificate_json);
    free(default_policy_json);
    return 2;
  }

  aig_write_aag(stdout, strat);
  aig_free(strat);
  if (fflush(stdout) != 0 || ferror(stdout)) {
    fprintf(stderr, "tlsfsolve: strategy output failed\n");
    free(default_certificate_json);
    free(default_policy_json);
    return 2;
  }
  free(default_certificate_json);
  free(default_policy_json);
  return 0;
}
