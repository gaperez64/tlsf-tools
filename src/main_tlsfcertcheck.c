// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L

/// tlsfcertcheck — independently check a GR(1) policy at its target size.
///
/// The certificate path checks only one-step implications.  In particular it
/// does not run the GR(1) winning-region fixpoint.  For a current goal j, every
/// invariant state has a least lexicographic rank (k,i).  Unless goal_j holds,
/// the checked policy moves to goal_j, a smaller k, or remains in X[j,k,i]
/// while fairness i is false at the successor.  Along a fair play k can fall
/// only finitely often, i can fall only finitely often at a fixed k, and an
/// infinite stay at a fixed (k,i) makes fair_i false forever.  Thus a play
/// satisfying every environment fairness assumption must reach goal_j and
/// advance the counter; cycling the counter proves every system justice.
///
/// Soundness invariant: REFUTED is claimed only when the policy is genuinely
/// losing.  A failed certificate condition is CERT_FAILED: the sufficient
/// proof did not go through, but nothing follows about the policy itself.
///
/// The independent fallback composes the policy with the game, computes the
/// reachable closed loop, and uses an existential Emerson-Lei generalized-
/// Buchi fixpoint to search for a reachable fair cycle missing one justice.
/// --json-out writes tlsf-gr1-checkresult-v1: an overall verdict and resource
/// totals plus per-method verdict, time, peak nodes, and structured witness.

#include "tlsf/aiger.h"
#include "tlsf/build_info.h"
#include "tlsf/oxidd_common.h"

#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum {
  EXIT_VERIFIED = 0,
  EXIT_REFUTED = 1,
  EXIT_ERROR = 2,
  EXIT_UNKNOWN = 3,
  EXIT_INVALID = 4,
  EXIT_INTERNAL = 5,
  EXIT_CERT_FAILED = 6,
};

typedef enum {
  CHECK_VERIFIED,
  CHECK_REFUTED,
  CHECK_UNKNOWN,
  CHECK_INVALID,
  CHECK_CERT_FAILED,
  CHECK_SKIPPED,
} CheckResult;

typedef enum {
  METHOD_AUTO,
  METHOD_CERTIFICATE,
  METHOD_CLOSED_LOOP,
  METHOD_BOTH
} Method;

typedef struct {
  uint32_t levels;
  Bdd *y;
  Bdd **x;
} RankGoal;

typedef struct {
  uint32_t levels;
  Bdd *x;
} DualInnerRank;

typedef struct {
  Bdd z;
  Bdd *y;
  DualInnerRank *inner;
} DualOuterRank;

typedef struct {
  bool present;
  bool has_control;
  char reason[128];
  uint8_t *state;
  uint8_t *curr;
  uint8_t *inputs;
  uint8_t *control;
} Counterexample;

typedef struct {
  CheckResult result;
  double seconds;
  size_t peak_nodes;
  Counterexample counterexample;
} MethodReport;

typedef struct {
  const char *game_path;
  const char *policy_path;
  const char *policy_json_path;
  const char *certificate_path;
  const char *certificate_json_path;
  const char *json_out_path;
  const char *emit_path;
  Method method;
  double timeout;
  size_t node_cap;
  bool stats;
  bool test_unspecialized_policy;
  bool test_rebuild_successor;
} Options;

typedef struct {
  Options options;
  Aig *game;
  Aig *policy;
  Aig *certificate;
  oxidd_bdd_manager_t manager;
  uint32_t original_nlat;
  uint32_t nstate, nin, nu, nc, ngoals, nfair, nfair_disj, nq, nvars;
  uint32_t *uinput, *cinput;
  uint32_t *qvar, *qpvar, *uvar, *cvar;
  Bdd *q, *qp, *u, *c;
  Bdd *game_next, game_bad, *goal, *fair, *cert_goal;
  Bdd *policy_control, *policy_curr_next;
  Bdd cert_inv, *cert_fair;
  RankGoal *rank;
  DualOuterRank *dual_rank;
  Bdd input_cube;
  uint32_t ncounter, ndual_levels, npolicy_choices;
  bool environment;
  bool bdd_failed;
  bool run_initialized;
  Counterexample *current_counterexample;
  OxiddFailure failure;
  OxiddSolveOptions bdd_options;
  OxiddRun run;
  double started;
  double setup_seconds, proof_seconds;
  size_t requested_roots, policy_mode_builds, policy_counter_constants;
  size_t policy_specialized_gates, policy_unspecialized_gates;
  size_t successor_substitutions, successor_applications;
  size_t peak_nodes;
} Checker;

typedef struct {
  const Aig *aig;
  uint32_t *root_by_output;
  Bdd *roots;
  size_t nroots;
} Compiled;

static Bdd initial_cube(Checker *ck);

static double now_seconds(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

static bool timed_out(const Checker *ck) {
  return ck->options.timeout > 0 &&
         now_seconds() - ck->started >= ck->options.timeout;
}

static void update_peak(Checker *ck) {
  size_t nodes = oxidd_bdd_manager_approx_num_inner_nodes(ck->manager);
  if (nodes > ck->peak_nodes)
    ck->peak_nodes = nodes;
}

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] GAME POLICY\n"
          "Check a combinational GR(1) policy without solving the game.\n"
          "  --policy-json FILE       policy mapping sidecar (default "
          "POLICY.json)\n"
          "  --certificate FILE       M2 certificate AAG\n"
          "  --certificate-json FILE  M2 sidecar (default CERTIFICATE.json)\n"
          "  --method NAME            auto|certificate|closed-loop|both\n"
          "  --json-out FILE          write tlsf-gr1-checkresult-v1 JSON\n"
          "  --emit-controller FILE   emit the checked standalone controller\n"
          "  --timeout SECONDS        return UNKNOWN after the soft deadline\n"
          "  --node-cap N             OxiDD inner-node cap (default 16777216)\n"
          "  --stats                  write construction/proof diagnostics to "
          "stderr\n"
          "Exit 0 VERIFIED, 1 REFUTED, 2 ERROR, 3 UNKNOWN, 4 INVALID,\n"
          "     5 INTERNAL-ERROR (verified certificate contradicted by the "
          "closed loop),\n"
          "     6 CERT_FAILED (a form of UNKNOWN: the certificate does not "
          "prove this policy;\n"
          "       nothing is concluded about the policy itself).\n",
          prog);
}

static bool parse_u64(const char *text, uint64_t *value) {
  char *end = nullptr;
  errno = 0;
  unsigned long long parsed = strtoull(text, &end, 10);
  if (errno || end == text || *end != '\0')
    return false;
  *value = (uint64_t)parsed;
  return true;
}

static bool parse_double(const char *text, double *value) {
  char *end = nullptr;
  errno = 0;
  double parsed = strtod(text, &end);
  if (errno || end == text || *end != '\0' || parsed < 0)
    return false;
  *value = parsed;
  return true;
}

static char *sidecar_default(const char *path) {
  size_t n = strlen(path) + sizeof ".json";
  char *result = malloc(n);
  if (result)
    snprintf(result, n, "%s.json", path);
  return result;
}

static int parse_options(int argc, char **argv, Options *options,
                         char **owned_policy_json, char **owned_cert_json) {
  *options =
      (Options){.method = METHOD_AUTO, .timeout = 0, .node_cap = 1u << 24};
  const char *positional[2] = {nullptr, nullptr};
  uint32_t npos = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
      usage(argv[0]);
      return 1;
    }
    if (!strcmp(argv[i], "--version")) {
      printf("tlsfcertcheck %s oxidd=%s research=%s simd=%s\n",
             TLSF_PROJECT_VERSION, tlsf_build_oxidd(), tlsf_build_research(),
             tlsf_build_simd());
      return 1;
    }
    if (!strcmp(argv[i], "--stats")) {
      options->stats = true;
      continue;
    }
    if (!strcmp(argv[i], "--test-unspecialized-policy")) {
      options->test_unspecialized_policy = true;
      continue;
    }
    if (!strcmp(argv[i], "--test-rebuild-successor")) {
      options->test_rebuild_successor = true;
      continue;
    }
    const char **slot = nullptr;
    if (!strcmp(argv[i], "--policy-json"))
      slot = &options->policy_json_path;
    else if (!strcmp(argv[i], "--certificate"))
      slot = &options->certificate_path;
    else if (!strcmp(argv[i], "--certificate-json"))
      slot = &options->certificate_json_path;
    else if (!strcmp(argv[i], "--json-out"))
      slot = &options->json_out_path;
    else if (!strcmp(argv[i], "--emit-controller"))
      slot = &options->emit_path;
    if (slot) {
      if (++i == argc) {
        fprintf(stderr, "%s: option requires a value\n", argv[0]);
        return -1;
      }
      *slot = argv[i];
      continue;
    }
    if (!strcmp(argv[i], "--method")) {
      if (++i == argc) {
        fprintf(stderr, "%s: --method requires a value\n", argv[0]);
        return -1;
      }
      if (!strcmp(argv[i], "auto"))
        options->method = METHOD_AUTO;
      else if (!strcmp(argv[i], "certificate"))
        options->method = METHOD_CERTIFICATE;
      else if (!strcmp(argv[i], "closed-loop"))
        options->method = METHOD_CLOSED_LOOP;
      else if (!strcmp(argv[i], "both"))
        options->method = METHOD_BOTH;
      else {
        fprintf(stderr, "%s: unknown method '%s'\n", argv[0], argv[i]);
        return -1;
      }
      continue;
    }
    if (!strcmp(argv[i], "--timeout")) {
      if (++i == argc || !parse_double(argv[i], &options->timeout)) {
        fprintf(stderr, "%s: invalid --timeout\n", argv[0]);
        return -1;
      }
      continue;
    }
    if (!strcmp(argv[i], "--node-cap")) {
      uint64_t cap;
      if (++i == argc || !parse_u64(argv[i], &cap) || cap < 1024 ||
          cap > SIZE_MAX) {
        fprintf(stderr, "%s: invalid --node-cap\n", argv[0]);
        return -1;
      }
      options->node_cap = (size_t)cap;
      continue;
    }
    if (argv[i][0] == '-') {
      fprintf(stderr, "%s: unknown option '%s'\n", argv[0], argv[i]);
      return -1;
    }
    if (npos == 2) {
      fprintf(stderr, "%s: too many positional arguments\n", argv[0]);
      return -1;
    }
    positional[npos++] = argv[i];
  }
  if (npos != 2) {
    usage(argv[0]);
    return -1;
  }
  options->game_path = positional[0];
  options->policy_path = positional[1];
  if (!options->policy_json_path) {
    *owned_policy_json = sidecar_default(options->policy_path);
    options->policy_json_path = *owned_policy_json;
  }
  if (options->certificate_path && !options->certificate_json_path) {
    *owned_cert_json = sidecar_default(options->certificate_path);
    options->certificate_json_path = *owned_cert_json;
  }
  if (options->certificate_json_path && !options->certificate_path) {
    fprintf(stderr, "%s: --certificate-json requires --certificate\n", argv[0]);
    return -1;
  }
  if ((options->method == METHOD_CERTIFICATE ||
       options->method == METHOD_BOTH) &&
      !options->certificate_path) {
    fprintf(stderr, "%s: selected method requires --certificate\n", argv[0]);
    return -1;
  }
  return 0;
}

static char *read_text_file(const char *path) {
  FILE *in = fopen(path, "rb");
  if (!in)
    return nullptr;
  if (fseek(in, 0, SEEK_END) != 0) {
    fclose(in);
    return nullptr;
  }
  long end = ftell(in);
  if (end < 0 || fseek(in, 0, SEEK_SET) != 0) {
    fclose(in);
    return nullptr;
  }
  char *text = malloc((size_t)end + 1);
  if (!text) {
    fclose(in);
    return nullptr;
  }
  size_t got = fread(text, 1, (size_t)end, in);
  bool ok = got == (size_t)end && !ferror(in);
  fclose(in);
  if (!ok) {
    free(text);
    return nullptr;
  }
  text[got] = '\0';
  return text;
}

static bool json_has_string(const char *text, const char *key,
                            const char *value) {
  char pattern[256];
  snprintf(pattern, sizeof pattern, "\"%s\"", key);
  const char *p = strstr(text, pattern);
  if (!p)
    return false;
  p = strchr(p + strlen(pattern), ':');
  if (!p)
    return false;
  p++;
  while (isspace((unsigned char)*p))
    p++;
  size_t n = strlen(value);
  return *p == '"' && strncmp(p + 1, value, n) == 0 && p[n + 1] == '"';
}

static bool json_uint(const char *text, const char *key, uint32_t *value) {
  char pattern[256];
  snprintf(pattern, sizeof pattern, "\"%s\"", key);
  const char *p = strstr(text, pattern);
  if (!p || !(p = strchr(p + strlen(pattern), ':')))
    return false;
  p++;
  while (isspace((unsigned char)*p))
    p++;
  char *end;
  unsigned long parsed = strtoul(p, &end, 10);
  if (end == p || parsed > UINT32_MAX)
    return false;
  *value = (uint32_t)parsed;
  return true;
}

static bool json_bool(const char *text, const char *key, bool value) {
  char pattern[256];
  snprintf(pattern, sizeof pattern, "\"%s\"", key);
  const char *p = strstr(text, pattern);
  if (!p || !(p = strchr(p + strlen(pattern), ':')))
    return false;
  p++;
  while (isspace((unsigned char)*p))
    p++;
  const char *expected = value ? "true" : "false";
  size_t n = strlen(expected);
  return strncmp(p, expected, n) == 0 && !isalnum((unsigned char)p[n]) &&
         p[n] != '_';
}

static Aig *read_aag(const char *path, bool game, char *error,
                     size_t error_cap) {
  FILE *in = fopen(path, "r");
  if (!in) {
    snprintf(error, error_cap, "cannot open '%s': %s", path, strerror(errno));
    return nullptr;
  }
  Aig *result = aig_read_aag(in);
  fclose(in);
  if (!result)
    snprintf(error, error_cap, "malformed ASCII AIGER %s'%s'",
             game ? "game " : "", path);
  return result;
}

static const char *latch_name(const Aig *game, uint32_t index, char *fallback,
                              size_t cap) {
  const char *name = aig_latch_name(game, index);
  if (name)
    return name;
  snprintf(fallback, cap, "l%u", index);
  return fallback;
}

static bool duplicate_inputs_or_outputs(const Aig *aig, const char **kind,
                                        const char **name) {
  for (uint32_t i = 0; i < aig_num_inputs(aig); i++) {
    const char *a = aig_input_name(aig, i, nullptr);
    if (!a) {
      *kind = "unnamed input";
      *name = "";
      return true;
    }
    for (uint32_t j = i + 1; j < aig_num_inputs(aig); j++) {
      const char *b = aig_input_name(aig, j, nullptr);
      if (b && !strcmp(a, b)) {
        *kind = "duplicate input";
        *name = a;
        return true;
      }
    }
  }
  for (uint32_t i = 0; i < aig_num_outputs(aig); i++) {
    const char *a = aig_output_at(aig, i, nullptr);
    for (uint32_t j = i + 1; j < aig_num_outputs(aig); j++) {
      const char *b = aig_output_at(aig, j, nullptr);
      if (!strcmp(a, b)) {
        *kind = "duplicate output";
        *name = a;
        return true;
      }
    }
  }
  return false;
}

static bool has_input(const Aig *aig, const char *name) {
  for (uint32_t i = 0; i < aig_num_inputs(aig); i++) {
    const char *candidate = aig_input_name(aig, i, nullptr);
    if (candidate && !strcmp(candidate, name))
      return true;
  }
  return false;
}

static bool has_output(const Aig *aig, const char *name) {
  return aig_output_lit(aig, name) != UINT32_MAX;
}

static uint32_t count_goals(const Aig *game) {
  uint32_t count = 0;
  for (uint32_t j = 0; j < aig_num_justice(game); j++) {
    uint32_t n;
    aig_justice_at(game, j, nullptr, &n);
    count += n ? n : 1;
  }
  return count;
}

static bool validate_sidecars(Checker *ck, char *message, size_t cap) {
  char *policy = read_text_file(ck->options.policy_json_path);
  if (!policy) {
    snprintf(message, cap, "cannot read policy sidecar '%s'",
             ck->options.policy_json_path);
    return false;
  }
  uint32_t nstate, goals;
  bool policy_environment = json_has_string(policy, "side", "environment");
  bool policy_system =
      json_has_string(policy, "side", "system") || !strstr(policy, "\"side\"");
  bool ok = json_has_string(policy, "format", "tlsf-gr1-policy-v1") &&
            json_uint(policy, "game_state_variables", &nstate) &&
            json_uint(policy, "goals", &goals) && nstate == ck->nstate &&
            goals == ck->ngoals && (policy_environment || policy_system);
  if (ok && policy_environment) {
    uint32_t counters;
    ok = json_has_string(policy, "reduction_semantics", "exact") &&
         json_has_string(policy, "strategy_semantics", "moore") &&
         json_uint(policy, "fairness_counters", &counters) &&
         counters == ck->nfair_disj;
  }
  ck->environment = policy_environment;
  ck->ncounter = ck->environment ? ck->nfair_disj : ck->ngoals;
  free(policy);
  if (!ok) {
    snprintf(message, cap, "policy sidecar does not match this game");
    return false;
  }
  if (!ck->options.certificate_path)
    return true;
  char *certificate = read_text_file(ck->options.certificate_json_path);
  if (!certificate) {
    snprintf(message, cap, "cannot read certificate sidecar '%s'",
             ck->options.certificate_json_path);
    return false;
  }
  uint32_t fairness;
  bool certificate_environment =
      json_has_string(certificate, "side", "environment");
  ok = json_has_string(certificate, "format", "tlsf-gr1-certificate-v1") &&
       json_has_string(certificate, "status",
                       ck->environment ? "unrealizable" : "realizable") &&
       certificate_environment == ck->environment &&
       json_uint(certificate, "state_variables", &nstate) &&
       json_uint(certificate, "goals", &goals) &&
       json_uint(certificate, "fairness_assumptions", &fairness) &&
       nstate == ck->nstate && goals == ck->ngoals && fairness == ck->nfair;
  if (ok && ck->environment)
    ok = json_has_string(certificate, "reduction_semantics", "exact") &&
         json_has_string(certificate, "strategy_semantics", "moore") &&
         json_bool(certificate, "environment_counter_strategy_exported", true);
  free(certificate);
  if (!ok) {
    snprintf(message, cap, "certificate sidecar does not match this game");
    return false;
  }
  return true;
}

static bool validate_policy_interface(Checker *ck, char *message, size_t cap) {
  const char *kind, *name;
  if (duplicate_inputs_or_outputs(ck->policy, &kind, &name)) {
    snprintf(message, cap, "%s%s%s", kind, *name ? ": " : "", name);
    return false;
  }
  if (aig_num_latches(ck->policy) != 0 || aig_num_justice(ck->policy) != 0 ||
      aig_num_fairness(ck->policy) != 0) {
    snprintf(message, cap, "policy must be a combinational AIG");
    return false;
  }
  uint32_t expected_inputs =
      ck->nstate + ck->ncounter + (ck->environment ? 0 : ck->nu);
  uint32_t expected_outputs =
      (ck->environment ? ck->nu : ck->nc) + ck->ncounter;
  if (aig_num_inputs(ck->policy) != expected_inputs ||
      aig_num_outputs(ck->policy) != expected_outputs) {
    snprintf(message, cap,
             "policy arity mismatch (inputs %u/%u, outputs %u/%u)",
             aig_num_inputs(ck->policy), expected_inputs,
             aig_num_outputs(ck->policy), expected_outputs);
    return false;
  }
  for (uint32_t j = 0; j < ck->nstate; j++) {
    char fallback[32];
    name = latch_name(ck->game, j, fallback, sizeof fallback);
    if (!has_input(ck->policy, name)) {
      snprintf(message, cap, "policy is missing state input '%s'", name);
      return false;
    }
  }
  char generated[96];
  for (uint32_t j = 0; j < ck->ncounter; j++) {
    snprintf(generated, sizeof generated, "curr_%u", j);
    if (!has_input(ck->policy, generated)) {
      snprintf(message, cap, "policy is missing counter input '%s'", generated);
      return false;
    }
    snprintf(generated, sizeof generated, "curr_next_%u", j);
    if (!has_output(ck->policy, generated)) {
      snprintf(message, cap, "policy is missing counter output '%s'",
               generated);
      return false;
    }
  }
  for (uint32_t p = 0; p < ck->nin; p++) {
    name = aig_input_name(ck->game, p, nullptr);
    if (ck->environment) {
      if (!is_controllable(name) && !has_output(ck->policy, name)) {
        snprintf(message, cap,
                 "environment policy is missing uncontrollable output '%s'",
                 name);
        return false;
      }
      if (is_controllable(name) && has_input(ck->policy, name)) {
        snprintf(message, cap,
                 "Moore environment policy reads current controllable '%s'",
                 name);
        return false;
      }
    } else if (is_controllable(name)) {
      if (!has_output(ck->policy, name)) {
        snprintf(message, cap, "policy is missing controllable output '%s'",
                 name);
        return false;
      }
    } else if (!has_input(ck->policy, name)) {
      snprintf(message, cap, "policy is missing uncontrollable input '%s'",
               name);
      return false;
    }
  }
  // Counts plus membership prove there are no extra names.
  return true;
}

static bool validate_game_names(Checker *ck, char *message, size_t cap) {
  for (uint32_t p = 0; p < ck->nin; p++) {
    const char *left = aig_input_name(ck->game, p, nullptr);
    for (uint32_t q = p + 1; q < ck->nin; q++)
      if (!strcmp(left, aig_input_name(ck->game, q, nullptr))) {
        snprintf(message, cap, "duplicate game input name '%s'", left);
        return false;
      }
  }
  for (uint32_t s = 0; s < ck->nstate; s++) {
    char left_fallback[32];
    const char *left =
        latch_name(ck->game, s, left_fallback, sizeof left_fallback);
    for (uint32_t t = s + 1; t < ck->nstate; t++) {
      char right_fallback[32];
      const char *right =
          latch_name(ck->game, t, right_fallback, sizeof right_fallback);
      if (!strcmp(left, right)) {
        snprintf(message, cap, "duplicate game state name '%s'", left);
        return false;
      }
    }
    for (uint32_t p = 0; p < ck->nin; p++)
      if (!strcmp(left, aig_input_name(ck->game, p, nullptr))) {
        snprintf(message, cap, "game state/input name overlap '%s'", left);
        return false;
      }
  }
  char reserved[64];
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    snprintf(reserved, sizeof reserved, "curr_%u", j);
    for (uint32_t p = 0; p < ck->nin; p++)
      if (!strcmp(reserved, aig_input_name(ck->game, p, nullptr))) {
        snprintf(message, cap, "game input uses reserved name '%s'", reserved);
        return false;
      }
    for (uint32_t s = 0; s < ck->nstate; s++) {
      char fallback[32];
      if (!strcmp(reserved,
                  latch_name(ck->game, s, fallback, sizeof fallback))) {
        snprintf(message, cap, "game state uses reserved name '%s'", reserved);
        return false;
      }
    }
  }
  for (uint32_t i = 0; i < ck->nc; i++) {
    const char *name = aig_input_name(ck->game, ck->cinput[i], nullptr);
    if (name[strlen(CONTROLLABLE_PREFIX)] == '\0') {
      snprintf(message, cap, "empty controllable signal name");
      return false;
    }
  }
  return true;
}

static bool output_is_expected_certificate(Checker *ck, const char *name,
                                           const uint32_t *levels) {
  if (!strcmp(name, "inv"))
    return true;
  char expected[96];
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    snprintf(expected, sizeof expected, "goal_%u", j);
    if (!strcmp(name, expected))
      return true;
    snprintf(expected, sizeof expected, "move_%u", j);
    if (!strcmp(name, expected))
      return true;
    for (uint32_t k = 0; k < levels[j]; k++) {
      snprintf(expected, sizeof expected, "y_%u_%u", j, k);
      if (!strcmp(name, expected))
        return true;
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        snprintf(expected, sizeof expected, "x_%u_%u_%u", j, k, i);
        if (!strcmp(name, expected))
          return true;
      }
    }
  }
  return false;
}

static bool output_is_expected_environment_certificate(Checker *ck,
                                                       const char *name,
                                                       const uint32_t *levels) {
  if (!strcmp(name, "inv") || !strcmp(name, "system_winning"))
    return true;
  char expected[128];
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    snprintf(expected, sizeof expected, "goal_%u", j);
    if (!strcmp(name, expected))
      return true;
  }
  for (uint32_t i = 0; i < ck->nfair; i++) {
    snprintf(expected, sizeof expected, "fair_%u", i);
    if (!strcmp(name, expected))
      return true;
  }
  for (uint32_t i = 0; i < ck->nfair_disj; i++) {
    snprintf(expected, sizeof expected, "move_%u", i);
    if (!strcmp(name, expected))
      return true;
  }
  uint32_t outer_levels = levels[0];
  for (uint32_t k = 0; k < outer_levels; k++) {
    snprintf(expected, sizeof expected, "z_%u", k);
    if (!strcmp(name, expected))
      return true;
    for (uint32_t j = 0; j < ck->ngoals; j++) {
      snprintf(expected, sizeof expected, "y_%u_%u", k, j);
      if (!strcmp(name, expected))
        return true;
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        size_t index = 1 + ((size_t)k * ck->ngoals + j) * ck->nfair_disj + i;
        for (uint32_t l = 0; l < levels[index]; l++) {
          snprintf(expected, sizeof expected, "x_%u_%u_%u_%u", k, j, i, l);
          if (!strcmp(name, expected))
            return true;
        }
      }
    }
  }
  return false;
}

static bool validate_environment_certificate_interface(Checker *ck,
                                                       uint32_t **levels_out,
                                                       char *message,
                                                       size_t cap) {
  const char *kind, *name;
  if (duplicate_inputs_or_outputs(ck->certificate, &kind, &name)) {
    snprintf(message, cap, "%s%s%s", kind, *name ? ": " : "", name);
    return false;
  }
  if (aig_num_latches(ck->certificate) != 0 ||
      aig_num_justice(ck->certificate) != 0 ||
      aig_num_fairness(ck->certificate) != 0 ||
      aig_num_inputs(ck->certificate) != ck->nstate + ck->nin) {
    snprintf(message, cap, "environment certificate shape does not match game");
    return false;
  }
  for (uint32_t j = 0; j < ck->nstate; j++) {
    char fallback[32];
    name = latch_name(ck->game, j, fallback, sizeof fallback);
    if (!has_input(ck->certificate, name)) {
      snprintf(message, cap, "certificate is missing state input '%s'", name);
      return false;
    }
  }
  for (uint32_t p = 0; p < ck->nin; p++) {
    name = aig_input_name(ck->game, p, nullptr);
    if (!has_input(ck->certificate, name)) {
      snprintf(message, cap, "certificate is missing game input '%s'", name);
      return false;
    }
  }
  if (!has_output(ck->certificate, "inv") ||
      !has_output(ck->certificate, "system_winning")) {
    snprintf(message, cap, "environment certificate is missing its region");
    return false;
  }
  char generated[128];
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    snprintf(generated, sizeof generated, "goal_%u", j);
    if (!has_output(ck->certificate, generated))
      goto missing;
  }
  for (uint32_t i = 0; i < ck->nfair; i++) {
    snprintf(generated, sizeof generated, "fair_%u", i);
    if (!has_output(ck->certificate, generated))
      goto missing;
  }
  for (uint32_t i = 0; i < ck->nfair_disj; i++) {
    snprintf(generated, sizeof generated, "move_%u", i);
    if (!has_output(ck->certificate, generated))
      goto missing;
  }
  uint32_t outer_levels = 0;
  for (;;) {
    snprintf(generated, sizeof generated, "z_%u", outer_levels);
    if (!has_output(ck->certificate, generated))
      break;
    outer_levels++;
  }
  if (!outer_levels) {
    snprintf(message, cap, "environment certificate has no outer rank levels");
    return false;
  }
  size_t count = 1 + (size_t)outer_levels * ck->ngoals * ck->nfair_disj;
  uint32_t *levels = calloc(count, sizeof *levels);
  if (!levels) {
    snprintf(message, cap, "out of memory");
    return false;
  }
  levels[0] = outer_levels;
  for (uint32_t k = 0; k < outer_levels; k++)
    for (uint32_t j = 0; j < ck->ngoals; j++) {
      snprintf(generated, sizeof generated, "y_%u_%u", k, j);
      if (!has_output(ck->certificate, generated))
        goto missing_levels;
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        size_t index = 1 + ((size_t)k * ck->ngoals + j) * ck->nfair_disj + i;
        for (;;) {
          snprintf(generated, sizeof generated, "x_%u_%u_%u_%u", k, j, i,
                   levels[index]);
          if (!has_output(ck->certificate, generated))
            break;
          levels[index]++;
        }
        if (!levels[index])
          goto missing_levels;
      }
    }
  for (uint32_t o = 0; o < aig_num_outputs(ck->certificate); o++) {
    name = aig_output_at(ck->certificate, o, nullptr);
    if (!output_is_expected_environment_certificate(ck, name, levels)) {
      snprintf(message, cap, "unexpected certificate output '%s'", name);
      free(levels);
      return false;
    }
  }
  *levels_out = levels;
  return true;

missing_levels:
  free(levels);
missing:
  snprintf(message, cap, "certificate is missing output '%s'", generated);
  return false;
}

static bool validate_certificate_interface(Checker *ck, uint32_t **levels_out,
                                           char *message, size_t cap) {
  if (ck->environment)
    return validate_environment_certificate_interface(ck, levels_out, message,
                                                      cap);
  const char *kind, *name;
  if (duplicate_inputs_or_outputs(ck->certificate, &kind, &name)) {
    snprintf(message, cap, "%s%s%s", kind, *name ? ": " : "", name);
    return false;
  }
  if (aig_num_latches(ck->certificate) != 0 ||
      aig_num_justice(ck->certificate) != 0 ||
      aig_num_fairness(ck->certificate) != 0) {
    snprintf(message, cap, "certificate must be a combinational AIG");
    return false;
  }
  if (aig_num_inputs(ck->certificate) != ck->nstate + ck->nin) {
    snprintf(message, cap, "certificate input arity does not match game");
    return false;
  }
  for (uint32_t j = 0; j < ck->nstate; j++) {
    char fallback[32];
    name = latch_name(ck->game, j, fallback, sizeof fallback);
    if (!has_input(ck->certificate, name)) {
      snprintf(message, cap, "certificate is missing state input '%s'", name);
      return false;
    }
  }
  for (uint32_t p = 0; p < ck->nin; p++) {
    name = aig_input_name(ck->game, p, nullptr);
    if (!has_input(ck->certificate, name)) {
      snprintf(message, cap, "certificate is missing game input '%s'", name);
      return false;
    }
  }
  if (!has_output(ck->certificate, "inv")) {
    snprintf(message, cap, "certificate is missing output 'inv'");
    return false;
  }
  uint32_t *levels = calloc(ck->ngoals, sizeof *levels);
  if (!levels) {
    snprintf(message, cap, "out of memory");
    return false;
  }
  char generated[96];
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    snprintf(generated, sizeof generated, "goal_%u", j);
    if (!has_output(ck->certificate, generated))
      goto missing;
    snprintf(generated, sizeof generated, "move_%u", j);
    if (!has_output(ck->certificate, generated))
      goto missing;
    for (;;) {
      snprintf(generated, sizeof generated, "y_%u_%u", j, levels[j]);
      if (!has_output(ck->certificate, generated))
        break;
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        snprintf(generated, sizeof generated, "x_%u_%u_%u", j, levels[j], i);
        if (!has_output(ck->certificate, generated))
          goto missing;
      }
      levels[j]++;
    }
    if (levels[j] == 0) {
      snprintf(message, cap, "certificate has no rank levels for goal %u", j);
      free(levels);
      return false;
    }
  }
  for (uint32_t o = 0; o < aig_num_outputs(ck->certificate); o++) {
    name = aig_output_at(ck->certificate, o, nullptr);
    if (!output_is_expected_certificate(ck, name, levels)) {
      snprintf(message, cap, "unexpected certificate output '%s'", name);
      free(levels);
      return false;
    }
  }
  *levels_out = levels;
  return true;

missing:
  snprintf(message, cap, "certificate is missing output '%s'", generated);
  free(levels);
  return false;
}

static uint32_t max_aig_var(const Aig *aig) {
  uint32_t maxvar = 0;
  for (uint32_t i = 0; i < aig_num_inputs(aig); i++) {
    uint32_t lit;
    aig_input_name(aig, i, &lit);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < aig_num_latches(aig); i++) {
    uint32_t lit;
    aig_latch_at(aig, i, &lit, nullptr, nullptr);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < aig_num_ands(aig); i++) {
    uint32_t lit;
    aig_and_at(aig, i, &lit, nullptr, nullptr);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  return maxvar;
}

static bool defined_literal(const bool *defined, uint32_t maxvar,
                            uint32_t lit) {
  return lit < 2 || (lit / 2 <= maxvar && defined[lit / 2]);
}

static bool validate_aig_structure(const Aig *aig, const char *kind,
                                   char *message, size_t cap) {
  uint32_t maxvar = max_aig_var(aig);
  bool *defined = calloc((size_t)maxvar + 1, sizeof *defined);
  if (!defined) {
    snprintf(message, cap, "out of memory validating %s AIG", kind);
    return false;
  }
  for (uint32_t i = 0; i < aig_num_inputs(aig); i++) {
    uint32_t lit;
    aig_input_name(aig, i, &lit);
    if (lit < 2 || lit / 2 > maxvar || defined[lit / 2]) {
      snprintf(message, cap, "malformed %s AIG input %u", kind, i);
      free(defined);
      return false;
    }
    defined[lit / 2] = true;
  }
  for (uint32_t i = 0; i < aig_num_latches(aig); i++) {
    uint32_t lit;
    aig_latch_at(aig, i, &lit, nullptr, nullptr);
    if (lit < 2 || lit / 2 > maxvar || defined[lit / 2]) {
      snprintf(message, cap, "malformed %s AIG latch %u", kind, i);
      free(defined);
      return false;
    }
    defined[lit / 2] = true;
  }
  for (uint32_t i = 0; i < aig_num_ands(aig); i++) {
    uint32_t lhs, r0, r1;
    aig_and_at(aig, i, &lhs, &r0, &r1);
    if (lhs < 2 || lhs / 2 > maxvar || defined[lhs / 2] ||
        !defined_literal(defined, maxvar, r0) ||
        !defined_literal(defined, maxvar, r1)) {
      snprintf(message, cap, "malformed %s AIG gate %u", kind, i);
      free(defined);
      return false;
    }
    defined[lhs / 2] = true;
  }
  for (uint32_t i = 0; i < aig_num_latches(aig); i++) {
    uint32_t current, next, reset;
    aig_latch_at(aig, i, &current, &next, &reset);
    if (!defined_literal(defined, maxvar, next) ||
        (reset > 1 && reset != current)) {
      snprintf(message, cap, "malformed %s AIG latch update %u", kind, i);
      free(defined);
      return false;
    }
  }
#define CHECK_LITERAL(section, index, literal)                                 \
  do {                                                                         \
    if (!defined_literal(defined, maxvar, (literal))) {                        \
      snprintf(message, cap, "malformed %s AIG %s %u", kind, section,          \
               (unsigned)(index));                                             \
      free(defined);                                                           \
      return false;                                                            \
    }                                                                          \
  } while (0)
  for (uint32_t i = 0; i < aig_num_outputs(aig); i++) {
    uint32_t lit;
    aig_output_at(aig, i, &lit);
    CHECK_LITERAL("output", i, lit);
  }
  for (uint32_t i = 0; i < aig_num_bad(aig); i++) {
    uint32_t lit;
    aig_bad_at(aig, i, &lit);
    CHECK_LITERAL("bad property", i, lit);
  }
  for (uint32_t i = 0; i < aig_num_constraints(aig); i++) {
    uint32_t lit;
    aig_constraint_at(aig, i, &lit);
    CHECK_LITERAL("constraint", i, lit);
  }
  for (uint32_t j = 0; j < aig_num_justice(aig); j++) {
    const uint32_t *lits;
    uint32_t count;
    aig_justice_at(aig, j, &lits, &count);
    for (uint32_t i = 0; i < count; i++)
      CHECK_LITERAL("justice literal", j, lits[i]);
  }
  for (uint32_t i = 0; i < aig_num_fairness(aig); i++)
    CHECK_LITERAL("fairness", i, aig_fairness_at(aig, i));
#undef CHECK_LITERAL
  free(defined);
  return true;
}

static bool compile_aig_roots(Checker *ck, const Aig *aig, const Bdd *inputs,
                              const Bdd *latches, const uint32_t *lits,
                              Bdd *roots, size_t count, const char *phase) {
  uint32_t maxvar = max_aig_var(aig);
  Bdd *map = calloc((size_t)maxvar + 1, sizeof *map);
  if (!map)
    return false;
  for (uint32_t i = 0; i < aig_num_inputs(aig); i++) {
    uint32_t lit;
    aig_input_name(aig, i, &lit);
    map[lit / 2] = oxidd_bdd_ref(inputs[i]);
  }
  for (uint32_t i = 0; i < aig_num_latches(aig); i++) {
    uint32_t lit;
    aig_latch_at(aig, i, &lit, nullptr, nullptr);
    map[lit / 2] = oxidd_bdd_ref(latches[i]);
  }
  oxidd_phase(&ck->run, phase);
  ck->requested_roots += count;
  bool ok = oxidd_build_roots(&ck->run, aig, map, maxvar, lits, roots, count);
  for (uint32_t i = 0; i <= maxvar; i++)
    oxidd_bdd_unref(map[i]);
  free(map);
  if (!ok) {
    for (size_t i = 0; i < count; i++) {
      oxidd_bdd_unref(roots[i]);
      roots[i] = (Bdd){0};
    }
    ck->bdd_failed = true;
  }
  update_peak(ck);
  return ok;
}

static int find_input(const Aig *aig, const char *name) {
  for (uint32_t i = 0; i < aig_num_inputs(aig); i++) {
    const char *candidate = aig_input_name(aig, i, nullptr);
    if (candidate && !strcmp(candidate, name))
      return (int)i;
  }
  return -1;
}

static Bdd named_root(const Aig *aig, const uint32_t *root_by_output,
                      const Bdd *roots, const char *name) {
  for (uint32_t i = 0; i < aig_num_outputs(aig); i++) {
    const char *candidate = aig_output_at(aig, i, nullptr);
    if (candidate && !strcmp(candidate, name) &&
        root_by_output[i] != UINT32_MAX)
      return oxidd_bdd_ref(roots[root_by_output[i]]);
  }
  return (Bdd){0};
}

static void compiled_free(Compiled *compiled) {
  for (size_t i = 0; i < compiled->nroots; i++)
    oxidd_bdd_unref(compiled->roots[i]);
  free(compiled->roots);
  free(compiled->root_by_output);
  *compiled = (Compiled){0};
}

static bool certificate_output_is_selected(const Checker *ck,
                                           const char *name) {
  if (!name)
    return true;
  if (!strncmp(name, "move_", 5))
    return false;
  return !ck->environment || strcmp(name, "system_winning");
}

static bool compile_certificate_outputs(Checker *ck, const Aig *aig,
                                        const Bdd *inputs, Compiled *compiled,
                                        const char *phase) {
  uint32_t noutputs = aig_num_outputs(aig);
  uint32_t *root_by_output = calloc(noutputs, sizeof *root_by_output);
  if (!root_by_output)
    return false;
  size_t count = 0;
  for (uint32_t i = 0; i < noutputs; i++) {
    const char *name = aig_output_at(aig, i, nullptr);
    if (!certificate_output_is_selected(ck, name))
      root_by_output[i] = UINT32_MAX;
    else
      root_by_output[i] = (uint32_t)count++;
  }
  uint32_t *lits = count ? calloc(count, sizeof *lits) : nullptr;
  Bdd *roots = count ? calloc(count, sizeof *roots) : nullptr;
  if (count && (!lits || !roots)) {
    free(root_by_output);
    free(lits);
    free(roots);
    return false;
  }
  for (uint32_t i = 0; i < noutputs; i++)
    if (root_by_output[i] != UINT32_MAX)
      aig_output_at(aig, i, &lits[root_by_output[i]]);
  bool ok =
      compile_aig_roots(ck, aig, inputs, nullptr, lits, roots, count, phase);
  free(lits);
  if (!ok) {
    free(root_by_output);
    free(roots);
    return false;
  }
  *compiled = (Compiled){aig, root_by_output, roots, count};
  return true;
}

static Bdd output_bdd(Checker *ck, const Aig *aig, const Compiled *compiled,
                      const char *name) {
  (void)ck;
  return named_root(aig, compiled->root_by_output, compiled->roots, name);
}

static bool compile_policy_roots(Checker *ck, int mode, bool specialized,
                                 Bdd *control, Bdd *counter_next) {
  uint32_t ninputs = aig_num_inputs(ck->policy);
  Bdd *inputs = calloc(ninputs, sizeof *inputs);
  if (!inputs)
    return false;
  bool ok = true;
  for (uint32_t p = 0; p < ninputs && ok; p++) {
    const char *name = aig_input_name(ck->policy, p, nullptr);
    bool found = false;
    for (uint32_t j = 0; j < ck->nstate && !found; j++) {
      char fallback[32];
      const char *state_name =
          latch_name(ck->game, j, fallback, sizeof fallback);
      if (!strcmp(name, state_name)) {
        inputs[p] = oxidd_bdd_ref(ck->q[j]);
        found = true;
      }
    }
    for (uint32_t j = 0; j < ck->ncounter && !found; j++) {
      char counter[64];
      snprintf(counter, sizeof counter, "curr_%u", j);
      if (!strcmp(name, counter)) {
        inputs[p] = specialized ? ((mode >= 0 && (uint32_t)mode == j)
                                       ? oxidd_bdd_true(ck->manager)
                                       : oxidd_bdd_false(ck->manager))
                                : oxidd_bdd_ref(ck->q[ck->nstate + j]);
        found = true;
      }
    }
    for (uint32_t i = 0; i < ck->nu && !ck->environment && !found; i++) {
      const char *input_name = aig_input_name(ck->game, ck->uinput[i], nullptr);
      if (!strcmp(name, input_name)) {
        inputs[p] = oxidd_bdd_ref(ck->u[i]);
        found = true;
      }
    }
    ok = found;
  }
  size_t count = (size_t)ck->npolicy_choices + ck->ncounter;
  uint32_t *lits = ok ? calloc(count, sizeof *lits) : nullptr;
  Bdd *roots = ok ? calloc(count, sizeof *roots) : nullptr;
  ok = ok && lits && roots;
  size_t root = 0;
  for (uint32_t i = 0; i < ck->npolicy_choices && ok; i++) {
    uint32_t game_input = ck->environment ? ck->uinput[i] : ck->cinput[i];
    const char *name = aig_input_name(ck->game, game_input, nullptr);
    lits[root++] = aig_output_lit(ck->policy, name);
  }
  char generated[96];
  for (uint32_t j = 0; j < ck->ncounter && ok; j++) {
    snprintf(generated, sizeof generated, "curr_next_%u", j);
    lits[root++] = aig_output_lit(ck->policy, generated);
  }
  size_t gates_before = ck->run.built_gates;
  if (ok)
    ok = compile_aig_roots(ck, ck->policy, inputs, nullptr, lits, roots, count,
                           specialized ? "checker_policy_mode"
                                       : "checker_policy");
  size_t built = ck->run.built_gates - gates_before;
  if (specialized) {
    ck->policy_mode_builds++;
    ck->policy_counter_constants += ck->ncounter;
    ck->policy_specialized_gates += built;
  } else {
    ck->policy_unspecialized_gates += built;
  }
  if (ok) {
    root = 0;
    for (uint32_t i = 0; i < ck->npolicy_choices; i++) {
      control[i] = roots[root];
      roots[root++] = (Bdd){0};
    }
    for (uint32_t j = 0; j < ck->ncounter; j++) {
      counter_next[j] = roots[root];
      roots[root++] = (Bdd){0};
    }
  }
  for (size_t i = 0; i < count; i++)
    oxidd_bdd_unref(roots ? roots[i] : (Bdd){0});
  for (uint32_t p = 0; p < ninputs; p++)
    oxidd_bdd_unref(inputs[p]);
  free(roots);
  free(lits);
  free(inputs);
  return ok;
}

static bool ensure_full_policy(Checker *ck, char *message, size_t cap) {
  if (ck->policy_curr_next)
    return true;
  ck->policy_control = ck->npolicy_choices ? calloc(ck->npolicy_choices,
                                                    sizeof *ck->policy_control)
                                           : nullptr;
  ck->policy_curr_next = calloc(ck->ncounter, sizeof *ck->policy_curr_next);
  if ((ck->npolicy_choices && !ck->policy_control) || !ck->policy_curr_next ||
      !compile_policy_roots(ck, -1, false, ck->policy_control,
                            ck->policy_curr_next)) {
    for (uint32_t i = 0; i < ck->npolicy_choices; i++)
      oxidd_bdd_unref(ck->policy_control ? ck->policy_control[i] : (Bdd){0});
    for (uint32_t j = 0; j < ck->ncounter; j++)
      oxidd_bdd_unref(ck->policy_curr_next ? ck->policy_curr_next[j]
                                           : (Bdd){0});
    free(ck->policy_control);
    free(ck->policy_curr_next);
    ck->policy_control = nullptr;
    ck->policy_curr_next = nullptr;
    snprintf(message, cap, "OxiDD capacity while compiling policy");
    return false;
  }
  return true;
}

static void bdd_replace(Bdd *slot, Bdd value) {
  oxidd_bdd_unref(*slot);
  *slot = value;
}

static bool bdd_or_into(Checker *ck, Bdd *slot, Bdd value) {
  Bdd next = oxidd_bdd_or(*slot, value);
  oxidd_bdd_unref(*slot);
  *slot = next;
  if (bdd_invalid(next))
    ck->bdd_failed = true;
  return !bdd_invalid(next);
}

static bool bdd_and_into(Checker *ck, Bdd *slot, Bdd value) {
  Bdd next = oxidd_bdd_and(*slot, value);
  oxidd_bdd_unref(*slot);
  *slot = next;
  if (bdd_invalid(next))
    ck->bdd_failed = true;
  return !bdd_invalid(next);
}

static bool checked_bdd_eq(Checker *ck, Bdd left, Bdd right) {
  Bdd equality = oxidd_bdd_equiv(left, right);
  if (bdd_invalid(equality)) {
    ck->bdd_failed = true;
    return false;
  }
  bool result = oxidd_bdd_valid(equality);
  oxidd_bdd_unref(equality);
  return result;
}

static bool checked_satisfiable(Checker *ck, Bdd value) {
  if (bdd_invalid(value)) {
    ck->bdd_failed = true;
    return false;
  }
  return oxidd_bdd_satisfiable(value);
}

static bool setup_bdds(Checker *ck, const uint32_t *levels, char *message,
                       size_t cap) {
  ck->nq = ck->nstate + ck->ncounter;
  ck->nvars = 2 * ck->nq + ck->nu + ck->nc;
  ck->manager =
      oxidd_bdd_manager_new(ck->options.node_cap, ck->options.node_cap, 1);
  if (!ck->manager._p) {
    snprintf(message, cap, "cannot create OxiDD manager");
    return false;
  }
  oxidd_bdd_manager_add_vars(ck->manager, ck->nvars);
  ck->bdd_options = oxidd_solve_options_default();
  ck->bdd_options.node_cap = ck->options.node_cap;
  ck->bdd_options.cache_cap = ck->options.node_cap;
  ck->bdd_options.failure = &ck->failure;
  oxidd_run_init(&ck->run, ck->manager, &ck->bdd_options, ck->options.node_cap,
                 ck->options.node_cap);
  ck->run_initialized = true;

  ck->qvar = calloc(ck->nq, sizeof *ck->qvar);
  ck->qpvar = calloc(ck->nq, sizeof *ck->qpvar);
  ck->uvar = ck->nu ? calloc(ck->nu, sizeof *ck->uvar) : nullptr;
  ck->cvar = ck->nc ? calloc(ck->nc, sizeof *ck->cvar) : nullptr;
  ck->q = calloc(ck->nq, sizeof *ck->q);
  ck->qp = calloc(ck->nq, sizeof *ck->qp);
  ck->u = ck->nu ? calloc(ck->nu, sizeof *ck->u) : nullptr;
  ck->c = ck->nc ? calloc(ck->nc, sizeof *ck->c) : nullptr;
  if (!ck->qvar || !ck->qpvar || !ck->q || !ck->qp ||
      (ck->nu && (!ck->uvar || !ck->u)) || (ck->nc && (!ck->cvar || !ck->c))) {
    snprintf(message, cap, "out of memory");
    return false;
  }
  for (uint32_t i = 0; i < ck->nq; i++) {
    ck->qvar[i] = 2 * i;
    ck->qpvar[i] = 2 * i + 1;
    ck->q[i] = oxidd_bdd_var(ck->manager, ck->qvar[i]);
    ck->qp[i] = oxidd_bdd_var(ck->manager, ck->qpvar[i]);
  }
  for (uint32_t i = 0; i < ck->nu; i++) {
    ck->uvar[i] = 2 * ck->nq + i;
    ck->u[i] = oxidd_bdd_var(ck->manager, ck->uvar[i]);
  }
  for (uint32_t i = 0; i < ck->nc; i++) {
    ck->cvar[i] = 2 * ck->nq + ck->nu + i;
    ck->c[i] = oxidd_bdd_var(ck->manager, ck->cvar[i]);
  }

  // Compile the sampled game over current state and independent u/c letters.
  Bdd *game_inputs = ck->nin ? calloc(ck->nin, sizeof *game_inputs) : nullptr;
  if (ck->nin && !game_inputs) {
    snprintf(message, cap, "out of memory");
    return false;
  }
  uint32_t ui = 0, ci = 0;
  for (uint32_t p = 0; p < ck->nin; p++)
    game_inputs[p] = is_controllable(aig_input_name(ck->game, p, nullptr))
                         ? ck->c[ci++]
                         : ck->u[ui++];
  uint32_t nbad = aig_num_bad(ck->game)
                      ? aig_num_bad(ck->game)
                      : (aig_num_outputs(ck->game) == 1 ? 1u : 0u);
  size_t game_root_count = (size_t)ck->nstate + nbad + ck->ngoals + ck->nfair;
  uint32_t *game_lits = calloc(game_root_count, sizeof *game_lits);
  Bdd *game_roots = calloc(game_root_count, sizeof *game_roots);
  if (!game_lits || !game_roots) {
    free(game_inputs);
    free(game_lits);
    free(game_roots);
    snprintf(message, cap, "out of memory");
    return false;
  }
  size_t root = 0;
  for (uint32_t j = 0; j < ck->nstate; j++)
    aig_latch_at(ck->game, j, nullptr, &game_lits[root++], nullptr);
  if (aig_num_bad(ck->game))
    for (uint32_t i = 0; i < nbad; i++)
      aig_bad_at(ck->game, i, &game_lits[root++]);
  else if (nbad)
    aig_output_at(ck->game, 0, &game_lits[root++]);
  for (uint32_t record = 0; record < aig_num_justice(ck->game); record++) {
    const uint32_t *lits;
    uint32_t count;
    aig_justice_at(ck->game, record, &lits, &count);
    if (!count)
      game_lits[root++] = AIG_TRUE;
    else
      for (uint32_t k = 0; k < count; k++)
        game_lits[root++] = lits[k];
  }
  for (uint32_t i = 0; i < ck->nfair; i++)
    game_lits[root++] = aig_fairness_at(ck->game, i);
  if (root != game_root_count ||
      !compile_aig_roots(ck, ck->game, game_inputs, ck->q, game_lits,
                         game_roots, game_root_count, "checker_game")) {
    free(game_inputs);
    free(game_lits);
    free(game_roots);
    snprintf(message, cap, "OxiDD capacity while compiling game");
    return false;
  }
  free(game_inputs);
  free(game_lits);
  ck->game_next = calloc(ck->nstate, sizeof *ck->game_next);
  ck->goal = calloc(ck->ngoals, sizeof *ck->goal);
  ck->fair = ck->nfair ? calloc(ck->nfair, sizeof *ck->fair) : nullptr;
  if (!ck->game_next || !ck->goal || (ck->nfair && !ck->fair)) {
    for (size_t i = 0; i < game_root_count; i++)
      oxidd_bdd_unref(game_roots[i]);
    free(game_roots);
    snprintf(message, cap, "out of memory");
    return false;
  }
  root = 0;
  for (uint32_t j = 0; j < ck->nstate; j++) {
    ck->game_next[j] = game_roots[root];
    game_roots[root++] = (Bdd){0};
  }
  ck->game_bad = oxidd_bdd_false(ck->manager);
  if (aig_num_bad(ck->game) > 0 || aig_num_outputs(ck->game) != 1) {
    // AIGER 1.9 bad-state properties are authoritative.  With none present,
    // zero or multiple ordinary outputs describe a pure-justice model.
    for (uint32_t i = 0; i < aig_num_bad(ck->game); i++) {
      Bdd bad = game_roots[root++];
      bool ok = bdd_or_into(ck, &ck->game_bad, bad);
      oxidd_bdd_unref(bad);
      game_roots[root - 1] = (Bdd){0};
      if (!ok) {
        for (size_t k = 0; k < game_root_count; k++)
          oxidd_bdd_unref(game_roots[k]);
        free(game_roots);
        snprintf(message, cap, "OxiDD capacity while compiling game safety");
        return false;
      }
    }
  } else {
    // Backward-compatible tlsf-tools dialect: one ordinary output is unsafe.
    bdd_replace(&ck->game_bad, game_roots[root]);
    game_roots[root++] = (Bdd){0};
  }
  uint32_t goal_index = 0;
  for (uint32_t record = 0; record < aig_num_justice(ck->game); record++) {
    const uint32_t *lits;
    uint32_t n;
    aig_justice_at(ck->game, record, &lits, &n);
    uint32_t count = n ? n : 1;
    for (uint32_t k = 0; k < count; k++) {
      ck->goal[goal_index++] = game_roots[root];
      game_roots[root++] = (Bdd){0};
    }
  }
  for (uint32_t i = 0; i < ck->nfair; i++) {
    ck->fair[i] = game_roots[root];
    game_roots[root++] = (Bdd){0};
  }
  free(game_roots);

  ck->npolicy_choices = ck->environment ? ck->nu : ck->nc;
  bool need_full_policy =
      ck->options.method == METHOD_CLOSED_LOOP ||
      ck->options.method == METHOD_BOTH ||
      (ck->options.method == METHOD_AUTO && !ck->certificate) ||
      ck->options.test_unspecialized_policy;
  if (need_full_policy && !ensure_full_policy(ck, message, cap))
    return false;
  char generated[96];

  // Certificate predicates are compiled over independent state/u/c variables.
  // A closed-loop-only request still validates the supplied certificate above,
  // but does not construct any of its Boolean functions.  Fixed-policy proofs
  // validate move_* names structurally without using them as proof premises.
  bool need_certificate =
      ck->certificate && ck->options.method != METHOD_CLOSED_LOOP;
  if (need_certificate) {
    Bdd *cert_inputs =
        calloc(aig_num_inputs(ck->certificate), sizeof *cert_inputs);
    if (!cert_inputs) {
      snprintf(message, cap, "out of memory");
      return false;
    }
    for (uint32_t p = 0; p < aig_num_inputs(ck->certificate); p++) {
      const char *name = aig_input_name(ck->certificate, p, nullptr);
      int game_index = find_input(ck->game, name);
      if (game_index >= 0) {
        uint32_t uindex = 0, cindex = 0;
        for (int q = 0; q <= game_index; q++) {
          if (is_controllable(aig_input_name(ck->game, (uint32_t)q, nullptr)))
            cindex++;
          else
            uindex++;
        }
        cert_inputs[p] =
            is_controllable(name) ? ck->c[cindex - 1] : ck->u[uindex - 1];
        continue;
      }
      for (uint32_t j = 0; j < ck->nstate; j++) {
        char fallback[32];
        const char *state_name =
            latch_name(ck->game, j, fallback, sizeof fallback);
        if (!strcmp(name, state_name)) {
          cert_inputs[p] = ck->q[j];
          break;
        }
      }
    }
    Compiled cert_compiled = {0};
    if (!compile_certificate_outputs(ck, ck->certificate, cert_inputs,
                                     &cert_compiled, "checker_certificate")) {
      free(cert_inputs);
      snprintf(message, cap, "OxiDD capacity while compiling certificate");
      return false;
    }
    free(cert_inputs);
    ck->cert_inv = output_bdd(ck, ck->certificate, &cert_compiled, "inv");
    ck->cert_goal = calloc(ck->ngoals, sizeof *ck->cert_goal);
    if (!ck->cert_goal) {
      compiled_free(&cert_compiled);
      snprintf(message, cap, "out of memory");
      return false;
    }
    if (ck->environment) {
      ck->cert_fair =
          ck->nfair ? calloc(ck->nfair, sizeof *ck->cert_fair) : nullptr;
      ck->ndual_levels = levels[0];
      ck->dual_rank = calloc(ck->ndual_levels, sizeof *ck->dual_rank);
      if ((ck->nfair && !ck->cert_fair) || !ck->dual_rank) {
        compiled_free(&cert_compiled);
        snprintf(message, cap, "out of memory");
        return false;
      }
      for (uint32_t i = 0; i < ck->nfair; i++) {
        snprintf(generated, sizeof generated, "fair_%u", i);
        ck->cert_fair[i] =
            output_bdd(ck, ck->certificate, &cert_compiled, generated);
      }
      for (uint32_t k = 0; k < ck->ndual_levels; k++) {
        snprintf(generated, sizeof generated, "z_%u", k);
        ck->dual_rank[k].z =
            output_bdd(ck, ck->certificate, &cert_compiled, generated);
        ck->dual_rank[k].y = calloc(ck->ngoals, sizeof(Bdd));
        ck->dual_rank[k].inner = calloc((size_t)ck->ngoals * ck->nfair_disj,
                                        sizeof *ck->dual_rank[k].inner);
        if (!ck->dual_rank[k].y || !ck->dual_rank[k].inner) {
          compiled_free(&cert_compiled);
          snprintf(message, cap, "out of memory");
          return false;
        }
        for (uint32_t j = 0; j < ck->ngoals; j++) {
          snprintf(generated, sizeof generated, "y_%u_%u", k, j);
          ck->dual_rank[k].y[j] =
              output_bdd(ck, ck->certificate, &cert_compiled, generated);
          for (uint32_t i = 0; i < ck->nfair_disj; i++) {
            size_t rank_index = (size_t)j * ck->nfair_disj + i;
            size_t level_index =
                1 + ((size_t)k * ck->ngoals + j) * ck->nfair_disj + i;
            DualInnerRank *inner = &ck->dual_rank[k].inner[rank_index];
            inner->levels = levels[level_index];
            inner->x = calloc(inner->levels, sizeof *inner->x);
            if (!inner->x) {
              compiled_free(&cert_compiled);
              snprintf(message, cap, "out of memory");
              return false;
            }
            for (uint32_t l = 0; l < inner->levels; l++) {
              snprintf(generated, sizeof generated, "x_%u_%u_%u_%u", k, j, i,
                       l);
              inner->x[l] =
                  output_bdd(ck, ck->certificate, &cert_compiled, generated);
            }
          }
        }
      }
    } else {
      ck->rank = calloc(ck->ngoals, sizeof *ck->rank);
      if (!ck->rank) {
        compiled_free(&cert_compiled);
        snprintf(message, cap, "out of memory");
        return false;
      }
      for (uint32_t j = 0; j < ck->ngoals; j++) {
        ck->rank[j].levels = levels[j];
        ck->rank[j].y = calloc(levels[j], sizeof(Bdd));
        ck->rank[j].x = calloc(levels[j], sizeof(Bdd *));
        if (!ck->rank[j].y || !ck->rank[j].x) {
          compiled_free(&cert_compiled);
          snprintf(message, cap, "out of memory");
          return false;
        }
        for (uint32_t k = 0; k < levels[j]; k++) {
          snprintf(generated, sizeof generated, "y_%u_%u", j, k);
          ck->rank[j].y[k] =
              output_bdd(ck, ck->certificate, &cert_compiled, generated);
          ck->rank[j].x[k] = calloc(ck->nfair_disj, sizeof(Bdd));
          if (!ck->rank[j].x[k]) {
            compiled_free(&cert_compiled);
            snprintf(message, cap, "out of memory");
            return false;
          }
          for (uint32_t i = 0; i < ck->nfair_disj; i++) {
            snprintf(generated, sizeof generated, "x_%u_%u_%u", j, k, i);
            ck->rank[j].x[k][i] =
                output_bdd(ck, ck->certificate, &cert_compiled, generated);
          }
        }
      }
    }
    // goal_j is deliberately not trusted.  check_certificate_mode compares it
    // with the game's flattened justice as a semantic proof condition before
    // using the game predicate in every obligation.
    for (uint32_t j = 0; j < ck->ngoals; j++) {
      snprintf(generated, sizeof generated, "goal_%u", j);
      ck->cert_goal[j] =
          output_bdd(ck, ck->certificate, &cert_compiled, generated);
    }
    compiled_free(&cert_compiled);
  }

  uint32_t *input_vars =
      (ck->nu + ck->nc) ? calloc(ck->nu + ck->nc, sizeof *input_vars) : nullptr;
  if (ck->nu + ck->nc && !input_vars) {
    snprintf(message, cap, "out of memory");
    return false;
  }
  memcpy(input_vars, ck->uvar, ck->nu * sizeof *input_vars);
  memcpy(input_vars + ck->nu, ck->cvar, ck->nc * sizeof *input_vars);
  ck->input_cube = cube_of(ck->manager, input_vars, ck->nu + ck->nc);
  free(input_vars);
  // The generic game functions still contain independent controllables.  The
  // certificate checker installs the policy after specializing the counter;
  // the closed-loop path installs the unspecialized policy once below.
  update_peak(ck);
  return true;
}

static Bdd assignment_cube(Checker *ck, int counter) {
  Bdd cube = oxidd_bdd_true(ck->manager);
  for (uint32_t j = 0; j < ck->ncounter; j++) {
    Bdd literal = (counter >= 0 && (uint32_t)counter == j)
                      ? oxidd_bdd_ref(ck->q[ck->nstate + j])
                      : oxidd_bdd_not(ck->q[ck->nstate + j]);
    Bdd next = oxidd_bdd_and(cube, literal);
    oxidd_bdd_unref(cube);
    oxidd_bdd_unref(literal);
    cube = next;
  }
  return cube;
}

static Bdd specialize(Bdd value, Bdd cube) {
  return oxidd_bdd_restrict(value, cube);
}

static oxidd_bdd_substitution_t *control_substitution(Checker *ck,
                                                      const Bdd *control) {
  oxidd_bdd_substitution_t *sub = oxidd_bdd_substitution_new(ck->nc);
  if (!sub)
    return nullptr;
  for (uint32_t i = 0; i < ck->nc; i++)
    oxidd_bdd_substitution_add_pair(sub, ck->cvar[i], control[i]);
  return sub;
}

static Bdd substitute_controls(Bdd value, oxidd_bdd_substitution_t *sub) {
  return sub ? oxidd_bdd_substitute(value, sub) : oxidd_bdd_ref(value);
}

static oxidd_bdd_substitution_t *state_substitution(Checker *ck,
                                                    const Bdd *next_state) {
  oxidd_bdd_substitution_t *sub = oxidd_bdd_substitution_new(ck->nstate);
  if (!sub)
    return nullptr;
  ck->successor_substitutions++;
  for (uint32_t j = 0; j < ck->nstate; j++)
    oxidd_bdd_substitution_add_pair(sub, ck->qvar[j], next_state[j]);
  return sub;
}

static Bdd successor(Checker *ck, Bdd state_predicate, const Bdd *next_state,
                     const oxidd_bdd_substitution_t *mode_substitution) {
  oxidd_bdd_substitution_t *local = nullptr;
  if (!mode_substitution) {
    local = state_substitution(ck, next_state);
    if (!local)
      return (Bdd){0};
    mode_substitution = local;
  }
  ck->successor_applications++;
  Bdd result = oxidd_bdd_substitute(state_predicate, mode_substitution);
  oxidd_bdd_substitution_free(local);
  if (bdd_invalid(result))
    ck->bdd_failed = true;
  return result;
}

typedef struct {
  oxidd_bdd_substitution_t *substitution;
  Bdd goal_and_inv;
  Bdd *fair;
  uint32_t nfair;
  Bdd *lower;
  uint32_t nlower;
} SuccessorCache;

static void successor_cache_clear(SuccessorCache *cache) {
  if (!cache)
    return;
  oxidd_bdd_substitution_free(cache->substitution);
  if (!bdd_invalid(cache->goal_and_inv))
    oxidd_bdd_unref(cache->goal_and_inv);
  if (cache->fair)
    for (uint32_t i = 0; i < cache->nfair; i++)
      if (!bdd_invalid(cache->fair[i]))
        oxidd_bdd_unref(cache->fair[i]);
  if (cache->lower)
    for (uint32_t k = 0; k < cache->nlower; k++)
      if (!bdd_invalid(cache->lower[k]))
        oxidd_bdd_unref(cache->lower[k]);
  free(cache->fair);
  free(cache->lower);
  *cache = (SuccessorCache){0};
}

static void counterexample_clear(Counterexample *counterexample) {
  if (!counterexample)
    return;
  free(counterexample->state);
  free(counterexample->curr);
  free(counterexample->inputs);
  free(counterexample->control);
  *counterexample = (Counterexample){0};
}

static bool assignment_value(oxidd_assignment_t assignment, uint32_t var) {
  return var < assignment.len && assignment.data[var] > 0;
}

static void capture_counterexample(Checker *ck, const char *reason,
                                   oxidd_assignment_t assignment,
                                   const Bdd *control,
                                   const oxidd_var_no_bool_pair_t *args,
                                   size_t nargs) {
  Counterexample *counterexample = ck->current_counterexample;
  if (!counterexample)
    return;
  counterexample_clear(counterexample);
  counterexample->state = ck->nstate ? calloc(ck->nstate, 1) : nullptr;
  counterexample->curr = ck->ncounter ? calloc(ck->ncounter, 1) : nullptr;
  counterexample->inputs = ck->nu ? calloc(ck->nu, 1) : nullptr;
  counterexample->control = control && ck->nc ? calloc(ck->nc, 1) : nullptr;
  if ((ck->nstate && !counterexample->state) ||
      (ck->ncounter && !counterexample->curr) ||
      (ck->nu && !counterexample->inputs) ||
      (control && ck->nc && !counterexample->control)) {
    counterexample_clear(counterexample);
    return;
  }
  counterexample->present = true;
  counterexample->has_control = control != nullptr;
  snprintf(counterexample->reason, sizeof counterexample->reason, "%s", reason);
  for (uint32_t j = 0; j < ck->nstate; j++)
    counterexample->state[j] = assignment_value(assignment, ck->qvar[j]);
  for (uint32_t j = 0; j < ck->ncounter; j++)
    counterexample->curr[j] =
        assignment_value(assignment, ck->qvar[ck->nstate + j]);
  for (uint32_t i = 0; i < ck->nu; i++)
    counterexample->inputs[i] = assignment_value(assignment, ck->uvar[i]);
  if (control)
    for (uint32_t i = 0; i < ck->nc; i++)
      counterexample->control[i] =
          oxidd_bdd_eval(control[i], args, nargs) ? 1 : 0;
}

static void print_counterexample(Checker *ck, const char *reason, Bdd witness,
                                 const Bdd *control) {
  printf("COUNTEREXAMPLE reason=%s\n", reason);
  oxidd_assignment_t assignment = oxidd_bdd_pick_cube(witness);
  if (!assignment.data)
    return;
  oxidd_var_no_bool_pair_t *args = calloc(ck->nvars, sizeof *args);
  size_t nargs = 0;
  if (args)
    for (uint32_t v = 0; v < ck->nvars; v++)
      if (v < assignment.len && assignment.data[v] >= 0) {
        args[nargs].var = v;
        args[nargs++].val = assignment.data[v] != 0;
      }
  capture_counterexample(ck, reason, assignment, control, args, nargs);
  fputs("  state", stdout);
  for (uint32_t j = 0; j < ck->nstate; j++) {
    char fallback[32];
    const char *name = latch_name(ck->game, j, fallback, sizeof fallback);
    int value =
        ck->qvar[j] < assignment.len ? assignment.data[ck->qvar[j]] : -1;
    printf(" %s=%c", name, value > 0 ? '1' : '0');
  }
  fputs("\n  curr", stdout);
  for (uint32_t j = 0; j < ck->ncounter; j++) {
    uint32_t var = ck->qvar[ck->nstate + j];
    int value = var < assignment.len ? assignment.data[var] : -1;
    printf(" curr_%u=%c", j, value > 0 ? '1' : '0');
  }
  fputs("\n  inputs", stdout);
  for (uint32_t i = 0; i < ck->nu; i++) {
    int value =
        ck->uvar[i] < assignment.len ? assignment.data[ck->uvar[i]] : -1;
    printf(" %s=%c", aig_input_name(ck->game, ck->uinput[i], nullptr),
           value > 0 ? '1' : '0');
  }
  if (control && args) {
    fputs("\n  outputs", stdout);
    for (uint32_t i = 0; i < ck->nc; i++)
      printf(" %s=%u", aig_input_name(ck->game, ck->cinput[i], nullptr),
             oxidd_bdd_eval(control[i], args, nargs) ? 1u : 0u);
  }
  fputc('\n', stdout);
  free(args);
  oxidd_assignment_free(assignment);
}

static CheckResult check_state_only(Checker *ck, Bdd predicate,
                                    const char *reason) {
  Bdd universal = oxidd_bdd_forall(predicate, ck->input_cube);
  if (bdd_invalid(universal)) {
    ck->bdd_failed = true;
    return CHECK_UNKNOWN;
  }
  Bdd dependence = oxidd_bdd_xor(predicate, universal);
  oxidd_bdd_unref(universal);
  if (checked_satisfiable(ck, dependence)) {
    print_counterexample(ck, reason, dependence, nullptr);
    oxidd_bdd_unref(dependence);
    return CHECK_CERT_FAILED;
  }
  oxidd_bdd_unref(dependence);
  return ck->bdd_failed ? CHECK_UNKNOWN : CHECK_VERIFIED;
}

static CheckResult validate_certificate_predicates(Checker *ck) {
  CheckResult state_only =
      check_state_only(ck, ck->cert_inv, "certificate inv is not state-only");
  if (state_only != CHECK_VERIFIED)
    return state_only;
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    Bdd previous = oxidd_bdd_false(ck->manager);
    for (uint32_t k = 0; k < ck->rank[j].levels; k++) {
      Bdd union_x = oxidd_bdd_false(ck->manager);
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        Bdd x = ck->rank[j].x[k][i];
        char reason[128];
        snprintf(reason, sizeof reason,
                 "certificate x_%u_%u_%u is not state-only", j, k, i);
        state_only = check_state_only(ck, x, reason);
        if (state_only != CHECK_VERIFIED) {
          oxidd_bdd_unref(union_x);
          oxidd_bdd_unref(previous);
          return state_only;
        }
        if (!bdd_or_into(ck, &union_x, x)) {
          oxidd_bdd_unref(previous);
          return CHECK_UNKNOWN;
        }
      }
      char reason[128];
      snprintf(reason, sizeof reason, "certificate y_%u_%u is not state-only",
               j, k);
      state_only = check_state_only(ck, ck->rank[j].y[k], reason);
      if (state_only != CHECK_VERIFIED) {
        oxidd_bdd_unref(union_x);
        oxidd_bdd_unref(previous);
        return state_only;
      }
      Bdd union_mismatch = oxidd_bdd_xor(union_x, ck->rank[j].y[k]);
      if (checked_satisfiable(ck, union_mismatch)) {
        snprintf(reason, sizeof reason,
                 "y_%u_%u is not the union of its X levels", j, k);
        print_counterexample(ck, reason, union_mismatch, nullptr);
        oxidd_bdd_unref(union_mismatch);
        oxidd_bdd_unref(union_x);
        oxidd_bdd_unref(previous);
        return CHECK_CERT_FAILED;
      }
      oxidd_bdd_unref(union_mismatch);
      if (ck->bdd_failed) {
        oxidd_bdd_unref(union_x);
        oxidd_bdd_unref(previous);
        return CHECK_UNKNOWN;
      }
      Bdd not_current = oxidd_bdd_not(ck->rank[j].y[k]);
      Bdd nonmonotone = oxidd_bdd_and(previous, not_current);
      oxidd_bdd_unref(not_current);
      if (checked_satisfiable(ck, nonmonotone)) {
        Bdd counter = assignment_cube(ck, (int)j);
        Bdd concrete = oxidd_bdd_and(nonmonotone, counter);
        print_counterexample(ck, "rank levels are not monotone", concrete,
                             nullptr);
        oxidd_bdd_unref(concrete);
        oxidd_bdd_unref(counter);
        oxidd_bdd_unref(nonmonotone);
        oxidd_bdd_unref(union_x);
        oxidd_bdd_unref(previous);
        return CHECK_CERT_FAILED;
      }
      oxidd_bdd_unref(nonmonotone);
      if (ck->bdd_failed) {
        oxidd_bdd_unref(union_x);
        oxidd_bdd_unref(previous);
        return CHECK_UNKNOWN;
      }
      oxidd_bdd_unref(previous);
      previous = union_x;
    }
    oxidd_bdd_unref(previous);
  }
  return CHECK_VERIFIED;
}

static bool reset_in_predicate(Checker *ck, Bdd predicate) {
  oxidd_var_no_bool_pair_t *args =
      ck->nstate ? calloc(ck->nstate, sizeof *args) : nullptr;
  if (ck->nstate && !args) {
    ck->bdd_failed = true;
    return false;
  }
  for (uint32_t j = 0; j < ck->nstate; j++) {
    uint32_t reset;
    aig_latch_at(ck->game, j, nullptr, nullptr, &reset);
    args[j].var = ck->qvar[j];
    args[j].val = reset != 0;
  }
  bool result = oxidd_bdd_eval(predicate, args, ck->nstate);
  free(args);
  return result;
}

static oxidd_bdd_substitution_t *
environment_substitution(Checker *ck, const Bdd *environment) {
  oxidd_bdd_substitution_t *sub = oxidd_bdd_substitution_new(ck->nu);
  if (!sub)
    return nullptr;
  for (uint32_t i = 0; i < ck->nu; i++)
    oxidd_bdd_substitution_add_pair(sub, ck->uvar[i], environment[i]);
  return sub;
}

static CheckResult validate_environment_certificate_predicates(Checker *ck) {
  CheckResult result =
      check_state_only(ck, ck->cert_inv, "environment inv is not state-only");
  if (result != CHECK_VERIFIED)
    return result;
  for (uint32_t k = 0; k < ck->ndual_levels; k++) {
    char reason[128];
    snprintf(reason, sizeof reason, "certificate z_%u is not state-only", k);
    result = check_state_only(ck, ck->dual_rank[k].z, reason);
    if (result != CHECK_VERIFIED)
      return result;
    Bdd union_y = oxidd_bdd_false(ck->manager);
    for (uint32_t j = 0; j < ck->ngoals; j++) {
      snprintf(reason, sizeof reason, "certificate y_%u_%u is not state-only",
               k, j);
      result = check_state_only(ck, ck->dual_rank[k].y[j], reason);
      if (result != CHECK_VERIFIED) {
        oxidd_bdd_unref(union_y);
        return result;
      }
      bdd_or_into(ck, &union_y, ck->dual_rank[k].y[j]);
      Bdd intersection = oxidd_bdd_true(ck->manager);
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        DualInnerRank *inner =
            &ck->dual_rank[k].inner[(size_t)j * ck->nfair_disj + i];
        Bdd previous = oxidd_bdd_false(ck->manager);
        for (uint32_t l = 0; l < inner->levels; l++) {
          snprintf(reason, sizeof reason,
                   "certificate x_%u_%u_%u_%u is not state-only", k, j, i, l);
          result = check_state_only(ck, inner->x[l], reason);
          if (result != CHECK_VERIFIED) {
            oxidd_bdd_unref(previous);
            oxidd_bdd_unref(intersection);
            oxidd_bdd_unref(union_y);
            return result;
          }
          Bdd not_current = oxidd_bdd_not(inner->x[l]);
          Bdd nonmonotone = oxidd_bdd_and(previous, not_current);
          oxidd_bdd_unref(not_current);
          if (checked_satisfiable(ck, nonmonotone)) {
            print_counterexample(ck, "dual inner rank is not monotone",
                                 nonmonotone, nullptr);
            oxidd_bdd_unref(nonmonotone);
            oxidd_bdd_unref(previous);
            oxidd_bdd_unref(intersection);
            oxidd_bdd_unref(union_y);
            return CHECK_CERT_FAILED;
          }
          oxidd_bdd_unref(nonmonotone);
          oxidd_bdd_unref(previous);
          previous = oxidd_bdd_ref(inner->x[l]);
        }
        bdd_and_into(ck, &intersection, previous);
        oxidd_bdd_unref(previous);
      }
      Bdd mismatch = oxidd_bdd_xor(intersection, ck->dual_rank[k].y[j]);
      oxidd_bdd_unref(intersection);
      if (checked_satisfiable(ck, mismatch)) {
        print_counterexample(ck, "dual Y is not the intersection of final X",
                             mismatch, nullptr);
        oxidd_bdd_unref(mismatch);
        oxidd_bdd_unref(union_y);
        return CHECK_CERT_FAILED;
      }
      oxidd_bdd_unref(mismatch);
    }
    Bdd mismatch = oxidd_bdd_xor(union_y, ck->dual_rank[k].z);
    oxidd_bdd_unref(union_y);
    if (checked_satisfiable(ck, mismatch)) {
      print_counterexample(ck, "dual Z is not the union of its Y regions",
                           mismatch, nullptr);
      oxidd_bdd_unref(mismatch);
      return CHECK_CERT_FAILED;
    }
    oxidd_bdd_unref(mismatch);
    if (k) {
      Bdd not_current = oxidd_bdd_not(ck->dual_rank[k].z);
      Bdd nonmonotone = oxidd_bdd_and(ck->dual_rank[k - 1].z, not_current);
      oxidd_bdd_unref(not_current);
      if (checked_satisfiable(ck, nonmonotone)) {
        print_counterexample(ck, "dual outer rank is not monotone", nonmonotone,
                             nullptr);
        oxidd_bdd_unref(nonmonotone);
        return CHECK_CERT_FAILED;
      }
      oxidd_bdd_unref(nonmonotone);
    }
  }
  Bdd region_mismatch =
      oxidd_bdd_xor(ck->cert_inv, ck->dual_rank[ck->ndual_levels - 1].z);
  if (checked_satisfiable(ck, region_mismatch)) {
    print_counterexample(ck, "environment inv differs from final dual Z",
                         region_mismatch, nullptr);
    oxidd_bdd_unref(region_mismatch);
    return CHECK_CERT_FAILED;
  }
  oxidd_bdd_unref(region_mismatch);
  return ck->bdd_failed ? CHECK_UNKNOWN : CHECK_VERIFIED;
}

static CheckResult check_environment_certificate_mode(Checker *ck) {
  CheckResult shape = validate_environment_certificate_predicates(ck);
  if (shape != CHECK_VERIFIED)
    return shape;
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    Bdd mismatch = oxidd_bdd_xor(ck->cert_goal[j], ck->goal[j]);
    if (checked_satisfiable(ck, mismatch)) {
      print_counterexample(ck, "certificate goal differs from game justice",
                           mismatch, nullptr);
      oxidd_bdd_unref(mismatch);
      return CHECK_CERT_FAILED;
    }
    oxidd_bdd_unref(mismatch);
  }
  for (uint32_t i = 0; i < ck->nfair; i++) {
    Bdd mismatch = oxidd_bdd_xor(ck->cert_fair[i], ck->fair[i]);
    if (checked_satisfiable(ck, mismatch)) {
      print_counterexample(ck,
                           "certificate fairness differs from game fairness",
                           mismatch, nullptr);
      oxidd_bdd_unref(mismatch);
      return CHECK_CERT_FAILED;
    }
    oxidd_bdd_unref(mismatch);
  }
  if (!reset_in_predicate(ck, ck->cert_inv)) {
    if (ck->bdd_failed)
      return CHECK_UNKNOWN;
    Bdd reset = initial_cube(ck);
    print_counterexample(ck, "reset state is outside environment inv", reset,
                         nullptr);
    oxidd_bdd_unref(reset);
    return CHECK_CERT_FAILED;
  }

  for (int mode = -1; mode < (int)ck->nfair_disj; mode++) {
    uint32_t current = mode < 0 ? 0u : (uint32_t)mode;
    uint32_t advanced = (current + 1) % ck->nfair_disj;
    Bdd counter_cube = assignment_cube(ck, mode);
    Bdd *environment = ck->nu ? calloc(ck->nu, sizeof *environment) : nullptr;
    Bdd *counter_next = calloc(ck->nfair_disj, sizeof *counter_next);
    Bdd *next_state = calloc(ck->nstate, sizeof *next_state);
    oxidd_bdd_substitution_t *mode_substitution = nullptr;
    Bdd bad = {0};
    if ((ck->nu && !environment) || !counter_next || !next_state) {
      oxidd_bdd_unref(counter_cube);
      free(environment);
      free(counter_next);
      free(next_state);
      return CHECK_UNKNOWN;
    }
    if (ck->options.test_unspecialized_policy) {
      for (uint32_t i = 0; i < ck->nu; i++)
        environment[i] = specialize(ck->policy_control[i], counter_cube);
      for (uint32_t i = 0; i < ck->nfair_disj; i++)
        counter_next[i] = specialize(ck->policy_curr_next[i], counter_cube);
    } else if (!compile_policy_roots(ck, mode, true, environment,
                                     counter_next)) {
      oxidd_bdd_unref(counter_cube);
      free(environment);
      free(counter_next);
      free(next_state);
      return CHECK_UNKNOWN;
    }
    oxidd_bdd_substitution_t *usub = environment_substitution(ck, environment);
    if (ck->nu && !usub)
      goto environment_unknown;
    bad = usub ? oxidd_bdd_substitute(ck->game_bad, usub)
               : oxidd_bdd_ref(ck->game_bad);
    for (uint32_t s = 0; s < ck->nstate; s++)
      next_state[s] = usub ? oxidd_bdd_substitute(ck->game_next[s], usub)
                           : oxidd_bdd_ref(ck->game_next[s]);
    if (usub)
      oxidd_bdd_substitution_free(usub);
    if (!ck->options.test_rebuild_successor) {
      mode_substitution = state_substitution(ck, next_state);
      if (!mode_substitution)
        goto environment_unknown;
    }
    Bdd fair_current = ck->nfair ? oxidd_bdd_ref(ck->fair[current])
                                 : oxidd_bdd_true(ck->manager);
    Bdd violation = oxidd_bdd_false(ck->manager);

    for (uint32_t q = 0; q < ck->nfair_disj; q++) {
      Bdd expected;
      if (current == advanced && q == current) {
        expected = oxidd_bdd_true(ck->manager);
      } else if (q == current) {
        expected = oxidd_bdd_not(fair_current);
      } else if (q == advanced) {
        expected = oxidd_bdd_ref(fair_current);
      } else {
        expected = oxidd_bdd_false(ck->manager);
      }
      Bdd differs = oxidd_bdd_xor(counter_next[q], expected);
      Bdd relevant = oxidd_bdd_and(ck->cert_inv, differs);
      bdd_or_into(ck, &violation, relevant);
      oxidd_bdd_unref(expected);
      oxidd_bdd_unref(differs);
      oxidd_bdd_unref(relevant);
    }

    for (uint32_t branch = 0; branch < 2; branch++) {
      if (current == advanced && branch == 1)
        continue;
      uint32_t phase = branch ? advanced : current;
      Bdd guard = current == advanced ? oxidd_bdd_true(ck->manager)
                                      : (branch ? oxidd_bdd_ref(fair_current)
                                                : oxidd_bdd_not(fair_current));
      Bdd previous_z = oxidd_bdd_false(ck->manager);
      for (uint32_t k = 0; k < ck->ndual_levels; k++) {
        Bdd not_previous_z = oxidd_bdd_not(previous_z);
        Bdd outer_layer = oxidd_bdd_and(ck->dual_rank[k].z, not_previous_z);
        oxidd_bdd_unref(not_previous_z);
        Bdd previous_y = oxidd_bdd_false(ck->manager);
        for (uint32_t j = 0; j < ck->ngoals; j++) {
          Bdd not_previous_y = oxidd_bdd_not(previous_y);
          Bdd selected0 = oxidd_bdd_and(outer_layer, ck->dual_rank[k].y[j]);
          Bdd selected = oxidd_bdd_and(selected0, not_previous_y);
          oxidd_bdd_unref(selected0);
          oxidd_bdd_unref(not_previous_y);
          DualInnerRank *inner =
              &ck->dual_rank[k].inner[(size_t)j * ck->nfair_disj + phase];
          Bdd previous_x = oxidd_bdd_false(ck->manager);
          for (uint32_t l = 0; l < inner->levels; l++) {
            Bdd not_previous_x = oxidd_bdd_not(previous_x);
            Bdd inner_layer0 = oxidd_bdd_and(inner->x[l], not_previous_x);
            Bdd inner_layer = oxidd_bdd_and(selected, inner_layer0);
            Bdd guarded_layer = oxidd_bdd_and(guard, inner_layer);
            oxidd_bdd_unref(not_previous_x);
            oxidd_bdd_unref(inner_layer0);
            oxidd_bdd_unref(inner_layer);

            Bdd not_goal = oxidd_bdd_not(ck->goal[j]);
            Bdd outer_progress = oxidd_bdd_or(previous_z, not_goal);
            oxidd_bdd_unref(not_goal);
            Bdd base = oxidd_bdd_and(outer_progress, ck->dual_rank[k].y[j]);
            oxidd_bdd_unref(outer_progress);
            Bdd phase_fair = ck->nfair ? oxidd_bdd_ref(ck->fair[phase])
                                       : oxidd_bdd_true(ck->manager);
            Bdd inner_progress = l ? oxidd_bdd_or(inner->x[l - 1], phase_fair)
                                   : oxidd_bdd_ref(phase_fair);
            oxidd_bdd_unref(phase_fair);
            Bdd target = oxidd_bdd_and(base, inner_progress);
            oxidd_bdd_unref(base);
            oxidd_bdd_unref(inner_progress);
            Bdd allowed = successor(ck, target, next_state, mode_substitution);
            oxidd_bdd_unref(target);
            bdd_or_into(ck, &allowed, bad);
            Bdd not_allowed = oxidd_bdd_not(allowed);
            Bdd failed = oxidd_bdd_and(guarded_layer, not_allowed);
            bdd_or_into(ck, &violation, failed);
            oxidd_bdd_unref(not_allowed);
            oxidd_bdd_unref(failed);
            oxidd_bdd_unref(allowed);
            oxidd_bdd_unref(guarded_layer);
            oxidd_bdd_unref(previous_x);
            previous_x = oxidd_bdd_ref(inner->x[l]);
          }
          oxidd_bdd_unref(previous_x);
          oxidd_bdd_unref(selected);
          Bdd more_y = oxidd_bdd_or(previous_y, ck->dual_rank[k].y[j]);
          oxidd_bdd_unref(previous_y);
          previous_y = more_y;
        }
        oxidd_bdd_unref(previous_y);
        oxidd_bdd_unref(outer_layer);
        oxidd_bdd_unref(previous_z);
        previous_z = oxidd_bdd_ref(ck->dual_rank[k].z);
      }
      oxidd_bdd_unref(previous_z);
      oxidd_bdd_unref(guard);
    }
    oxidd_bdd_unref(fair_current);
    if (checked_satisfiable(ck, violation)) {
      Bdd concrete = oxidd_bdd_and(violation, counter_cube);
      print_counterexample(ck, "dual one-step certificate obligation", concrete,
                           nullptr);
      oxidd_bdd_unref(concrete);
      oxidd_bdd_unref(violation);
      oxidd_bdd_unref(bad);
      goto environment_failed;
    }
    oxidd_bdd_unref(violation);
    oxidd_bdd_unref(bad);
    for (uint32_t i = 0; i < ck->nu; i++)
      oxidd_bdd_unref(environment[i]);
    for (uint32_t i = 0; i < ck->nfair_disj; i++)
      oxidd_bdd_unref(counter_next[i]);
    for (uint32_t s = 0; s < ck->nstate; s++)
      oxidd_bdd_unref(next_state[s]);
    oxidd_bdd_substitution_free(mode_substitution);
    oxidd_bdd_unref(counter_cube);
    free(environment);
    free(counter_next);
    free(next_state);
    if (ck->bdd_failed)
      return CHECK_UNKNOWN;
    continue;

  environment_failed:
    for (uint32_t i = 0; i < ck->nu; i++)
      oxidd_bdd_unref(environment[i]);
    for (uint32_t i = 0; i < ck->nfair_disj; i++)
      oxidd_bdd_unref(counter_next[i]);
    for (uint32_t s = 0; s < ck->nstate; s++)
      oxidd_bdd_unref(next_state[s]);
    oxidd_bdd_substitution_free(mode_substitution);
    oxidd_bdd_unref(counter_cube);
    free(environment);
    free(counter_next);
    free(next_state);
    return CHECK_CERT_FAILED;

  environment_unknown:
    for (uint32_t i = 0; i < ck->nu; i++)
      oxidd_bdd_unref(environment[i]);
    for (uint32_t i = 0; i < ck->nfair_disj; i++)
      oxidd_bdd_unref(counter_next[i]);
    for (uint32_t s = 0; s < ck->nstate; s++)
      if (!bdd_invalid(next_state[s]))
        oxidd_bdd_unref(next_state[s]);
    if (!bdd_invalid(bad))
      oxidd_bdd_unref(bad);
    oxidd_bdd_substitution_free(mode_substitution);
    oxidd_bdd_unref(counter_cube);
    free(environment);
    free(counter_next);
    free(next_state);
    return CHECK_UNKNOWN;
  }
  return CHECK_VERIFIED;
}

static CheckResult check_certificate_mode(Checker *ck) {
  if (ck->environment)
    return check_environment_certificate_mode(ck);
  CheckResult shape = validate_certificate_predicates(ck);
  if (shape != CHECK_VERIFIED)
    return shape;
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    Bdd mismatch = oxidd_bdd_xor(ck->cert_goal[j], ck->goal[j]);
    if (checked_satisfiable(ck, mismatch)) {
      char reason[128];
      snprintf(reason, sizeof reason,
               "certificate goal_%u differs from game justice", j);
      Bdd counter = assignment_cube(ck, (int)j);
      Bdd concrete = oxidd_bdd_and(mismatch, counter);
      print_counterexample(ck, reason, concrete, nullptr);
      oxidd_bdd_unref(concrete);
      oxidd_bdd_unref(counter);
      oxidd_bdd_unref(mismatch);
      return CHECK_CERT_FAILED;
    }
    oxidd_bdd_unref(mismatch);
    if (ck->bdd_failed)
      return CHECK_UNKNOWN;
  }
  if (!reset_in_predicate(ck, ck->cert_inv)) {
    if (ck->bdd_failed)
      return CHECK_UNKNOWN;
    Bdd reset = oxidd_bdd_true(ck->manager);
    for (uint32_t j = 0; j < ck->nstate; j++) {
      uint32_t value;
      aig_latch_at(ck->game, j, nullptr, nullptr, &value);
      Bdd lit = value ? oxidd_bdd_ref(ck->q[j]) : oxidd_bdd_not(ck->q[j]);
      bdd_and_into(ck, &reset, lit);
      oxidd_bdd_unref(lit);
    }
    Bdd counter = assignment_cube(ck, -1);
    bdd_and_into(ck, &reset, counter);
    oxidd_bdd_unref(counter);
    print_counterexample(ck, "reset state is outside inv", reset, nullptr);
    oxidd_bdd_unref(reset);
    return CHECK_CERT_FAILED;
  }

  for (uint32_t j = 0; j < ck->ngoals; j++) {
    Bdd covered = oxidd_bdd_false(ck->manager);
    for (uint32_t k = 0; k < ck->rank[j].levels; k++)
      for (uint32_t i = 0; i < ck->nfair_disj; i++)
        if (!bdd_or_into(ck, &covered, ck->rank[j].x[k][i])) {
          oxidd_bdd_unref(covered);
          return CHECK_UNKNOWN;
        }
    Bdd not_covered = oxidd_bdd_not(covered);
    Bdd missing = oxidd_bdd_and(ck->cert_inv, not_covered);
    oxidd_bdd_unref(not_covered);
    oxidd_bdd_unref(covered);
    if (checked_satisfiable(ck, missing)) {
      Bdd counter = assignment_cube(ck, (int)j);
      Bdd concrete = oxidd_bdd_and(missing, counter);
      print_counterexample(ck, "invariant state has no rank", concrete,
                           nullptr);
      oxidd_bdd_unref(concrete);
      oxidd_bdd_unref(counter);
      oxidd_bdd_unref(missing);
      return CHECK_CERT_FAILED;
    }
    oxidd_bdd_unref(missing);
    if (ck->bdd_failed)
      return CHECK_UNKNOWN;
  }

  // Check every one-hot counter mode and the all-zero reset convention.  The
  // all-zero mode is semantically goal 0 but may select different policy gates,
  // so it is checked independently rather than assumed equivalent to curr_0.
  for (int mode = -1; mode < (int)ck->ngoals; mode++) {
    uint32_t goal = mode < 0 ? 0u : (uint32_t)mode;
    Bdd counter_cube = assignment_cube(ck, mode);
    Bdd *control = ck->nc ? calloc(ck->nc, sizeof *control) : nullptr;
    Bdd *counter_next = calloc(ck->ngoals, sizeof *counter_next);
    Bdd *next_state = calloc(ck->nstate, sizeof *next_state);
    SuccessorCache successors = {0};
    Bdd bad = {0};
    Bdd next_inv = {0};
    if ((ck->nc && !control) || !counter_next || !next_state) {
      oxidd_bdd_unref(counter_cube);
      free(control);
      free(counter_next);
      free(next_state);
      return CHECK_UNKNOWN;
    }
    if (ck->options.test_unspecialized_policy) {
      for (uint32_t i = 0; i < ck->nc; i++)
        control[i] = specialize(ck->policy_control[i], counter_cube);
      for (uint32_t j = 0; j < ck->ngoals; j++)
        counter_next[j] = specialize(ck->policy_curr_next[j], counter_cube);
    } else if (!compile_policy_roots(ck, mode, true, control, counter_next)) {
      oxidd_bdd_unref(counter_cube);
      free(control);
      free(counter_next);
      free(next_state);
      return CHECK_UNKNOWN;
    }
    oxidd_bdd_substitution_t *csub = control_substitution(ck, control);
    if (ck->nc && !csub) {
      for (uint32_t i = 0; i < ck->nc; i++)
        oxidd_bdd_unref(control[i]);
      for (uint32_t j = 0; j < ck->ngoals; j++)
        oxidd_bdd_unref(counter_next[j]);
      oxidd_bdd_unref(counter_cube);
      free(control);
      free(counter_next);
      free(next_state);
      return CHECK_UNKNOWN;
    }
    bad = substitute_controls(ck->game_bad, csub);
    for (uint32_t s = 0; s < ck->nstate; s++)
      next_state[s] = substitute_controls(ck->game_next[s], csub);
    oxidd_bdd_substitution_free(csub);
    if (!ck->options.test_rebuild_successor) {
      successors.substitution = state_substitution(ck, next_state);
      if (!successors.substitution)
        goto mode_unknown;
    }
    if (!ck->options.test_rebuild_successor && ck->nfair) {
      successors.nfair = ck->nfair_disj;
      successors.fair = calloc(successors.nfair, sizeof *successors.fair);
      if (!successors.fair)
        goto mode_unknown;
    }
    uint32_t levels = ck->rank[goal].levels;
    if (!ck->options.test_rebuild_successor && levels > 1) {
      successors.nlower = levels - 1;
      successors.lower = calloc(successors.nlower, sizeof *successors.lower);
      if (!successors.lower)
        goto mode_unknown;
    }
    next_inv = successor(ck, ck->cert_inv, next_state, successors.substitution);
    if (!ck->options.test_rebuild_successor) {
      successors.goal_and_inv =
          successor(ck, ck->goal[goal], next_state, successors.substitution);
      bdd_and_into(ck, &successors.goal_and_inv, next_inv);
    }
    Bdd violation = oxidd_bdd_and(ck->cert_inv, bad);
    Bdd not_next_inv = oxidd_bdd_not(next_inv);
    Bdd leaves = oxidd_bdd_and(ck->cert_inv, not_next_inv);
    bdd_or_into(ck, &violation, leaves);
    oxidd_bdd_unref(not_next_inv);
    oxidd_bdd_unref(leaves);

    // The policy format fixes the counter update, not just its one-hotness.
    for (uint32_t q = 0; q < ck->ngoals; q++) {
      Bdd expected;
      uint32_t next_goal = (goal + 1) % ck->ngoals;
      if (q == goal && q == next_goal)
        expected = oxidd_bdd_true(ck->manager);
      else if (q == goal)
        expected = oxidd_bdd_not(ck->goal[goal]);
      else if (q == next_goal)
        expected = oxidd_bdd_ref(ck->goal[goal]);
      else
        expected = oxidd_bdd_false(ck->manager);
      Bdd differs = oxidd_bdd_xor(counter_next[q], expected);
      Bdd relevant = oxidd_bdd_and(ck->cert_inv, differs);
      bdd_or_into(ck, &violation, relevant);
      oxidd_bdd_unref(expected);
      oxidd_bdd_unref(differs);
      oxidd_bdd_unref(relevant);
    }

    Bdd at_goal = oxidd_bdd_and(ck->cert_inv, ck->goal[goal]);
    Bdd ranked = oxidd_bdd_ref(at_goal);
    for (uint32_t k = 0; k < ck->rank[goal].levels; k++) {
      for (uint32_t i = 0; i < ck->nfair_disj; i++) {
        Bdd not_ranked = oxidd_bdd_not(ranked);
        Bdd layer0 = oxidd_bdd_and(ck->rank[goal].x[k][i], not_ranked);
        Bdd layer = oxidd_bdd_and(ck->cert_inv, layer0);
        oxidd_bdd_unref(not_ranked);
        oxidd_bdd_unref(layer0);

        Bdd allowed = successor(ck, ck->rank[goal].x[k][i], next_state,
                                successors.substitution);
        if (ck->nfair) {
          Bdd fair_next;
          if (ck->options.test_rebuild_successor) {
            fair_next = successor(ck, ck->fair[i], next_state, nullptr);
          } else {
            if (bdd_invalid(successors.fair[i]))
              successors.fair[i] = successor(ck, ck->fair[i], next_state,
                                             successors.substitution);
            fair_next = successors.fair[i];
          }
          Bdd not_fair_next = oxidd_bdd_not(fair_next);
          bdd_and_into(ck, &allowed, not_fair_next);
          if (ck->options.test_rebuild_successor)
            oxidd_bdd_unref(fair_next);
          oxidd_bdd_unref(not_fair_next);
        } else {
          Bdd no_escape = oxidd_bdd_false(ck->manager);
          bdd_replace(&allowed, no_escape);
        }
        if (ck->options.test_rebuild_successor) {
          Bdd goal_and_inv = successor(ck, ck->goal[goal], next_state, nullptr);
          bdd_and_into(ck, &goal_and_inv, next_inv);
          bdd_or_into(ck, &allowed, goal_and_inv);
          oxidd_bdd_unref(goal_and_inv);
        } else {
          bdd_or_into(ck, &allowed, successors.goal_and_inv);
        }
        if (k > 0) {
          Bdd lower_next;
          if (ck->options.test_rebuild_successor) {
            lower_next =
                successor(ck, ck->rank[goal].y[k - 1], next_state, nullptr);
          } else {
            if (bdd_invalid(successors.lower[k - 1]))
              successors.lower[k - 1] =
                  successor(ck, ck->rank[goal].y[k - 1], next_state,
                            successors.substitution);
            lower_next = successors.lower[k - 1];
          }
          bdd_or_into(ck, &allowed, lower_next);
          if (ck->options.test_rebuild_successor)
            oxidd_bdd_unref(lower_next);
        }
        Bdd not_allowed = oxidd_bdd_not(allowed);
        Bdd progress_bad = oxidd_bdd_and(layer, not_allowed);
        bdd_or_into(ck, &violation, progress_bad);
        oxidd_bdd_unref(not_allowed);
        oxidd_bdd_unref(progress_bad);
        oxidd_bdd_unref(allowed);
        oxidd_bdd_unref(layer);
        bdd_or_into(ck, &ranked, ck->rank[goal].x[k][i]);
      }
    }
    oxidd_bdd_unref(ranked);
    oxidd_bdd_unref(at_goal);
    if (ck->bdd_failed || bdd_invalid(violation)) {
      oxidd_bdd_unref(violation);
      goto mode_unknown;
    }
    if (checked_satisfiable(ck, violation)) {
      Bdd concrete = oxidd_bdd_and(violation, counter_cube);
      print_counterexample(ck, "one-step certificate obligation", concrete,
                           control);
      oxidd_bdd_unref(concrete);
      oxidd_bdd_unref(violation);
      for (uint32_t i = 0; i < ck->nc; i++)
        oxidd_bdd_unref(control[i]);
      for (uint32_t q = 0; q < ck->ngoals; q++)
        oxidd_bdd_unref(counter_next[q]);
      for (uint32_t s = 0; s < ck->nstate; s++)
        oxidd_bdd_unref(next_state[s]);
      oxidd_bdd_unref(bad);
      oxidd_bdd_unref(next_inv);
      successor_cache_clear(&successors);
      oxidd_bdd_unref(counter_cube);
      free(control);
      free(counter_next);
      free(next_state);
      return CHECK_CERT_FAILED;
    }
    if (ck->bdd_failed) {
      oxidd_bdd_unref(violation);
      goto mode_unknown;
    }
    oxidd_bdd_unref(violation);
    for (uint32_t i = 0; i < ck->nc; i++)
      oxidd_bdd_unref(control[i]);
    for (uint32_t q = 0; q < ck->ngoals; q++)
      oxidd_bdd_unref(counter_next[q]);
    for (uint32_t s = 0; s < ck->nstate; s++)
      oxidd_bdd_unref(next_state[s]);
    oxidd_bdd_unref(bad);
    oxidd_bdd_unref(next_inv);
    successor_cache_clear(&successors);
    oxidd_bdd_unref(counter_cube);
    free(control);
    free(counter_next);
    free(next_state);
    update_peak(ck);
    if (timed_out(ck))
      return CHECK_UNKNOWN;
    continue;

  mode_unknown:
    for (uint32_t i = 0; i < ck->nc; i++)
      oxidd_bdd_unref(control[i]);
    for (uint32_t q = 0; q < ck->ngoals; q++)
      oxidd_bdd_unref(counter_next[q]);
    for (uint32_t s = 0; s < ck->nstate; s++)
      oxidd_bdd_unref(next_state[s]);
    if (!bdd_invalid(bad))
      oxidd_bdd_unref(bad);
    if (!bdd_invalid(next_inv))
      oxidd_bdd_unref(next_inv);
    successor_cache_clear(&successors);
    oxidd_bdd_unref(counter_cube);
    free(control);
    free(counter_next);
    free(next_state);
    return CHECK_UNKNOWN;
  }
  return CHECK_VERIFIED;
}

static Bdd initial_cube(Checker *ck) {
  Bdd initial = oxidd_bdd_true(ck->manager);
  for (uint32_t s = 0; s < ck->nstate; s++) {
    uint32_t reset;
    aig_latch_at(ck->game, s, nullptr, nullptr, &reset);
    Bdd literal = reset ? oxidd_bdd_ref(ck->q[s]) : oxidd_bdd_not(ck->q[s]);
    bdd_and_into(ck, &initial, literal);
    oxidd_bdd_unref(literal);
  }
  for (uint32_t j = 0; j < ck->ncounter; j++) {
    Bdd literal = oxidd_bdd_not(ck->q[ck->nstate + j]);
    bdd_and_into(ck, &initial, literal);
    oxidd_bdd_unref(literal);
  }
  return initial;
}

static bool build_closed_loop(Checker *ck, Bdd **next_out, Bdd *bad_out) {
  oxidd_bdd_substitution_t *csub = control_substitution(ck, ck->policy_control);
  if (ck->nc && !csub)
    return false;
  Bdd *next = calloc(ck->nq, sizeof *next);
  if (!next) {
    oxidd_bdd_substitution_free(csub);
    return false;
  }
  for (uint32_t s = 0; s < ck->nstate; s++)
    next[s] = substitute_controls(ck->game_next[s], csub);
  for (uint32_t j = 0; j < ck->ngoals; j++)
    next[ck->nstate + j] = oxidd_bdd_ref(ck->policy_curr_next[j]);
  *bad_out = substitute_controls(ck->game_bad, csub);
  oxidd_bdd_substitution_free(csub);
  for (uint32_t q = 0; q < ck->nq; q++)
    if (bdd_invalid(next[q])) {
      for (uint32_t i = 0; i < ck->nq; i++)
        oxidd_bdd_unref(next[i]);
      free(next);
      oxidd_bdd_unref(*bad_out);
      ck->bdd_failed = true;
      return false;
    }
  *next_out = next;
  return !bdd_invalid(*bad_out);
}

static Bdd pre_exists(Checker *ck, Bdd target, const Bdd *next, Bdd unc_cube) {
  oxidd_bdd_substitution_t *sub = oxidd_bdd_substitution_new(ck->nq);
  if (!sub)
    return (Bdd){0};
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_substitution_add_pair(sub, ck->qvar[q], next[q]);
  Bdd image = oxidd_bdd_substitute(target, sub);
  oxidd_bdd_substitution_free(sub);
  Bdd result = oxidd_bdd_exists(image, unc_cube);
  oxidd_bdd_unref(image);
  return result;
}

static Bdd build_relation(Checker *ck, const Bdd *next) {
  Bdd relation = oxidd_bdd_true(ck->manager);
  for (uint32_t q = 0; q < ck->nq; q++) {
    Bdd equality = oxidd_bdd_equiv(ck->qp[q], next[q]);
    if (!bdd_and_into(ck, &relation, equality)) {
      oxidd_bdd_unref(equality);
      break;
    }
    oxidd_bdd_unref(equality);
  }
  return relation;
}

static Bdd post_image(Checker *ck, Bdd states, Bdd relation, Bdd quantify,
                      oxidd_bdd_substitution_t *prime_to_current) {
  Bdd joined = oxidd_bdd_and(states, relation);
  Bdd projected = oxidd_bdd_exists(joined, quantify);
  oxidd_bdd_unref(joined);
  Bdd result = oxidd_bdd_substitute(projected, prime_to_current);
  oxidd_bdd_unref(projected);
  return result;
}

static Bdd pre_exists_safe(Checker *ck, Bdd target, const Bdd *next, Bdd bad,
                           Bdd control_cube) {
  oxidd_bdd_substitution_t *sub = oxidd_bdd_substitution_new(ck->nq);
  if (!sub)
    return (Bdd){0};
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_substitution_add_pair(sub, ck->qvar[q], next[q]);
  Bdd image = oxidd_bdd_substitute(target, sub);
  oxidd_bdd_substitution_free(sub);
  Bdd not_bad = oxidd_bdd_not(bad);
  Bdd safe_image = oxidd_bdd_and(not_bad, image);
  oxidd_bdd_unref(not_bad);
  oxidd_bdd_unref(image);
  Bdd result = oxidd_bdd_exists(safe_image, control_cube);
  oxidd_bdd_unref(safe_image);
  return result;
}

static CheckResult check_environment_closed_loop_mode(Checker *ck) {
  oxidd_bdd_substitution_t *usub =
      environment_substitution(ck, ck->policy_control);
  if (ck->nu && !usub)
    return CHECK_UNKNOWN;
  Bdd *next = calloc(ck->nq, sizeof *next);
  if (!next) {
    oxidd_bdd_substitution_free(usub);
    return CHECK_UNKNOWN;
  }
  for (uint32_t s = 0; s < ck->nstate; s++)
    next[s] = usub ? oxidd_bdd_substitute(ck->game_next[s], usub)
                   : oxidd_bdd_ref(ck->game_next[s]);
  for (uint32_t i = 0; i < ck->ncounter; i++)
    next[ck->nstate + i] = oxidd_bdd_ref(ck->policy_curr_next[i]);
  Bdd bad = usub ? oxidd_bdd_substitute(ck->game_bad, usub)
                 : oxidd_bdd_ref(ck->game_bad);
  if (usub)
    oxidd_bdd_substitution_free(usub);

  Bdd relation = build_relation(ck, next);
  Bdd not_bad = oxidd_bdd_not(bad);
  bdd_and_into(ck, &relation, not_bad);
  oxidd_bdd_unref(not_bad);
  uint32_t *quant_vars = calloc((size_t)ck->nq + ck->nc, sizeof *quant_vars);
  if (!quant_vars)
    goto unknown;
  memcpy(quant_vars, ck->qvar, ck->nq * sizeof *quant_vars);
  memcpy(quant_vars + ck->nq, ck->cvar, ck->nc * sizeof *quant_vars);
  Bdd quantify = cube_of(ck->manager, quant_vars, ck->nq + ck->nc);
  free(quant_vars);
  Bdd control_cube = cube_of(ck->manager, ck->cvar, ck->nc);
  oxidd_bdd_substitution_t *rename = oxidd_bdd_substitution_new(ck->nq);
  if (!rename)
    goto unknown_with_cubes;
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_substitution_add_pair(rename, ck->qpvar[q], ck->q[q]);

  Bdd reachable = initial_cube(ck);
  for (;;) {
    Bdd post = post_image(ck, reachable, relation, quantify, rename);
    Bdd expanded = oxidd_bdd_or(reachable, post);
    oxidd_bdd_unref(post);
    bool done = checked_bdd_eq(ck, expanded, reachable);
    oxidd_bdd_unref(reachable);
    reachable = expanded;
    if (done || ck->bdd_failed || timed_out(ck))
      break;
  }
  if (ck->bdd_failed || timed_out(ck))
    goto unknown_reachable;

  // A safe infinite path that eventually avoids one fairness assumption
  // satisfies the original implication vacuously and refutes the purported
  // environment counter-strategy.
  for (uint32_t i = 0; i < ck->nfair; i++) {
    Bdd not_fair = oxidd_bdd_not(ck->fair[i]);
    Bdd allowed = oxidd_bdd_and(reachable, not_fair);
    oxidd_bdd_unref(not_fair);
    Bdd z = oxidd_bdd_ref(allowed);
    for (;;) {
      Bdd pre = pre_exists_safe(ck, z, next, bad, control_cube);
      Bdd next_z = oxidd_bdd_and(allowed, pre);
      oxidd_bdd_unref(pre);
      bool done = checked_bdd_eq(ck, next_z, z);
      oxidd_bdd_unref(z);
      z = next_z;
      if (done || ck->bdd_failed || timed_out(ck))
        break;
    }
    oxidd_bdd_unref(allowed);
    if (ck->bdd_failed || timed_out(ck)) {
      oxidd_bdd_unref(z);
      goto unknown_reachable;
    }
    if (checked_satisfiable(ck, z)) {
      print_counterexample(ck, "safe cycle violates environment fairness", z,
                           nullptr);
      oxidd_bdd_unref(z);
      goto refuted;
    }
    oxidd_bdd_unref(z);
  }

  // Otherwise the system refutes the counter-strategy exactly when it has a
  // safe generalized-Buchi path visiting every fairness and every justice set.
  Bdd z = oxidd_bdd_ref(reachable);
  for (;;) {
    Bdd new_z = oxidd_bdd_ref(reachable);
    uint32_t acceptance_count = ck->nfair + ck->ngoals;
    for (uint32_t a = 0; a < acceptance_count; a++) {
      Bdd acceptance = a < ck->nfair ? oxidd_bdd_ref(ck->fair[a])
                                     : oxidd_bdd_ref(ck->goal[a - ck->nfair]);
      Bdd y = oxidd_bdd_false(ck->manager);
      for (;;) {
        Bdd pre_z = pre_exists_safe(ck, z, next, bad, control_cube);
        Bdd hit = oxidd_bdd_and(acceptance, pre_z);
        Bdd pre_y = pre_exists_safe(ck, y, next, bad, control_cube);
        Bdd next_y = oxidd_bdd_or(hit, pre_y);
        bdd_and_into(ck, &next_y, reachable);
        oxidd_bdd_unref(pre_z);
        oxidd_bdd_unref(hit);
        oxidd_bdd_unref(pre_y);
        bool done = checked_bdd_eq(ck, next_y, y);
        oxidd_bdd_unref(y);
        y = next_y;
        if (done || ck->bdd_failed || timed_out(ck))
          break;
      }
      oxidd_bdd_unref(acceptance);
      if (ck->bdd_failed || timed_out(ck)) {
        oxidd_bdd_unref(y);
        oxidd_bdd_unref(new_z);
        oxidd_bdd_unref(z);
        goto unknown_reachable;
      }
      bdd_and_into(ck, &new_z, y);
      oxidd_bdd_unref(y);
    }
    bool done = checked_bdd_eq(ck, new_z, z);
    oxidd_bdd_unref(z);
    z = new_z;
    if (done || ck->bdd_failed || timed_out(ck))
      break;
  }
  if (ck->bdd_failed || timed_out(ck)) {
    oxidd_bdd_unref(z);
    goto unknown_reachable;
  }
  if (checked_satisfiable(ck, z)) {
    print_counterexample(ck, "safe fair cycle satisfies every justice", z,
                         nullptr);
    oxidd_bdd_unref(z);
    goto refuted;
  }
  oxidd_bdd_unref(z);

  oxidd_bdd_unref(reachable);
  oxidd_bdd_substitution_free(rename);
  oxidd_bdd_unref(control_cube);
  oxidd_bdd_unref(quantify);
  oxidd_bdd_unref(relation);
  oxidd_bdd_unref(bad);
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return CHECK_VERIFIED;

refuted:
  oxidd_bdd_unref(reachable);
  oxidd_bdd_substitution_free(rename);
  oxidd_bdd_unref(control_cube);
  oxidd_bdd_unref(quantify);
  oxidd_bdd_unref(relation);
  oxidd_bdd_unref(bad);
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return CHECK_REFUTED;

unknown_reachable:
  oxidd_bdd_unref(reachable);
  oxidd_bdd_substitution_free(rename);
unknown_with_cubes:
  oxidd_bdd_unref(control_cube);
  oxidd_bdd_unref(quantify);
unknown:
  oxidd_bdd_unref(relation);
  oxidd_bdd_unref(bad);
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return CHECK_UNKNOWN;
}

static CheckResult check_closed_loop_mode(Checker *ck) {
  if (ck->environment)
    return check_environment_closed_loop_mode(ck);
  Bdd *next = nullptr;
  Bdd bad = {0};
  if (!build_closed_loop(ck, &next, &bad))
    return CHECK_UNKNOWN;
  uint32_t *unc_vars = ck->nu ? calloc(ck->nu, sizeof *unc_vars) : nullptr;
  if (ck->nu && !unc_vars)
    goto unknown;
  memcpy(unc_vars, ck->uvar, ck->nu * sizeof *unc_vars);
  Bdd unc_cube = cube_of(ck->manager, unc_vars, ck->nu);
  free(unc_vars);
  Bdd relation = build_relation(ck, next);
  uint32_t *quant_vars = calloc(ck->nq + ck->nu, sizeof *quant_vars);
  if (!quant_vars)
    goto unknown_with_unc;
  memcpy(quant_vars, ck->qvar, ck->nq * sizeof *quant_vars);
  memcpy(quant_vars + ck->nq, ck->uvar, ck->nu * sizeof *quant_vars);
  Bdd quantify = cube_of(ck->manager, quant_vars, ck->nq + ck->nu);
  free(quant_vars);
  oxidd_bdd_substitution_t *rename = oxidd_bdd_substitution_new(ck->nq);
  if (!rename)
    goto unknown_with_relation;
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_substitution_add_pair(rename, ck->qpvar[q], ck->q[q]);

  Bdd reachable = initial_cube(ck);
  for (;;) {
    Bdd post = post_image(ck, reachable, relation, quantify, rename);
    Bdd expanded = oxidd_bdd_or(reachable, post);
    oxidd_bdd_unref(post);
    if (bdd_invalid(expanded)) {
      oxidd_bdd_unref(reachable);
      reachable = expanded;
      ck->bdd_failed = true;
      break;
    }
    bool done = checked_bdd_eq(ck, expanded, reachable);
    oxidd_bdd_unref(reachable);
    reachable = expanded;
    update_peak(ck);
    if (done || timed_out(ck) || ck->bdd_failed)
      break;
  }
  if (bdd_invalid(reachable) || timed_out(ck) || ck->bdd_failed)
    goto unknown_reachable;

  Bdd safety_bad = oxidd_bdd_and(reachable, bad);
  if (checked_satisfiable(ck, safety_bad)) {
    print_counterexample(ck, "reachable bad transition", safety_bad,
                         ck->policy_control);
    oxidd_bdd_unref(safety_bad);
    goto refuted;
  }
  oxidd_bdd_unref(safety_bad);
  if (ck->bdd_failed)
    goto unknown_reachable;
  for (uint32_t goal = 0; goal < ck->ngoals; goal++) {
    Bdd not_goal = oxidd_bdd_not(ck->goal[goal]);
    Bdd allowed = oxidd_bdd_and(reachable, not_goal);
    oxidd_bdd_unref(not_goal);
    Bdd z = oxidd_bdd_ref(allowed);
    for (;;) {
      Bdd new_z = oxidd_bdd_ref(allowed);
      for (uint32_t fi = 0; fi < ck->nfair_disj; fi++) {
        Bdd fair = ck->nfair ? oxidd_bdd_ref(ck->fair[fi])
                             : oxidd_bdd_true(ck->manager);
        Bdd y = oxidd_bdd_false(ck->manager);
        for (;;) {
          Bdd pre_z = pre_exists(ck, z, next, unc_cube);
          Bdd hit = oxidd_bdd_and(fair, pre_z);
          Bdd pre_y = pre_exists(ck, y, next, unc_cube);
          Bdd next_y = oxidd_bdd_or(hit, pre_y);
          bdd_and_into(ck, &next_y, allowed);
          oxidd_bdd_unref(pre_z);
          oxidd_bdd_unref(hit);
          oxidd_bdd_unref(pre_y);
          if (bdd_invalid(next_y)) {
            oxidd_bdd_unref(y);
            y = next_y;
            ck->bdd_failed = true;
            break;
          }
          bool done = checked_bdd_eq(ck, next_y, y);
          oxidd_bdd_unref(y);
          y = next_y;
          if (done || timed_out(ck) || ck->bdd_failed)
            break;
        }
        oxidd_bdd_unref(fair);
        if (bdd_invalid(y) || timed_out(ck) || ck->bdd_failed) {
          oxidd_bdd_unref(y);
          oxidd_bdd_unref(new_z);
          oxidd_bdd_unref(z);
          oxidd_bdd_unref(allowed);
          goto unknown_reachable;
        }
        bdd_and_into(ck, &new_z, y);
        oxidd_bdd_unref(y);
      }
      bool done = checked_bdd_eq(ck, new_z, z);
      oxidd_bdd_unref(z);
      z = new_z;
      update_peak(ck);
      if (done || timed_out(ck) || ck->bdd_failed)
        break;
    }
    oxidd_bdd_unref(allowed);
    if (timed_out(ck) || ck->bdd_failed) {
      oxidd_bdd_unref(z);
      goto unknown_reachable;
    }
    if (checked_satisfiable(ck, z)) {
      print_counterexample(ck, "reachable fair cycle misses justice", z,
                           ck->policy_control);
      printf("  lasso=symbolic fair-cycle witness (goal=%u)\n", goal);
      oxidd_bdd_unref(z);
      goto refuted;
    }
    oxidd_bdd_unref(z);
    if (ck->bdd_failed)
      goto unknown_reachable;
  }

  oxidd_bdd_unref(reachable);
  oxidd_bdd_substitution_free(rename);
  oxidd_bdd_unref(quantify);
  oxidd_bdd_unref(relation);
  oxidd_bdd_unref(unc_cube);
  oxidd_bdd_unref(bad);
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return CHECK_VERIFIED;

refuted:
  oxidd_bdd_unref(reachable);
  oxidd_bdd_substitution_free(rename);
  oxidd_bdd_unref(quantify);
  oxidd_bdd_unref(relation);
  oxidd_bdd_unref(unc_cube);
  oxidd_bdd_unref(bad);
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return CHECK_REFUTED;

unknown_reachable:
  oxidd_bdd_unref(reachable);
  oxidd_bdd_substitution_free(rename);
unknown_with_relation:
  oxidd_bdd_unref(quantify);
  oxidd_bdd_unref(relation);
unknown_with_unc:
  oxidd_bdd_unref(unc_cube);
unknown:
  oxidd_bdd_unref(bad);
  if (next) {
    for (uint32_t q = 0; q < ck->nq; q++)
      oxidd_bdd_unref(next[q]);
  }
  free(next);
  return CHECK_UNKNOWN;
}

static bool emit_controller(Checker *ck, const char *path) {
  Bdd *next = nullptr;
  Bdd bad = {0};
  if (!build_closed_loop(ck, &next, &bad))
    return false;
  oxidd_bdd_unref(bad);
  Aig *controller = aig_new();
  uint32_t *var2lit = malloc(ck->nvars * sizeof *var2lit);
  uint32_t *latches = calloc(ck->nq, sizeof *latches);
  if (!controller || !var2lit || !latches) {
    aig_free(controller);
    free(var2lit);
    free(latches);
    goto fail;
  }
  for (uint32_t v = 0; v < ck->nvars; v++)
    var2lit[v] = UINT32_MAX;
  for (uint32_t i = 0; i < ck->nu; i++)
    var2lit[ck->uvar[i]] =
        aig_input(controller, aig_input_name(ck->game, ck->uinput[i], nullptr));
  for (uint32_t s = 0; s < ck->nstate; s++) {
    uint32_t reset;
    char fallback[32];
    aig_latch_at(ck->game, s, nullptr, nullptr, &reset);
    const char *name = latch_name(ck->game, s, fallback, sizeof fallback);
    latches[s] = aig_latch_named(controller, AIG_FALSE, reset, name);
    var2lit[ck->qvar[s]] = latches[s];
  }
  char generated[96];
  for (uint32_t j = 0; j < ck->ngoals; j++) {
    snprintf(generated, sizeof generated, "curr_%u", j);
    latches[ck->nstate + j] =
        aig_latch_named(controller, AIG_FALSE, 0, generated);
    var2lit[ck->qvar[ck->nstate + j]] = latches[ck->nstate + j];
  }
  Bdd2Aig conversion = {controller, var2lit, 0, ck->nvars, {0}, false};
  for (uint32_t i = 0; i < ck->nc; i++) {
    const char *name = aig_input_name(ck->game, ck->cinput[i], nullptr);
    name += strlen(CONTROLLABLE_PREFIX);
    aig_set_output(controller, name,
                   bdd2aig(&conversion, ck->policy_control[i]));
  }
  for (uint32_t q = 0; q < ck->nq && !conversion.error; q++)
    aig_set_latch_next(controller, latches[q], bdd2aig(&conversion, next[q]));
  memo_free(&conversion.memo);
  free(var2lit);
  free(latches);
  if (conversion.error) {
    aig_free(controller);
    goto fail;
  }
  FILE *out = fopen(path, "w");
  if (!out) {
    aig_free(controller);
    goto fail;
  }
  aig_write_aag(out, controller);
  bool ok = !ferror(out);
  if (fclose(out) != 0)
    ok = false;
  aig_free(controller);
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return ok;

fail:
  for (uint32_t q = 0; q < ck->nq; q++)
    oxidd_bdd_unref(next[q]);
  free(next);
  return false;
}

static const char *result_name(CheckResult result) {
  switch (result) {
  case CHECK_VERIFIED:
    return "VERIFIED";
  case CHECK_REFUTED:
    return "REFUTED";
  case CHECK_UNKNOWN:
    return "UNKNOWN";
  case CHECK_INVALID:
    return "INVALID";
  case CHECK_CERT_FAILED:
    return "CERT_FAILED";
  case CHECK_SKIPPED:
    return "SKIPPED";
  }
  return "UNKNOWN";
}

static const char *method_name(Method method) {
  switch (method) {
  case METHOD_AUTO:
    return "auto";
  case METHOD_CERTIFICATE:
    return "certificate";
  case METHOD_CLOSED_LOOP:
    return "closed-loop";
  case METHOD_BOTH:
    return "both";
  }
  return "auto";
}

static const char *exit_name(int exit_code) {
  switch (exit_code) {
  case EXIT_VERIFIED:
    return "VERIFIED";
  case EXIT_REFUTED:
    return "REFUTED";
  case EXIT_ERROR:
    return "ERROR";
  case EXIT_UNKNOWN:
    return "UNKNOWN";
  case EXIT_INVALID:
    return "INVALID";
  case EXIT_INTERNAL:
    return "INTERNAL-ERROR";
  case EXIT_CERT_FAILED:
    return "CERT_FAILED";
  }
  return "ERROR";
}

static void json_string(FILE *out, const char *text) {
  fputc('"', out);
  for (const unsigned char *p = (const unsigned char *)text; *p; p++) {
    switch (*p) {
    case '"':
      fputs("\\\"", out);
      break;
    case '\\':
      fputs("\\\\", out);
      break;
    case '\b':
      fputs("\\b", out);
      break;
    case '\f':
      fputs("\\f", out);
      break;
    case '\n':
      fputs("\\n", out);
      break;
    case '\r':
      fputs("\\r", out);
      break;
    case '\t':
      fputs("\\t", out);
      break;
    default:
      if (*p < 0x20)
        fprintf(out, "\\u%04x", *p);
      else
        fputc(*p, out);
    }
  }
  fputc('"', out);
}

static void json_named_value(FILE *out, bool *first, const char *name,
                             bool value) {
  if (!*first)
    fputs(", ", out);
  *first = false;
  json_string(out, name);
  fprintf(out, ": %s", value ? "true" : "false");
}

static void write_counterexample_json(FILE *out, const Checker *ck,
                                      const Counterexample *counterexample) {
  if (!counterexample->present) {
    fputs("null", out);
    return;
  }
  fputs("{\n        \"reason\": ", out);
  json_string(out, counterexample->reason);
  fputs(",\n        \"state\": {", out);
  bool first = true;
  for (uint32_t j = 0; j < ck->nstate; j++) {
    char fallback[32];
    const char *name = latch_name(ck->game, j, fallback, sizeof fallback);
    json_named_value(out, &first, name, counterexample->state[j]);
  }
  fputs("},\n        \"curr\": {", out);
  first = true;
  for (uint32_t j = 0; j < ck->ncounter; j++) {
    char name[64];
    snprintf(name, sizeof name, "curr_%u", j);
    json_named_value(out, &first, name, counterexample->curr[j]);
  }
  fputs("},\n        \"uncontrollable_inputs\": {", out);
  first = true;
  for (uint32_t i = 0; i < ck->nu; i++)
    json_named_value(out, &first,
                     aig_input_name(ck->game, ck->uinput[i], nullptr),
                     counterexample->inputs[i]);
  fputs("},\n        \"control_choice\": ", out);
  if (!counterexample->has_control) {
    fputs("null\n      }", out);
    return;
  }
  fputc('{', out);
  first = true;
  for (uint32_t i = 0; i < ck->nc; i++)
    json_named_value(out, &first,
                     aig_input_name(ck->game, ck->cinput[i], nullptr),
                     counterexample->control[i]);
  fputs("}\n      }", out);
}

static void write_method_json(FILE *out, const Checker *ck,
                              const MethodReport *report) {
  fputs("{\n      \"verdict\": ", out);
  json_string(out, result_name(report->result));
  fprintf(out,
          ",\n      \"time_seconds\": %.9f,\n"
          "      \"peak_bdd_nodes\": %zu,\n"
          "      \"counterexample\": ",
          report->seconds, report->peak_nodes);
  write_counterexample_json(out, ck, &report->counterexample);
  fputs("\n    }", out);
}

static bool write_result_json(const Checker *ck,
                              const MethodReport *certificate,
                              const MethodReport *closed_loop, int exit_code,
                              double elapsed) {
  if (!ck->options.json_out_path)
    return true;
  FILE *out = fopen(ck->options.json_out_path, "w");
  if (!out)
    return false;
  const Counterexample *counterexample = nullptr;
  const char *counterexample_method = nullptr;
  if (closed_loop->result == CHECK_REFUTED &&
      closed_loop->counterexample.present) {
    counterexample = &closed_loop->counterexample;
    counterexample_method = "closed-loop";
  } else if (certificate->counterexample.present) {
    counterexample = &certificate->counterexample;
    counterexample_method = "certificate";
  } else if (closed_loop->counterexample.present) {
    counterexample = &closed_loop->counterexample;
    counterexample_method = "closed-loop";
  }
  fputs("{\n  \"format\": \"tlsf-gr1-checkresult-v1\",\n"
        "  \"requested_method\": ",
        out);
  json_string(out, method_name(ck->options.method));
  fputs(",\n  \"verdict\": ", out);
  json_string(out, exit_name(exit_code));
  fprintf(out,
          ",\n  \"exit_code\": %d,\n"
          "  \"methods\": {\n    \"certificate\": ",
          exit_code);
  write_method_json(out, ck, certificate);
  fputs(",\n    \"closed_loop\": ", out);
  write_method_json(out, ck, closed_loop);
  fprintf(out,
          "\n  },\n  \"peak_bdd_nodes\": %zu,\n"
          "  \"elapsed_seconds\": %.9f,\n"
          "  \"counterexample_method\": ",
          ck->peak_nodes, elapsed);
  if (counterexample_method)
    json_string(out, counterexample_method);
  else
    fputs("null", out);
  fputs(",\n  \"counterexample\": ", out);
  if (counterexample)
    write_counterexample_json(out, ck, counterexample);
  else
    fputs("null", out);
  fputs("\n}\n", out);
  bool ok = !ferror(out);
  if (fclose(out) != 0)
    ok = false;
  return ok;
}

static void cleanup(Checker *ck) {
  if (ck->rank)
    for (uint32_t j = 0; j < ck->ngoals; j++) {
      for (uint32_t k = 0; k < ck->rank[j].levels; k++) {
        for (uint32_t i = 0; i < ck->nfair_disj; i++)
          oxidd_bdd_unref(ck->rank[j].x[k][i]);
        free(ck->rank[j].x[k]);
        oxidd_bdd_unref(ck->rank[j].y[k]);
      }
      free(ck->rank[j].x);
      free(ck->rank[j].y);
    }
  free(ck->rank);
  if (ck->dual_rank)
    for (uint32_t k = 0; k < ck->ndual_levels; k++) {
      oxidd_bdd_unref(ck->dual_rank[k].z);
      for (uint32_t j = 0; j < ck->ngoals; j++) {
        oxidd_bdd_unref(ck->dual_rank[k].y[j]);
        for (uint32_t i = 0; i < ck->nfair_disj; i++) {
          DualInnerRank *inner =
              &ck->dual_rank[k].inner[(size_t)j * ck->nfair_disj + i];
          for (uint32_t l = 0; l < inner->levels; l++)
            oxidd_bdd_unref(inner->x[l]);
          free(inner->x);
        }
      }
      free(ck->dual_rank[k].y);
      free(ck->dual_rank[k].inner);
    }
  free(ck->dual_rank);
  oxidd_bdd_unref(ck->cert_inv);
  for (uint32_t i = 0; i < ck->npolicy_choices; i++)
    oxidd_bdd_unref(ck->policy_control ? ck->policy_control[i] : (Bdd){0});
  for (uint32_t j = 0; j < ck->ncounter; j++)
    oxidd_bdd_unref(ck->policy_curr_next ? ck->policy_curr_next[j] : (Bdd){0});
  for (uint32_t s = 0; s < ck->nstate; s++)
    oxidd_bdd_unref(ck->game_next ? ck->game_next[s] : (Bdd){0});
  for (uint32_t j = 0; j < ck->ngoals; j++)
    oxidd_bdd_unref(ck->goal ? ck->goal[j] : (Bdd){0});
  for (uint32_t j = 0; j < ck->ngoals; j++)
    oxidd_bdd_unref(ck->cert_goal ? ck->cert_goal[j] : (Bdd){0});
  for (uint32_t i = 0; i < ck->nfair; i++)
    oxidd_bdd_unref(ck->fair ? ck->fair[i] : (Bdd){0});
  for (uint32_t i = 0; i < ck->nfair; i++)
    oxidd_bdd_unref(ck->cert_fair ? ck->cert_fair[i] : (Bdd){0});
  oxidd_bdd_unref(ck->game_bad);
  oxidd_bdd_unref(ck->input_cube);
  for (uint32_t q = 0; q < ck->nq; q++) {
    oxidd_bdd_unref(ck->q ? ck->q[q] : (Bdd){0});
    oxidd_bdd_unref(ck->qp ? ck->qp[q] : (Bdd){0});
  }
  for (uint32_t i = 0; i < ck->nu; i++)
    oxidd_bdd_unref(ck->u ? ck->u[i] : (Bdd){0});
  for (uint32_t i = 0; i < ck->nc; i++)
    oxidd_bdd_unref(ck->c ? ck->c[i] : (Bdd){0});
  free(ck->policy_control);
  free(ck->policy_curr_next);
  free(ck->game_next);
  free(ck->goal);
  free(ck->cert_goal);
  free(ck->fair);
  free(ck->cert_fair);
  free(ck->qvar);
  free(ck->qpvar);
  free(ck->uvar);
  free(ck->cvar);
  free(ck->q);
  free(ck->qp);
  free(ck->u);
  free(ck->c);
  free(ck->uinput);
  free(ck->cinput);
  if (ck->manager._p)
    oxidd_bdd_manager_unref(ck->manager);
  aig_free(ck->certificate);
  aig_free(ck->policy);
  aig_free(ck->game);
}

int main(int argc, char **argv) {
  Options options;
  char *owned_policy_json = nullptr, *owned_cert_json = nullptr;
  int parsed =
      parse_options(argc, argv, &options, &owned_policy_json, &owned_cert_json);
  if (parsed != 0) {
    free(owned_policy_json);
    free(owned_cert_json);
    return parsed > 0 ? 0 : EXIT_ERROR;
  }
  Checker ck = {.options = options, .started = now_seconds()};
  MethodReport certificate = {.result = CHECK_SKIPPED};
  MethodReport closed_loop = {.result = CHECK_SKIPPED};
  int exit_code = EXIT_ERROR;
  uint32_t *levels = nullptr;
  char message[512] = {0};
  ck.game = read_aag(options.game_path, true, message, sizeof message);
  ck.policy = read_aag(options.policy_path, false, message, sizeof message);
  if (options.certificate_path)
    ck.certificate =
        read_aag(options.certificate_path, false, message, sizeof message);
  if (!ck.game || !ck.policy || (options.certificate_path && !ck.certificate)) {
    printf("INVALID\n");
    fprintf(stderr, "tlsfcertcheck: %s\n", message);
    exit_code = EXIT_INVALID;
    goto finish;
  }
  bool structure_ok =
      validate_aig_structure(ck.game, "game", message, sizeof message) &&
      validate_aig_structure(ck.policy, "policy", message, sizeof message) &&
      (!ck.certificate || validate_aig_structure(ck.certificate, "certificate",
                                                 message, sizeof message));
  if (!structure_ok) {
    printf("INVALID\n");
    fprintf(stderr, "tlsfcertcheck: %s\n", message);
    exit_code = EXIT_INVALID;
    goto finish;
  }
  ck.original_nlat = aig_num_latches(ck.game);
  aig_sample_input_dependent_acceptance(ck.game);
  ck.nstate = aig_num_latches(ck.game);
  ck.nin = aig_num_inputs(ck.game);
  ck.ngoals = count_goals(ck.game);
  ck.nfair = aig_num_fairness(ck.game);
  ck.nfair_disj = ck.nfair ? ck.nfair : 1;
  if (!ck.ngoals) {
    printf("INVALID\n");
    fprintf(stderr, "tlsfcertcheck: game has no justice goals\n");
    exit_code = EXIT_INVALID;
    goto finish;
  }
  ck.uinput = ck.nin ? calloc(ck.nin, sizeof *ck.uinput) : nullptr;
  ck.cinput = ck.nin ? calloc(ck.nin, sizeof *ck.cinput) : nullptr;
  if (ck.nin && (!ck.uinput || !ck.cinput)) {
    printf("ERROR\n");
    fprintf(stderr, "tlsfcertcheck: out of memory\n");
    exit_code = EXIT_ERROR;
    goto finish;
  }
  for (uint32_t p = 0; p < ck.nin; p++) {
    const char *name = aig_input_name(ck.game, p, nullptr);
    if (is_controllable(name))
      ck.cinput[ck.nc++] = p;
    else
      ck.uinput[ck.nu++] = p;
  }

  bool interface_ok = validate_game_names(&ck, message, sizeof message) &&
                      validate_sidecars(&ck, message, sizeof message) &&
                      validate_policy_interface(&ck, message, sizeof message);
  if (interface_ok && ck.certificate)
    interface_ok =
        validate_certificate_interface(&ck, &levels, message, sizeof message);
  if (!interface_ok) {
    printf("INVALID\n");
    fprintf(stderr, "tlsfcertcheck: %s\n", message);
    exit_code = EXIT_INVALID;
    goto finish;
  }

  double setup_started = now_seconds();
  if (!setup_bdds(&ck, levels, message, sizeof message)) {
    ck.setup_seconds = now_seconds() - setup_started;
    printf("UNKNOWN\n");
    fprintf(stderr, "tlsfcertcheck: %s\n", message);
    exit_code = EXIT_UNKNOWN;
    goto finish;
  }
  ck.setup_seconds = now_seconds() - setup_started;
  free(levels);
  levels = nullptr;

  bool run_certificate = options.method == METHOD_CERTIFICATE ||
                         options.method == METHOD_BOTH ||
                         (options.method == METHOD_AUTO && ck.certificate);
  bool run_closed_loop = options.method == METHOD_CLOSED_LOOP ||
                         options.method == METHOD_BOTH ||
                         (options.method == METHOD_AUTO && !ck.certificate);
  if (run_certificate) {
    double started = now_seconds();
    ck.current_counterexample = &certificate.counterexample;
    certificate.result = check_certificate_mode(&ck);
    certificate.seconds = now_seconds() - started;
    ck.proof_seconds += certificate.seconds;
    certificate.peak_nodes = ck.peak_nodes;
    if (options.method == METHOD_AUTO &&
        certificate.result == CHECK_CERT_FAILED) {
      puts("NOTE certificate did not prove the policy; falling back to "
           "closed-loop");
      run_closed_loop = true;
    }
  }
  if (run_closed_loop) {
    double started = now_seconds();
    ck.current_counterexample = &closed_loop.counterexample;
    if (!ensure_full_policy(&ck, message, sizeof message)) {
      fprintf(stderr, "tlsfcertcheck: %s\n", message);
      closed_loop.result = CHECK_UNKNOWN;
    } else {
      closed_loop.result = check_closed_loop_mode(&ck);
    }
    closed_loop.seconds = now_seconds() - started;
    ck.proof_seconds += closed_loop.seconds;
    closed_loop.peak_nodes = ck.peak_nodes;
  }
  ck.current_counterexample = nullptr;

  if (certificate.result != CHECK_SKIPPED)
    printf("METHOD certificate %s time=%.6f\n", result_name(certificate.result),
           certificate.seconds);
  if (closed_loop.result != CHECK_SKIPPED)
    printf("METHOD closed-loop %s time=%.6f\n", result_name(closed_loop.result),
           closed_loop.seconds);
  printf("STATS peak_bdd_nodes=%zu elapsed=%.6f\n", ck.peak_nodes,
         now_seconds() - ck.started);

  bool disagree = certificate.result == CHECK_VERIFIED &&
                  closed_loop.result == CHECK_REFUTED;
  if (disagree) {
    printf("INTERNAL-ERROR\n");
    fprintf(stderr,
            "tlsfcertcheck: certificate and closed-loop methods disagree\n");
    exit_code = EXIT_INTERNAL;
  } else if (certificate.result == CHECK_INVALID ||
             closed_loop.result == CHECK_INVALID) {
    printf("INVALID\n");
    exit_code = EXIT_INVALID;
  } else if (closed_loop.result == CHECK_REFUTED) {
    printf("REFUTED\n");
    exit_code = EXIT_REFUTED;
  } else if (certificate.result == CHECK_VERIFIED ||
             closed_loop.result == CHECK_VERIFIED) {
    bool emitted = true;
    if (options.emit_path)
      emitted = ensure_full_policy(&ck, message, sizeof message) &&
                emit_controller(&ck, options.emit_path);
    if (!emitted) {
      printf("ERROR\n");
      fprintf(stderr, "tlsfcertcheck: cannot emit controller '%s'\n",
              options.emit_path);
      exit_code = EXIT_ERROR;
    } else {
      printf("VERIFIED\n");
      exit_code = EXIT_VERIFIED;
    }
  } else if (certificate.result == CHECK_UNKNOWN ||
             closed_loop.result == CHECK_UNKNOWN) {
    printf("UNKNOWN\n");
    exit_code = EXIT_UNKNOWN;
  } else if (certificate.result == CHECK_CERT_FAILED) {
    printf("CERT_FAILED\n");
    exit_code = EXIT_CERT_FAILED;
  } else {
    printf("UNKNOWN\n");
    exit_code = EXIT_UNKNOWN;
  }

finish:
  free(levels);
  if (!write_result_json(&ck, &certificate, &closed_loop, exit_code,
                         now_seconds() - ck.started)) {
    fprintf(stderr, "tlsfcertcheck: cannot write JSON result '%s'\n",
            options.json_out_path);
    exit_code = EXIT_ERROR;
  }
  if (ck.run_initialized)
    oxidd_run_finish(&ck.run);
  if (options.stats)
    fprintf(stderr,
            "TLSFCERTCHECK_STATS aig_gates_visited=%zu requested_roots=%zu "
            "setup_seconds=%.9f proof_seconds=%.9f "
            "peak_live_nodes_sample=%zu policy_mode_builds=%zu "
            "policy_counter_constants=%zu policy_specialized_gates=%zu "
            "policy_unspecialized_gates=%zu successor_substitutions=%zu "
            "successor_applications=%zu final_status=%s\n",
            ck.run.built_gates, ck.requested_roots, ck.setup_seconds,
            ck.proof_seconds, ck.peak_nodes, ck.policy_mode_builds,
            ck.policy_counter_constants, ck.policy_specialized_gates,
            ck.policy_unspecialized_gates, ck.successor_substitutions,
            ck.successor_applications, exit_name(exit_code));
  counterexample_clear(&certificate.counterexample);
  counterexample_clear(&closed_loop.counterexample);
  cleanup(&ck);
  free(owned_policy_json);
  free(owned_cert_json);
  return exit_code;
}
