// U0 in-process replay of an environment (UNREAL) certificate and policy
// through the public C API (tlsf/gr1_oxidd.h and tlsf/gr1_check.h);
// test/oracle/test_gr1_environment_replay.py replays through the CLI. See
// docs/gr1-environment-certificate.md for the format.
//
// The fixture is the n=1 valuation of that file's forbidden_family(): one
// justice goal that safety forbids, plus one fairness assumption. It is
// UNREAL by construction.
#define _GNU_SOURCE
#include "tlsf/gr1_oxidd.h"
#include "tlsf/gr1_check.h"

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char forbidden_1[] =
    "aag 3 2 1 0 0 1 0 1 1\n"
    "2\n4\n6 4 0\n6\n1\n6\n2\n"
    "i0 u0\ni1 controllable_c0\nb0 bad_record\nj0 justice_0\nf0 fairness_0\n";

// The same game with its controllable input's symbol missing, which
// aig_read_aag accepts.
static const char forbidden_1_unnamed_input[] =
    "aag 3 2 1 0 0 1 0 1 1\n"
    "2\n4\n6 4 0\n6\n1\n6\n2\n"
    "i0 u0\nb0 bad_record\nj0 justice_0\nf0 fairness_0\n";

static TlsfGr1Bytes span(const char *s, size_t size) {
  return (TlsfGr1Bytes){(const uint8_t *)s, size};
}

static Aig *parse_game(const char *text) {
  FILE *in = fmemopen((void *)text, strlen(text), "r");
  assert(in);
  Aig *game = aig_read_aag(in);
  fclose(in);
  assert(game);
  return game;
}

int main(void) {
  size_t game_size = strlen(forbidden_1);
  Aig *game = parse_game(forbidden_1);
  char reason[128];
  assert(tlsf_gr1_validate_game(game, reason, sizeof reason));

  OxiddFailure failure = {0};
  char *cert = NULL, *cert_json = NULL, *policy = NULL, *policy_json = NULL;
  size_t cert_size = 0, cert_json_size = 0, policy_size = 0;
  size_t policy_json_size = 0;
  Gr1CertificateOptions export = {
      .semantics = GR1_CERTIFICATE_SEMANTICS_EXACT,
      .aag_bytes = &cert,
      .json_bytes = &cert_json,
      .policy_aag_bytes = &policy,
      .policy_json_bytes = &policy_json,
      .aag_size = &cert_size,
      .json_size = &cert_json_size,
      .policy_aag_size = &policy_size,
      .policy_json_size = &policy_json_size,
      .max_artifact_bytes = 1u << 20,
  };
  Gr1SolveOptions options = {.oxidd = oxidd_solve_options_default(),
                             .certificate = &export};
  options.oxidd.failure = &failure;
  options.oxidd.node_cap = options.oxidd.cache_cap = 1u << 16;
  options.oxidd.max_artifact_bytes = 1u << 20;
  // The fixture encodes safety as one AIGER 'b' record and has zero ordinary
  // outputs; the default OXIDD_SAFETY_OBJECTIVE_OUTPUT would request ordinary
  // output 0, find none, and fail root construction
  // (gr1_oxidd.c's build_gr1_roots). Select the typed-bad objective instead.
  options.oxidd.safety_objective = OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd(game, &unreal, &options);
  assert(unreal == 1);
  assert(strategy == NULL);
  assert(failure.kind == OXIDD_FAILURE_NONE && !export.failed);
  assert(cert && cert_json && policy && policy_json);
  assert(cert_size && cert_json_size && policy_size && policy_json_size);
  assert(strstr(cert_json, "\"side\":\"environment\""));
  assert(strstr(policy_json, "\"side\":\"environment\""));

  TlsfGr1CheckInput check_input = {
      .game_aag = span(forbidden_1, game_size),
      .certificate_aag = span(cert, cert_size),
      .certificate_json = span(cert_json, cert_json_size),
      .policy_aag = span(policy, policy_size),
      .policy_json = span(policy_json, policy_json_size),
  };
  TlsfGr1CheckOptions check_options = {
      .method = TLSF_GR1_CHECK_CERTIFICATE,
      .node_cap = 1u << 16,
      .cache_cap = 1u << 16,
      .max_artifact_bytes = 1u << 20,
  };
  TlsfGr1CheckResult checked;

  // Every environment route must verify the exported witness, as
  // replay_verified() does through the CLI.
  for (TlsfGr1CheckMethod method = TLSF_GR1_CHECK_AUTO;
       method <= TLSF_GR1_CHECK_BOTH; method++) {
    if (method == TLSF_GR1_CHECK_REGION)
      continue; // region-v1 is system-only and policy-free
    check_options.method = method;
    assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
           TLSF_GR1_CHECK_OK);
    if (checked.verdict != TLSF_GR1_CHECK_VERIFIED)
      fwrite(checked.json, 1, checked.json_size, stderr);
    assert(checked.verdict == TLSF_GR1_CHECK_VERIFIED);
    tlsf_gr1_check_result_clear(&checked);
  }

  // A truncated environment policy is INVALID. native_api.c tampers with a
  // system-side sidecar byte; this cuts the environment policy's AAG.
  check_options.method = TLSF_GR1_CHECK_CERTIFICATE;
  TlsfGr1CheckInput truncated_input = check_input;
  truncated_input.policy_aag = span(policy, policy_size / 2);
  assert(tlsf_gr1_check(&truncated_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_OK);
  assert(checked.verdict == TLSF_GR1_CHECK_INVALID);
  tlsf_gr1_check_result_clear(&checked);

  // A game input without a name is INVALID in-process, not a null strcmp
  // in validate_game_names.
  TlsfGr1CheckInput unnamed_input = check_input;
  unnamed_input.game_aag =
      span(forbidden_1_unnamed_input, strlen(forbidden_1_unnamed_input));
  assert(tlsf_gr1_check(&unnamed_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_OK);
  assert(checked.verdict == TLSF_GR1_CHECK_INVALID);
  tlsf_gr1_check_result_clear(&checked);

  free(cert);
  free(cert_json);
  free(policy);
  free(policy_json);
  return 0;
}
