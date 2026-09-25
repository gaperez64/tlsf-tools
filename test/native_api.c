#define _GNU_SOURCE
#include "tlsf/pipeline.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/gr1_check.h"
#include "tlsf/gr1_reduction.h"
#include "tlsf/gr1_lift.h"
#include "tlsf/print_tlsf.h"

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static const char real_game[] =
    "aag 3 2 1 1 0 0 0 1 0\n"
    "2\n4\n6 6 1\n0\n1\n6\n"
    "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n";
static const char unreal_game[] =
    "aag 3 2 1 1 0 0 0 1 0\n"
    "2\n4\n6 6 0\n0\n1\n6\n"
    "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n";

static TlsfGr1Bytes span(const char *s, size_t size) {
  return (TlsfGr1Bytes){(const uint8_t *)s, size};
}

static int cancelled(void *context) {
  (void)context;
  return 1;
}

typedef struct {
  unsigned calls, threshold;
} CancelAfter;

static int cancel_after(void *context) {
  CancelAfter *state = context;
  return ++state->calls >= state->threshold;
}

static Aig *parse_game(const char *text) {
  FILE *in = fmemopen((void *)text, strlen(text), "r");
  assert(in);
  Aig *game = aig_read_aag(in);
  fclose(in);
  assert(game);
  return game;
}

static void roundtrip(const char *game_text, int expect_unreal) {
  size_t game_size = strlen(game_text);
  Aig *game = parse_game(game_text);
  char reason[128];
  assert(tlsf_gr1_validate_game(game, reason, sizeof reason));
  OxiddSolveOptions options = oxidd_solve_options_default();
  OxiddFailure failure = {0};
  options.failure = &failure;
  options.node_cap = options.cache_cap = 1u << 16;
  options.max_artifact_bytes = 1u << 20;
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
  int unreal = 0;
  Aig *strategy =
      solve_gr1_oxidd_ex_with_certificate(game, &unreal, &options, &export);
  assert(unreal == expect_unreal);
  assert(failure.kind == OXIDD_FAILURE_NONE && !export.failed);
  assert((strategy != NULL) == !unreal);
  assert(cert && cert_json && policy && policy_json);
  assert(cert_size && cert_json_size && policy_size && policy_json_size);
  aig_free(strategy);
  TlsfGr1CheckInput check_input = {
      .game_aag = span(game_text, game_size),
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
  assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_OK);
  if (checked.verdict != TLSF_GR1_CHECK_VERIFIED)
    fwrite(checked.json, 1, checked.json_size, stderr);
  assert(checked.verdict == TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&checked);
  if (!expect_unreal) {
    char *changed = strdup(cert);
    assert(changed);
    char *line = changed;
    for (int i = 0; i < 4; i++) {
      line = strchr(line, '\n');
      assert(line);
      line++;
    }
    assert(*line == '2');
    *line = '0';
    TlsfGr1CheckInput mutated = check_input;
    mutated.certificate_aag = span(changed, cert_size);
    check_options.method = TLSF_GR1_CHECK_AUTO;
    int pipe_fds[2];
    assert(pipe(pipe_fds) == 0);
    int saved = dup(STDOUT_FILENO);
    assert(saved >= 0);
    fflush(stdout);
    assert(dup2(pipe_fds[1], STDOUT_FILENO) >= 0);
    close(pipe_fds[1]);
    TlsfGr1CheckStatus status =
        tlsf_gr1_check(&mutated, &check_options, &checked);
    fflush(stdout);
    assert(dup2(saved, STDOUT_FILENO) >= 0);
    close(saved);
    char leaked[16];
    assert(read(pipe_fds[0], leaked, sizeof leaked) == 0);
    close(pipe_fds[0]);
    assert(status == TLSF_GR1_CHECK_OK);
    assert(checked.verdict == TLSF_GR1_CHECK_VERIFIED);
    assert(checked.json && strstr(checked.json, "\"reason\":"));
    tlsf_gr1_check_result_clear(&checked);
    free(changed);
  }
  for (TlsfGr1CheckMethod method = TLSF_GR1_CHECK_AUTO;
       method <= TLSF_GR1_CHECK_BOTH; method++) {
    if (method == TLSF_GR1_CHECK_REGION || method == TLSF_GR1_CHECK_CERTIFICATE)
      continue;
    check_options.method = method;
    assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
           TLSF_GR1_CHECK_OK);
    assert(checked.verdict == TLSF_GR1_CHECK_VERIFIED);
    tlsf_gr1_check_result_clear(&checked);
  }
  check_options.method = TLSF_GR1_CHECK_CERTIFICATE;
  if (!expect_unreal) {
    TlsfGr1CheckInput region_input = check_input;
    region_input.policy_aag = (TlsfGr1Bytes){0};
    region_input.policy_json = (TlsfGr1Bytes){0};
    check_options.method = TLSF_GR1_CHECK_REGION;
    assert(tlsf_gr1_check(&region_input, &check_options, &checked) ==
           TLSF_GR1_CHECK_OK);
    assert(checked.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
    tlsf_gr1_check_result_clear(&checked);
    check_options.method = TLSF_GR1_CHECK_CERTIFICATE;
  }
  char *tampered = strdup(cert_json);
  assert(tampered);
  tampered[0] = 'X';
  check_input.certificate_json = span(tampered, cert_json_size);
  assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_OK);
  if (checked.verdict != TLSF_GR1_CHECK_INVALID)
    fprintf(stderr, "tampered sidecar verdict=%d evidence=%s\n",
            checked.verdict, checked.json ? checked.json : "(none)");
  assert(checked.verdict == TLSF_GR1_CHECK_INVALID);
  tlsf_gr1_check_result_clear(&checked);
  free(tampered);
  check_input.certificate_json = span(cert_json, cert_json_size);
  check_input.game_aag = span("not an AAG", 10);
  assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_OK);
  assert(checked.verdict == TLSF_GR1_CHECK_INVALID);
  tlsf_gr1_check_result_clear(&checked);
  check_input.game_aag = span(game_text, game_size);
  check_options.node_cap = 1;
  assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_BAD_ARGUMENT);
  assert(checked.verdict != TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&checked);
  check_options.node_cap = 1u << 16;
  check_options.cancelled = cancelled;
  assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_CANCELLED);
  assert(checked.json == NULL);
  tlsf_gr1_check_result_clear(&checked);
  check_options.cancelled = NULL;
  check_options.deadline_mono_ns = 1;
  assert(tlsf_gr1_check(&check_input, &check_options, &checked) ==
         TLSF_GR1_CHECK_DEADLINE);
  assert(checked.json == NULL);
  tlsf_gr1_check_result_clear(&checked);
  free(cert);
  free(cert_json);
  free(policy);
  free(policy_json);
}

static void mid_compile_cancellation(void) {
  char game_text[16384];
  const unsigned gates = 128;
  int used = snprintf(game_text, sizeof game_text,
                      "aag %u 2 1 1 %u 0 0 1 0\n2\n4\n6 6 1\n%u\n1\n6\n",
                      3 + gates, gates, 2 * (3 + gates));
  assert(used > 0 && (size_t)used < sizeof game_text);
  for (unsigned i = 0; i < gates; i++) {
    int written =
        snprintf(game_text + used, sizeof game_text - (size_t)used,
                 "%u %u %u\n", 8 + 2 * i, i ? 6 + 2 * i : 6, i & 1 ? 4 : 2);
    assert(written > 0 && (size_t)written < sizeof game_text - (size_t)used);
    used += written;
  }
  used += snprintf(game_text + used, sizeof game_text - (size_t)used,
                   "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n");
  assert((size_t)used < sizeof game_text);
  char *bytes[4] = {0};
  size_t sizes[4] = {0};
  Gr1CertificateOptions export = {

      .semantics = GR1_CERTIFICATE_SEMANTICS_EXACT,
      .aag_bytes = &bytes[0],
      .json_bytes = &bytes[1],
      .policy_aag_bytes = &bytes[2],
      .policy_json_bytes = &bytes[3],
      .aag_size = &sizes[0],
      .json_size = &sizes[1],
      .policy_aag_size = &sizes[2],
      .policy_json_size = &sizes[3],
      .max_artifact_bytes = 1u << 20,
  };
  OxiddSolveOptions options = oxidd_solve_options_default();
  options.node_cap = options.cache_cap = 1u << 16;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd_ex_with_certificate(
      parse_game(game_text), &unreal, &options, &export);
  assert(strategy && !unreal && !export.failed);
  aig_free(strategy);
  TlsfGr1CheckInput input = {
      .game_aag = span(game_text, (size_t)used),
      .certificate_aag = span(bytes[0], sizes[0]),
      .certificate_json = span(bytes[1], sizes[1]),
      .policy_aag = span(bytes[2], sizes[2]),
      .policy_json = span(bytes[3], sizes[3]),
  };
  TlsfGr1CheckOptions check_options = {

      .method = TLSF_GR1_CHECK_CERTIFICATE,
      .node_cap = 1u << 16,
      .cache_cap = 1u << 16,
      .max_artifact_bytes = 1u << 20,
      .cancelled = cancel_after,
  };
  bool stopped_during_compile = false;
  for (unsigned threshold = 3; threshold < 24 && !stopped_during_compile;
       threshold++) {
    CancelAfter state = {.threshold = threshold};
    check_options.cancel_ctx = &state;
    TlsfGr1CheckResult result;
    TlsfGr1CheckStatus status = tlsf_gr1_check(&input, &check_options, &result);
    stopped_during_compile = status == TLSF_GR1_CHECK_CANCELLED &&
                             !strcmp(result.stage, "checker_game") &&
                             state.calls >= 3 && !result.json;
    tlsf_gr1_check_result_clear(&result);
  }
  assert(stopped_during_compile);
  for (size_t i = 0; i < 4; i++)
    free(bytes[i]);
}

static void solver_limits(void) {
  OxiddSolveOptions options = oxidd_solve_options_default();
  OxiddFailure failure = {0};
  options.failure = &failure;
  options.node_cap = options.cache_cap = 1u << 16;
  options.cancelled = cancelled;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd_ex(parse_game(real_game), &unreal, &options);
  assert(!strategy && !unreal);
  assert(failure.kind == OXIDD_FAILURE_CANCELLED);
  options.cancelled = NULL;
  options.deadline_mono_ns = 1;
  strategy = solve_gr1_oxidd_ex(parse_game(real_game), &unreal, &options);
  assert(!strategy && !unreal);
  assert(failure.kind == OXIDD_FAILURE_DEADLINE);
  options.deadline_mono_ns = 0;
  char *certificate = NULL;
  size_t certificate_size = 0;
  Gr1CertificateOptions export = {

      .semantics = GR1_CERTIFICATE_SEMANTICS_EXACT,
      .aag_bytes = &certificate,
      .aag_size = &certificate_size,
      .max_artifact_bytes = 1,
  };
  strategy = solve_gr1_oxidd_ex_with_certificate(parse_game(real_game), &unreal,
                                                 &options, &export);
  assert(!strategy && !unreal && export.failed);
  assert(!certificate && !certificate_size);
  free(certificate);
  char *aag = NULL, *json = NULL, *policy = NULL, *policy_json = NULL;
  size_t aag_size = 0, json_size = 0, policy_size = 0, policy_json_size = 0;
  Gr1CertificateOptions partial = {

      .semantics = GR1_CERTIFICATE_SEMANTICS_EXACT,
      .aag_bytes = &aag,
      .json_bytes = &json,
      .policy_aag_bytes = &policy,
      .policy_json_bytes = &policy_json,
      .aag_size = &aag_size,
      .json_size = &json_size,
      .policy_aag_size = &policy_size,
      .policy_json_size = &policy_json_size,
      .max_artifact_bytes = 500,
  };
  failure = (OxiddFailure){0};
  strategy = solve_gr1_oxidd_ex_with_certificate(parse_game(real_game), &unreal,
                                                 &options, &partial);
  assert(!strategy && !unreal && partial.failed);
  assert(failure.kind == OXIDD_FAILURE_ARTIFACT_LIMIT);
  assert(!aag && !json && !policy && !policy_json);
  assert(!aag_size && !json_size && !policy_size && !policy_json_size);
  Gr1CertificateOptions invalid_export = {

      .aag_bytes = &certificate};
  strategy = solve_gr1_oxidd_ex_with_certificate(parse_game(real_game), &unreal,
                                                 &options, &invalid_export);
  assert(!strategy && !unreal && invalid_export.failed);
  assert(failure.kind == OXIDD_FAILURE_INVALID);
  strategy = solve_gr1_oxidd_ex(parse_game(real_game), NULL, &options);
  assert(!strategy && failure.kind == OXIDD_FAILURE_INVALID);
}

static void expand_source(const char *source_path,
                          const char *provenance_path) {
  FILE *input = fopen(source_path, "rb");
  assert(input);
  assert(fseek(input, 0, SEEK_END) == 0);
  long length = ftell(input);
  assert(length > 0);
  assert(fseek(input, 0, SEEK_SET) == 0);
  char *source = malloc((size_t)length);
  assert(source);
  assert(fread(source, 1, (size_t)length, input) == (size_t)length);
  fclose(input);
  char hash[65];
  assert(tlsf_pipeline_source_sha256(source, (size_t)length, hash));
  FILE *stream = fmemopen(source, (size_t)length, "r");
  assert(stream);
  TlsfSpec *spec = cli_parse(stream, "native-api-test");
  fclose(stream);
  assert(spec);
  FILE *provenance = fopen(provenance_path, "wb");
  assert(provenance);
  ParamOverride override = {.name = "n", .value = 4};
  assert(tlsf_pipeline_expand_spec(spec, &override, 1, provenance, hash, false,
                                   NULL) == 0);
  assert(fclose(provenance) == 0);
  print_tlsf(stdout, spec, false);
  spec_free(spec);
  free(source);
}

static void write_artifact(const char *prefix, const char *suffix,
                           const char *bytes, size_t size) {
  size_t length = strlen(prefix) + strlen(suffix) + 1;
  char *path = malloc(length);
  assert(path);
  snprintf(path, length, "%s%s", prefix, suffix);
  FILE *out = fopen(path, "wb");
  assert(out);
  assert(fwrite(bytes, 1, size, out) == size);
  assert(fclose(out) == 0);
  free(path);
}

static void export_game_file(const char *game_path,
                             const char *certificate_path,
                             const char *policy_path, const char *prefix) {
  FILE *in = fopen(game_path, "rb");
  assert(in);
  Aig *game = aig_read_aag(in);
  assert(fclose(in) == 0 && game);
  size_t cert_json_path_size = strlen(certificate_path) + 6;
  size_t policy_json_path_size = strlen(policy_path) + 6;
  char *cert_json_path = malloc(cert_json_path_size);
  char *policy_json_path = malloc(policy_json_path_size);
  assert(cert_json_path && policy_json_path);
  snprintf(cert_json_path, cert_json_path_size, "%s.json", certificate_path);
  snprintf(policy_json_path, policy_json_path_size, "%s.json", policy_path);
  char *cert = NULL, *cert_json = NULL, *policy = NULL, *policy_json = NULL;
  size_t cert_size = 0, cert_json_size = 0, policy_size = 0;
  size_t policy_json_size = 0;
  Gr1CertificateOptions export = {

      .aag_path = certificate_path,
      .json_path = cert_json_path,
      .policy_aag_path = policy_path,
      .policy_json_path = policy_json_path,
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
  OxiddSolveOptions options = oxidd_solve_options_default();
  options.max_artifact_bytes = 1u << 20;
  int unreal = 0;
  Aig *strategy =
      solve_gr1_oxidd_ex_with_certificate(game, &unreal, &options, &export);
  assert(!export.failed && (strategy || unreal));
  aig_free(strategy);
  assert(cert && cert_json && policy && policy_json);
  write_artifact(prefix, ".certificate.aag", cert, cert_size);
  write_artifact(prefix, ".certificate.json", cert_json, cert_json_size);
  write_artifact(prefix, ".policy.aag", policy, policy_size);
  write_artifact(prefix, ".policy.json", policy_json, policy_json_size);
  printf("%d\n", unreal);
  free(cert);
  free(cert_json);
  free(policy);
  free(policy_json);
  free(cert_json_path);
  free(policy_json_path);
}

int main(int argc, char **argv) {
  if (argc == 4 && !strcmp(argv[1], "--expand")) {
    expand_source(argv[2], argv[3]);
    return 0;
  }
  if (argc == 6 && !strcmp(argv[1], "--export")) {
    export_game_file(argv[2], argv[3], argv[4], argv[5]);
    return 0;
  }
  roundtrip(real_game, 0);
  roundtrip(unreal_game, 1);
  mid_compile_cancellation();
  solver_limits();
  assert(!tlsf_gr1_validate_game(NULL, NULL, 0));
  char hash[65];
  assert(!tlsf_pipeline_source_sha256("x\0y", 3, hash));
  TlsfPipelineError pipeline_error;
  TlsfPipelineOptions pipeline_options = {

      .error = &pipeline_error};
  assert(
      !tlsf_pipeline_load_bytes((const uint8_t *)"x\0y", 3, &pipeline_options));
  assert(pipeline_error.status == TLSF_PIPELINE_INVALID);
  int error_pipe[2];
  assert(pipe(error_pipe) == 0);
  int saved_error = dup(STDERR_FILENO);
  assert(saved_error >= 0);
  fflush(stderr);
  assert(dup2(error_pipe[1], STDERR_FILENO) >= 0);
  close(error_pipe[1]);
  assert(!tlsf_pipeline_load_bytes((const uint8_t *)"not TLSF", 8,
                                   &pipeline_options));
  fflush(stderr);
  assert(dup2(saved_error, STDERR_FILENO) >= 0);
  close(saved_error);
  char diagnostics[16];
  assert(read(error_pipe[0], diagnostics, sizeof diagnostics) == 0);
  close(error_pipe[0]);
  assert(pipeline_error.status == TLSF_PIPELINE_INVALID);
  assert(pipeline_error.message[0]);
  const char source[] =
      "INFO { TITLE: \"small\" DESCRIPTION: \"small\" SEMANTICS: Mealy "
      "TARGET: Mealy }\n"
      "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G b; } }\n";
  assert(tlsf_pipeline_source_sha256(source, strlen(source), hash));
  char source_copy[sizeof source];
  memcpy(source_copy, source, sizeof source);
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes(
      (const uint8_t *)source_copy, strlen(source_copy), NULL);
  assert(pipeline);
  source_copy[0] = 'X';
  assert(pipeline->source_size == strlen(source));
  assert(!memcmp(pipeline->source_bytes, source, pipeline->source_size));
  assert(!strcmp(pipeline->source_sha256, hash));
  tlsf_pipeline_free(pipeline);
  return 0;
}
