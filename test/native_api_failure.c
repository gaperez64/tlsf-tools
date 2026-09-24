#define _GNU_SOURCE
#include "tlsf/native.h"

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <stdlib.h>
#include <string.h>

static int fail_malloc, fail_calloc;
static size_t fail_malloc_at, malloc_calls;
static size_t fail_export_at, export_calls, fail_realloc_at, realloc_calls;

void *__real_malloc(size_t size);
void *__real_calloc(size_t count, size_t size);
void *__wrap_malloc(size_t size);
void *__wrap_calloc(size_t count, size_t size);
void *__wrap_malloc(size_t size) {
  malloc_calls++;
  return fail_malloc || (fail_malloc_at && malloc_calls == fail_malloc_at)
             ? NULL
             : __real_malloc(size);
}
void *__wrap_calloc(size_t count, size_t size) {
  return fail_calloc ? NULL : __real_calloc(count, size);
}

void *__real_oxidd_host_calloc(size_t count, size_t size);
void *__wrap_oxidd_host_calloc(size_t count, size_t size);
void *__wrap_oxidd_host_calloc(size_t count, size_t size) {
  export_calls++;
  return fail_export_at && export_calls == fail_export_at
             ? NULL
             : __real_oxidd_host_calloc(count, size);
}
void *__real_oxidd_host_realloc(void *pointer, size_t size);
void *__wrap_oxidd_host_realloc(void *pointer, size_t size);
void *__wrap_oxidd_host_realloc(void *pointer, size_t size) {
  realloc_calls++;
  return fail_realloc_at && realloc_calls == fail_realloc_at
             ? NULL
             : __real_oxidd_host_realloc(pointer, size);
}

static const char game_text[] =
    "aag 3 2 1 1 0 0 0 1 0\n2\n4\n6 6 1\n0\n1\n6\n"
    "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n";

static Aig *game_new(void) {
  FILE *stream = fmemopen((void *)game_text, strlen(game_text), "r");
  assert(stream);
  Aig *game = aig_read_aag(stream);
  fclose(stream);
  assert(game);
  return game;
}

static void deeper_failures(void) {
  char *valid[4] = {0};
  size_t valid_sizes[4] = {0};
  for (size_t injection = 0; injection <= 4; injection++) {
    char *bytes[4] = {0};
    size_t sizes[4] = {0};
    OxiddFailure failure = {0};
    OxiddSolveOptionsV2 options = oxidd_solve_options_default_v2();
    options.node_cap = options.cache_cap = 1u << 16;
    options.failure = &failure;
    options.max_artifact_bytes = 1u << 20;
    Gr1CertificateOptionsV2 export = {
        .abi_version = TLSF_GR1_CERTIFICATE_OPTIONS_ABI_VERSION,
        .struct_size = sizeof(Gr1CertificateOptionsV2),
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
    Aig *game = game_new();
    export_calls = 0;
    fail_export_at = injection;
    int unreal = 0;
    Aig *strategy = solve_gr1_oxidd_ex_with_certificate_v2(game, &unreal,
                                                           &options, &export);
    fail_export_at = 0;
    if (injection) {
      assert(!strategy && !unreal && export.failed);
      assert(failure.kind != OXIDD_FAILURE_NONE);
      for (size_t i = 0; i < 4; i++)
        assert(!bytes[i] && !sizes[i]);
    } else {
      assert(strategy && !unreal && !export.failed);
      for (size_t i = 0; i < 4; i++) {
        valid[i] = strdup(bytes[i]);
        valid_sizes[i] = sizes[i];
        assert(valid[i]);
      }
    }
    aig_free(strategy);
    for (size_t i = 0; i < 4; i++)
      free(bytes[i]);
  }
  OxiddFailure solver_failure = {0};
  OxiddSolveOptionsV2 solver_options = oxidd_solve_options_default_v2();
  solver_options.node_cap = solver_options.cache_cap = 1u << 16;
  solver_options.failure = &solver_failure;
  realloc_calls = 0;
  fail_realloc_at = 1;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd_ex_v2(game_new(), &unreal, &solver_options);
  fail_realloc_at = 0;
  assert(realloc_calls > 0);
  assert(!strategy && !unreal && solver_failure.kind != OXIDD_FAILURE_NONE);
  TlsfGr1CheckInput input = {
      .game_aag = {(const uint8_t *)game_text, strlen(game_text)},
      .certificate_aag = {(const uint8_t *)valid[0], valid_sizes[0]},
      .certificate_json = {(const uint8_t *)valid[1], valid_sizes[1]},
      .policy_aag = {(const uint8_t *)valid[2], valid_sizes[2]},
      .policy_json = {(const uint8_t *)valid[3], valid_sizes[3]},
  };
  TlsfGr1CheckOptions check_options = {
      .abi_version = TLSF_NATIVE_ABI_VERSION,
      .method = TLSF_GR1_CHECK_CERTIFICATE,
      .node_cap = 1u << 16,
      .cache_cap = 1u << 16,
      .max_artifact_bytes = 1u << 20,
  };
  for (size_t injection = 1; injection <= 2; injection++) {
    malloc_calls = 0;
    fail_malloc_at = injection;
    TlsfGr1CheckResult result;
    TlsfGr1CheckStatus status = tlsf_gr1_check(&input, &check_options, &result);
    fail_malloc_at = 0;
    assert(status == TLSF_GR1_CHECK_LIMIT);
    assert(!result.json && result.verdict != TLSF_GR1_CHECK_VERIFIED);
    tlsf_gr1_check_result_clear(&result);
  }
  export_calls = 0;
  fail_export_at = 1;
  TlsfGr1CheckResult result;
  TlsfGr1CheckStatus status = tlsf_gr1_check(&input, &check_options, &result);
  fail_export_at = 0;
  assert(status == TLSF_GR1_CHECK_LIMIT && !result.json);
  tlsf_gr1_check_result_clear(&result);
  for (size_t i = 0; i < 4; i++)
    free(valid[i]);
}

int main(void) {
  const char source[] =
      "INFO { TITLE: \"small\" DESCRIPTION: \"small\" SEMANTICS: Mealy "
      "TARGET: Mealy }\n"
      "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G b; } }\n";
  TlsfPipelineError error;
  TlsfPipelineOptionsV2 options = {.abi_version =
                                       TLSF_PIPELINE_OPTIONS_ABI_VERSION,
                                   .struct_size = sizeof(TlsfPipelineOptionsV2),
                                   .error = &error};
  fail_malloc = 1;
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes_v2(
      (const uint8_t *)source, strlen(source), &options);
  fail_malloc = 0;
  assert(!pipeline && error.status == TLSF_PIPELINE_LIMIT);

  fail_calloc = 1;
  pipeline = tlsf_pipeline_load_bytes_v2((const uint8_t *)source,
                                         strlen(source), &options);
  fail_calloc = 0;
  assert(!pipeline && error.status == TLSF_PIPELINE_LIMIT);

  TlsfGr1CheckInput input = {
      .game_aag = {(const uint8_t *)"aag", 3},
      .certificate_aag = {(const uint8_t *)"aag", 3},
      .certificate_json = {(const uint8_t *)"{}", 2},
      .policy_aag = {(const uint8_t *)"aag", 3},
      .policy_json = {(const uint8_t *)"{}", 2},
  };
  TlsfGr1CheckOptions check_options = {
      .abi_version = TLSF_NATIVE_ABI_VERSION,
      .method = TLSF_GR1_CHECK_CERTIFICATE,
      .node_cap = 1u << 16,
      .cache_cap = 1u << 16,
      .max_artifact_bytes = 1u << 20,
  };
  TlsfGr1CheckResult result;
  fail_malloc = 1;
  TlsfGr1CheckStatus status = tlsf_gr1_check(&input, &check_options, &result);
  fail_malloc = 0;
  assert(status == TLSF_GR1_CHECK_LIMIT);
  assert(result.json == NULL && result.verdict != TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&result);
  deeper_failures();
}
