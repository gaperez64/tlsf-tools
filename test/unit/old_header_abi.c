/* This translation unit sees only the headers copied from before phase-stats.
 */
#include "tlsf/gr1_lift.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/gr1_reduction.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#define CHECK(test)                                                            \
  do {                                                                         \
    if (!(test)) {                                                             \
      fprintf(stderr, "old ABI check failed at %d: %s\n", __LINE__, #test);    \
      abort();                                                                 \
    }                                                                          \
  } while (0)

static const char source[] = "INFO { TITLE: \"ABI\" DESCRIPTION: \"ABI\" "
                             "SEMANTICS: Mealy TARGET: Mealy }\n"
                             "MAIN { INPUTS { i; } OUTPUTS { o; } "
                             "GUARANTEE { G (i -> o); G F o; } }\n";

static const char param_source[] =
    "INFO { TITLE: \"ABI lift\" DESCRIPTION: \"ABI lift\" SEMANTICS: Mealy "
    "TARGET: Mealy }\n"
    "GLOBAL { PARAMETERS { extent = 5; } }\n"
    "MAIN { INPUTS { demand[extent]; } OUTPUTS { response[extent]; } "
    "GUARANTEES { &&[0 <= i < extent] G F response[i]; } }\n";

static void *guarded_copy(const void *source_bytes, size_t size,
                          void **mapping) {
  const size_t page = (size_t)sysconf(_SC_PAGESIZE);
  CHECK(page > size);
  *mapping = mmap(NULL, page * 2, PROT_READ | PROT_WRITE,
                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  CHECK(*mapping != MAP_FAILED);
  CHECK(mprotect((char *)*mapping + page, page, PROT_NONE) == 0);
  void *layout = (char *)*mapping + page - size;
  memcpy(layout, source_bytes, size);
  return layout;
}
static void unguard(void *mapping) {
  CHECK(munmap(mapping, (size_t)sysconf(_SC_PAGESIZE) * 2) == 0);
}

/* Built in a separate translation unit against the new public headers. */
extern void run_new_controls(const char *, size_t, const char *, size_t);

int main(void) {
  void *mapping = NULL;
  TlsfGr1LiftOptions lift_options = {0};
  const TlsfGr1LiftOptions *old_lift =
      guarded_copy(&lift_options, sizeof lift_options, &mapping);
  TlsfGr1LiftResult lift_result = {0};
  TlsfGr1LiftError lift_error = {0};
  CHECK(tlsf_gr1_lift((const uint8_t *)source, strlen(source), NULL, 0,
                      old_lift, &lift_result,
                      &lift_error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(strcmp(lift_error.stage, "parameters") == 0);
  CHECK(lift_result.game_aag == NULL);
  TlsfGr1LiftStatus lift_status =
      tlsf_gr1_lift((const uint8_t *)param_source, strlen(param_source), NULL,
                    0, old_lift, &lift_result, &lift_error);
  if (lift_status != TLSF_GR1_LIFT_OK)
    fprintf(stderr, "old lift status=%d stage=%s message=%s\n", lift_status,
            lift_error.stage, lift_error.message);
  CHECK(lift_status == TLSF_GR1_LIFT_OK);
  CHECK(lift_result.verdict == TLSF_GR1_CHECK_VERIFIED);
  CHECK(lift_result.game_aag && lift_result.certificate_aag &&
        lift_result.policy_aag);
  tlsf_gr1_lift_result_clear(&lift_result);
  unguard(mapping);

  TlsfPipelineError load_error = {0};
  TlsfPipelineOptions load_options = {0};
  load_options.certify = true;
  load_options.template_mask = TPL_ALL;
  load_options.error = &load_error;
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes(
      (const uint8_t *)source, strlen(source), &load_options);
  CHECK(pipeline != NULL);
  TlsfGr1ReductionOptions reduction_options = {0};
  reduction_options.semantics = TLSF_GR1_EXACT;
  reduction_options.max_artifact_bytes = 1u << 20;
  reduction_options.max_monitor_states = 100;
  const TlsfGr1ReductionOptions *old_reduction =
      guarded_copy(&reduction_options, sizeof reduction_options, &mapping);
  TlsfGr1Reduction reduction = {0};
  TlsfGr1ReductionError reduction_error = {0};
  CHECK(tlsf_gr1_reduce(pipeline, old_reduction, &reduction,
                        &reduction_error) == TLSF_GR1_REDUCE_OK);
  CHECK(reduction.game != NULL && reduction.aag != NULL && reduction.aag_size);
  unguard(mapping);

  char *cert = NULL, *cert_json = NULL, *policy = NULL, *policy_json = NULL;
  size_t cert_size = 0, cert_json_size = 0, policy_size = 0,
         policy_json_size = 0;
  Gr1CertificateOptions certificate = {0};
  certificate.semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
  certificate.aag_bytes = &cert;
  certificate.json_bytes = &cert_json;
  certificate.policy_aag_bytes = &policy;
  certificate.policy_json_bytes = &policy_json;
  certificate.aag_size = &cert_size;
  certificate.json_size = &cert_json_size;
  certificate.policy_aag_size = &policy_size;
  certificate.policy_json_size = &policy_json_size;
  certificate.max_artifact_bytes = 1u << 20;
  Gr1CertificateOptions *old_certificate =
      guarded_copy(&certificate, sizeof certificate, &mapping);
  OxiddSolveOptions solver = oxidd_solve_options_default();
  solver.node_cap = solver.cache_cap = 1u << 16;
  solver.max_artifact_bytes = 1u << 20;
  int unreal = 0;
  Aig *game = reduction.game;
  reduction.game = NULL;
  Aig *strategy = solve_gr1_oxidd_ex_with_certificate(game, &unreal, &solver,
                                                      old_certificate);
  CHECK(strategy != NULL && !unreal && !old_certificate->failed);
  CHECK(cert && cert_json && policy && policy_json);
  CHECK(cert_size && cert_json_size && policy_size && policy_json_size);
  aig_free(strategy);
  unguard(mapping);

  TlsfGr1CheckInput check_input = {0};
  check_input.game_aag =
      (TlsfGr1Bytes){(const uint8_t *)reduction.aag, reduction.aag_size};
  check_input.certificate_aag =
      (TlsfGr1Bytes){(const uint8_t *)cert, cert_size};
  check_input.certificate_json =
      (TlsfGr1Bytes){(const uint8_t *)cert_json, cert_json_size};
  check_input.policy_aag = (TlsfGr1Bytes){(const uint8_t *)policy, policy_size};
  check_input.policy_json =
      (TlsfGr1Bytes){(const uint8_t *)policy_json, policy_json_size};
  TlsfGr1CheckOptions check_options = {0};
  check_options.method = TLSF_GR1_CHECK_CERTIFICATE;
  check_options.node_cap = check_options.cache_cap = 1u << 16;
  check_options.max_artifact_bytes = 1u << 20;
  const TlsfGr1CheckOptions *old_check =
      guarded_copy(&check_options, sizeof check_options, &mapping);
  TlsfGr1CheckResult checked = {0};
  CHECK(tlsf_gr1_check(&check_input, old_check, &checked) == TLSF_GR1_CHECK_OK);
  CHECK(checked.verdict == TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&checked);
  unguard(mapping);
  tlsf_gr1_reduction_clear(&reduction);
  tlsf_pipeline_free(pipeline);
  free(cert);
  free(cert_json);
  free(policy);
  free(policy_json);
  run_new_controls(source, strlen(source), param_source, strlen(param_source));
  return 0;
}
