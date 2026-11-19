#include "tlsf/gr1_lift.h"
#include "../check.h"
#include <string.h>
static int cancelled(void *ctx) {
  (void)ctx;
  return 1;
}
int main(void) {
  static const char source[] =
      "INFO { TITLE: \"x\" DESCRIPTION: \"x\" SEMANTICS: Mealy TARGET: Mealy "
      "}\n"
      "GLOBAL { PARAMETERS { n = 5; } }\n"
      "MAIN { INPUTS { a[n]; } OUTPUTS { b[n]; } GUARANTEES { G F b[0]; } }\n";
  TlsfGr1LiftOptions options = {0};

  options.cancelled = cancelled;
  TlsfGr1LiftResult result = {0};
  TlsfGr1LiftError error = {0};
  CHECK(tlsf_gr1_lift((const uint8_t *)source, strlen(source), NULL, 0,
                      &options, &result, &error) == TLSF_GR1_LIFT_CANCELLED);
  CHECK(result.game_aag == NULL && result.certificate_aag == NULL);
  tlsf_gr1_lift_result_clear(&result);
  options.cancelled = NULL;
  options.phase_budget.max_seed_probes = 1;
  CHECK(tlsf_gr1_lift((const uint8_t *)source, strlen(source), NULL, 0,
                      &options, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(strstr(result.decline_detail, "n[2]=probe_failure"));
  CHECK(strstr(result.decline_detail, "probe_budget_exhausted"));
  CHECK(sizeof result.decline_detail == TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE);
  tlsf_gr1_lift_result_clear(&result);
  CHECK(result.decline_detail[0] == '\0');
  TlsfGr1BothResult both = {0};
  CHECK(sizeof both.decline_detail == sizeof result.decline_detail);
  strcpy(both.decline_detail, "n[2]=probe_budget_exhausted");
  tlsf_gr1_both_result_clear(&both);
  CHECK(both.decline_detail[0] == '\0');
  return 0;
}
