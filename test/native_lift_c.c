#include "tlsf/gr1_lift.h"
#include <assert.h>
#include <string.h>
static int cancelled(void *ctx) { (void)ctx; return 1; }
int main(void) {
  static const char source[] =
      "INFO { TITLE: \"x\" DESCRIPTION: \"x\" SEMANTICS: Mealy TARGET: Mealy }\n"
      "GLOBAL { PARAMETERS { n = 5; } }\n"
      "MAIN { INPUTS { a[n]; } OUTPUTS { b[n]; } GUARANTEES { G F b[0]; } }\n";
  TlsfGr1LiftOptions options = {0};
  options.abi_version = TLSF_GR1_LIFT_ABI_VERSION;
  options.struct_size = sizeof options;
  options.cancelled = cancelled;
  TlsfGr1LiftResult result = {0};
  TlsfGr1LiftError error = {0};
  assert(tlsf_gr1_lift_v1((const uint8_t *)source, strlen(source),
                          NULL, 0, &options, &result, &error) == TLSF_GR1_LIFT_CANCELLED);
  assert(result.game_aag == NULL && result.certificate_aag == NULL);
  tlsf_gr1_lift_result_clear(&result);
  return 0;
}
