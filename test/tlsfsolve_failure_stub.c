#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"

OxiddSolveResult solve_safety_oxidd_result(Aig *game,
                                           const OxiddSolveOptions *opts) {
  if (opts && opts->failure)
    *opts->failure = (OxiddFailure){OXIDD_FAILURE_BDD, "construction", "and",
                                    42, 7};
  aig_free(game);
  return (OxiddSolveResult){.status = OXIDD_SOLVE_ERROR};
}

Aig *solve_safety_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  aig_free(game);
  return nullptr;
}

Aig *solve_safety_oxidd_ex(Aig *game, int *unreal,
                           const OxiddSolveOptions *opts) {
  (void)opts;
  return solve_safety_oxidd(game, unreal);
}

Aig *solve_gr1_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  aig_free(game);
  return nullptr;
}

Aig *solve_gr1_oxidd_ex(Aig *game, int *unreal, const OxiddSolveOptions *opts) {
  (void)opts;
  return solve_gr1_oxidd(game, unreal);
}

Aig *solve_gr1_oxidd_with_certificate(Aig *game, int *unreal,
                                      Gr1CertificateOptions *certificate) {
  (void)certificate;
  return solve_gr1_oxidd(game, unreal);
}

Aig *solve_gr1_oxidd_ex_with_certificate(
    Aig *game, int *unreal, const OxiddSolveOptions *opts,
    Gr1CertificateOptions *certificate) {
  (void)opts;
  (void)certificate;
  return solve_gr1_oxidd(game, unreal);
}
