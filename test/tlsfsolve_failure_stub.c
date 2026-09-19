#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"

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
