#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"

Aig *solve_safety_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  aig_free(game);
  return nullptr;
}

Aig *solve_gr1_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  aig_free(game);
  return nullptr;
}
