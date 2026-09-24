#include "tlsf/gr1_oxidd.h"

#include <stdio.h>

bool tlsf_gr1_validate_game(const Aig *game, char *message, size_t capacity) {
  if (!game) {
    if (message && capacity)
      snprintf(message, capacity, "null game");
    return false;
  }
  if (aig_num_constraints(game) || !aig_num_justice(game)) {
    if (message && capacity)
      snprintf(message, capacity,
               "GR(1) requires justice and no invariant constraints");
    return false;
  }
  for (uint32_t j = 0; j < aig_num_justice(game); j++) {
    uint32_t members = 0;
    aig_justice_at(game, j, nullptr, &members);
    if (members != 1) {
      if (message && capacity)
        snprintf(message, capacity, "justice record %u is not singleton", j);
      return false;
    }
  }
  for (uint32_t j = 0; j < aig_num_latches(game); j++) {
    uint32_t reset;
    aig_latch_at(game, j, nullptr, nullptr, &reset);
    if (reset > 1) {
      if (message && capacity)
        snprintf(message, capacity, "latch %u has nonconstant reset", j);
      return false;
    }
  }
  if (message && capacity)
    message[0] = '\0';
  return true;
}
