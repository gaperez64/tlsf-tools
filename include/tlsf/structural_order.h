#ifndef TLSF_STRUCTURAL_ORDER_H
#define TLSF_STRUCTURAL_ORDER_H

#include "tlsf/aiger.h"
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
  TLSF_ORDER_INCUMBENT = 0,
  TLSF_ORDER_TYPED_INTERLEAVED,
  TLSF_ORDER_ROLE_GROUPED
} TlsfStructuralOrder;

/* Source-bound frontend records only. Names identify records; they never sort
 * them. Missing/ambiguous typing returns an empty list (incumbent fallback).
 * The order retains separate input/output blocks for MONA's supported layout.
 * Free every returned string and the array with free(). */
int tlsf_structural_ap_order_v1(const uint8_t *source, size_t size,
                                TlsfStructuralOrder order, int lowercase,
                                char ***names, size_t *count);

/* Complete logical-variable permutation: game inputs, latches, then auxiliary
 * counter variables. Missing typed provenance yields identity. This does not
 * renumber the game or any BDD identifier. Caller frees *variables. */
int tlsf_structural_game_order_v1(const Aig *game, const char *provenance,
                                  TlsfStructuralOrder order, uint32_t auxiliary,
                                  uint32_t **variables, size_t *count);

#ifdef __cplusplus
}
#endif
#endif
