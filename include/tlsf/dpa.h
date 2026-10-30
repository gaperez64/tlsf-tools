#ifndef TLSF_DPA_H
#define TLSF_DPA_H
#include "tlsf/ast_api.h"
#include <stddef.h>
#ifdef __cplusplus
extern "C" {
#endif

typedef struct TlsfDpa TlsfDpa;
typedef uint32_t TlsfDpaState;
typedef uint32_t TlsfDpaLabel;
typedef enum {
  TLSF_DPA_OK,
  TLSF_DPA_DECLINED,
  TLSF_DPA_INVALID,
  TLSF_DPA_INTERNAL
} TlsfDpaCode;
typedef enum {
  TLSF_DPA_NONE,
  TLSF_DPA_UNSUPPORTED,
  TLSF_DPA_STATE_LIMIT,
  TLSF_DPA_HOST_LIMIT,
  TLSF_DPA_BDD_LIMIT,
  TLSF_DPA_DEADLINE,
  TLSF_DPA_CANCELLED,
  TLSF_DPA_PRIORITY_LIMIT
} TlsfDpaReason;
typedef struct {
  TlsfDpaCode code;
  TlsfDpaReason reason;
} TlsfDpaStatus;
typedef struct {
  size_t max_states,
      max_host_bytes;          // zero: unlimited; includes scratch storage
  size_t bdd_nodes, bdd_cache; // zero: bounded library defaults
  uint64_t deadline_mono_ns;   // absolute CLOCK_MONOTONIC, zero: none
  const volatile bool *cancel; // borrowed until free; one caller per context
  int (*cancelled)(void *);    // may load an atomic flag
  void *cancel_ctx;
} TlsfDpaBudget;
typedef struct {
  TlsfDpaLabel label;
  TlsfDpaState successor;
  uint32_t priority; // max-odd: largest infinitely recurring priority is odd
} TlsfDpaEdge;
typedef enum {
  TLSF_DPA_FALSE,
  TLSF_DPA_TRUE,
  TLSF_DPA_DECISION
} TlsfDpaLabelKind;
typedef struct {
  TlsfDpaLabelKind kind;
  uint32_t ap;
  TlsfDpaLabel low, high;
} TlsfDpaLabelNode;

// Infinite-word ground AST only. The conversion API rejects finite semantics.
// Copies the AST and partition (inputs first, including unused declarations).
// Stage 1 admits syntactic safety/co-safety, GF finite-window formulas and
// their complements. Everything else declines. Failure always sets *out=NULL.
// Syntax depth above 256 declines; recursive symbolic work is capped at 512
// frames (host limit). BDD nodes/cache are separate from C host-byte
// accounting. Deadlines/cancellation are cooperative between individual FFI
// operations.
TlsfDpaStatus tlsf_dpa_create(const TlsfAstNode *root,
                              const char *const *inputs, uint32_t n_inputs,
                              const char *const *outputs, uint32_t n_outputs,
                              const TlsfDpaBudget *budget, TlsfDpa **out);
void tlsf_dpa_free(TlsfDpa *ctx); // accepts NULL, including after any decline
TlsfDpaStatus tlsf_dpa_status(const TlsfDpa *ctx);
TlsfDpaState tlsf_dpa_initial(const TlsfDpa *ctx);
uint32_t tlsf_dpa_ap_count(const TlsfDpa *ctx);
const char *tlsf_dpa_ap_name(const TlsfDpa *ctx, uint32_t ap);
uint32_t tlsf_dpa_max_priority(const TlsfDpa *ctx);
size_t tlsf_dpa_state_count(const TlsfDpa *ctx);
// Whole nonempty, disjoint row covering true, or *edges=NULL,*count=0.
// IDs never move or recycle. Rows/names/nodes remain borrowed until free.
// A failed expansion permanently declines the context; previous rows remain
// inspectable, but consumers must abandon the entire attempt.
TlsfDpaStatus tlsf_dpa_successors(TlsfDpa *ctx, TlsfDpaState state,
                                  const TlsfDpaEdge **edges, size_t *count);
const TlsfDpaLabelNode *tlsf_dpa_label_node(const TlsfDpa *ctx,
                                            TlsfDpaLabel label);
// Full reachable expansion, using the same successor API. Success alone
// certifies completion; decline never provides a partial automaton answer.
TlsfDpaStatus tlsf_dpa_expand(TlsfDpa *ctx);
#ifdef __cplusplus
}
#endif
#endif
