#ifndef TLSF_AST_H
#define TLSF_AST_H

/// ast.h — LTL formula AST.
///
/// All nodes are arena-allocated.  The tagged union uses a flat layout:
/// unary nodes use `.arg`, binary nodes use `.lhs`/`.rhs`.
///
/// Operator taxonomy (after NNF):
///   Safety-compatible :  X, G, R (release), W (weak until)
///   Liveness          :  F, U (until), M (strong release / dual of W)
///
/// Pre-expansion nodes (not present after expand()):
///   NODE_DEF_CALL, NODE_BUS_INDEX, NODE_PATTERN

#include "tlsf/arena.h"
#include <stdbool.h>
#include <stdint.h>

// ---------------------------------------------------------------------------
// Node kind enumeration
// ---------------------------------------------------------------------------

typedef enum NodeKind {
  // -- Atoms --
  NODE_TRUE,  ///< boolean true
  NODE_FALSE, ///< boolean false
  NODE_AP,    ///< atomic proposition (interned identifier string)

  // -- Integer atoms (appear in parameter expressions before expansion) --
  NODE_INT, ///< integer literal

  // -- Boolean connectives --
  NODE_NOT,   ///< ¬φ
  NODE_AND,   ///< φ ∧ ψ
  NODE_OR,    ///< φ ∨ ψ
  NODE_IMPL,  ///< φ → ψ
  NODE_EQUIV, ///< φ ↔ ψ

  // -- LTL: safety-compatible (NNF duals of liveness operators) --
  NODE_X, ///< Xφ  (next)
  NODE_G, ///< Gφ  (globally)
  NODE_R, ///< φ R ψ  (release — dual of U)
  NODE_W, ///< φ W ψ  (weak until — dual of M)

  // -- LTL: liveness --
  NODE_F, ///< Fφ  (finally / eventually)
  NODE_U, ///< φ U ψ  (until)
  NODE_M, ///< φ M ψ  (strong release — dual of W)

  // -- LTLf only (TLSF v1.2) --
  NODE_X_STRONG, ///< X[!]φ  (strong next — defined only for finite semantics)

  // -- Pre-expansion only: not present after expand() --
  NODE_DEF_CALL,  ///< identifier([args])  — definition/function call
  NODE_BUS_INDEX, ///< name[expr]          — bus signal indexing
  NODE_PATTERN,   ///< pattern(name, args) — high-level pattern instantiation

  // -- Integer expressions (pre-expansion) --
  NODE_INT_ADD, ///< e + e
  NODE_INT_SUB, ///< e - e
  NODE_INT_MUL, ///< e * e
  NODE_INT_DIV, ///< e / e
  NODE_INT_MOD, ///< e % e
  NODE_INT_NEG, ///< -e
  NODE_INT_VAR, ///< integer variable reference (interned name)
  NODE_SIZEOF,  ///< SIZEOF bus — bus width (hi-lo+1), resolved during expand

  // -- Comparisons (in definition guards; evaluated to a bool during expand) --
  NODE_CMP_EQ, ///< e == e
  NODE_CMP_NE, ///< e != e
  NODE_CMP_LT, ///< e < e
  NODE_CMP_LE, ///< e <= e
  NODE_CMP_GT, ///< e > e
  NODE_CMP_GE, ///< e >= e

  // -- Definition cases:  cond : value  ...  (right-nested, resolved at expand)
  NODE_ITE, ///< if cond then if_then else if_else

  // -- Indexed next:  X[count] body  — count-fold next, resolved at expand
  NODE_NEXT_N, ///< lhs = count expression, rhs = body

  // -- Bounded temporal:  G[lo:hi] body / F[lo:hi] body  (resolved at expand
  //    into a conjunction/disjunction of X^k body for k in [lo,hi]).
  NODE_G_RANGE, ///< qlo = lo, qhi = hi, qbody = body
  NODE_F_RANGE, ///< qlo = lo, qhi = hi, qbody = body

  // -- Set expressions (pre-expansion) --
  NODE_SET,      ///< { e, e, ... }  — set literal (children = elements)
  NODE_SET_ENUM, ///< set comprehension: { x : range }
  NODE_FORALL,   ///< bounded big-conjunction  &&[lo <|<= v <|<= hi] body
  NODE_EXISTS,   ///< bounded big-disjunction   ||[lo <|<= v <|<= hi] body

  NODE_KIND_COUNT, ///< sentinel — keep last
} NodeKind;

// ---------------------------------------------------------------------------
// Node structure
// ---------------------------------------------------------------------------

typedef struct Node Node;

typedef enum BoundedTemporalOrigin {
  BOUNDED_NONE,
  BOUNDED_NEXT,
  BOUNDED_G_RANGE,
  BOUNDED_F_RANGE,
} BoundedTemporalOrigin;

typedef struct {
  BoundedTemporalOrigin origin;
  int64_t lo;
  int64_t hi;
  Node *body;
} BoundedTemporalMeta;

struct Node {
  NodeKind kind;

  union {
    // NODE_AP, NODE_INT_VAR, NODE_DEF_CALL (callee name before arg list)
    const char *name; ///< interned string pointer

    // NODE_INT
    int64_t ival;

    // Unary: NODE_NOT, NODE_X, NODE_X_STRONG, NODE_F, NODE_G, NODE_INT_NEG
    struct {
      Node *arg;
    };

    // Binary LTL / boolean / integer arithmetic
    struct {
      Node *lhs;
      Node *rhs;
    };

    // NODE_DEF_CALL / NODE_PATTERN: callee + argument list
    struct {
      const char *callee; ///< interned function/pattern name
      Node **call_args;   ///< arena-allocated array of argument nodes
      uint16_t call_argc; ///< argument count
    };

    // NODE_BUS_INDEX: signal name + index expression
    struct {
      const char *bus_name; ///< interned signal name
      Node *bus_index;      ///< index expression (integer)
    };

    // NODE_SIZEOF: bus name whose width is requested
    struct {
      const char *sizeof_name; ///< interned bus name
    };

    // NODE_ITE: if-then-else (definition guard chain)
    struct {
      Node *if_cond;
      Node *if_then;
      Node *if_else;
    };

    // NODE_FORALL / NODE_EXISTS: bounded quantifier
    //   &&[ qlo (<|<=) qvar (<|<=) qhi ] qbody
    struct {
      const char *qvar; ///< interned bound-variable name
      Node *qlo;        ///< lower-bound integer expression
      Node *qhi;        ///< upper-bound integer expression
      Node *qbody;      ///< quantified formula
      bool qlo_strict;  ///< true if the lower relation is '<' (else '<=')
      bool qhi_strict;  ///< true if the upper relation is '<' (else '<=')
    };

    // NODE_SET / NODE_SET_ENUM
    struct {
      Node **set_elems;  ///< arena-allocated array of child nodes
      uint16_t set_size; ///< element / child count
    };
  };

  // Expansion metadata for compact backends: the node is still ordinary LTL,
  // but it remembers that it came from X[k], G[lo:hi], or F[lo:hi].
  BoundedTemporalMeta bounded;
};

// ---------------------------------------------------------------------------
// Node constructors (all allocate from arena, return nullptr on OOM)
// ---------------------------------------------------------------------------

[[nodiscard]] Node *node_true(Arena *a);
[[nodiscard]] Node *node_false(Arena *a);
[[nodiscard]] Node *node_ap(Arena *a, const char *interned_name);
[[nodiscard]] Node *node_int(Arena *a, int64_t val);

[[nodiscard]] Node *node_not(Arena *a, Node *arg);
[[nodiscard]] Node *node_and(Arena *a, Node *lhs, Node *rhs);
[[nodiscard]] Node *node_or(Arena *a, Node *lhs, Node *rhs);
[[nodiscard]] Node *node_impl(Arena *a, Node *lhs, Node *rhs);
[[nodiscard]] Node *node_equiv(Arena *a, Node *lhs, Node *rhs);

[[nodiscard]] Node *node_x(Arena *a, Node *arg);
[[nodiscard]] Node *node_x_strong(Arena *a, Node *arg);
[[nodiscard]] Node *node_next_n(Arena *a, Node *count, Node *body);
[[nodiscard]] Node *node_g_range(Arena *a, Node *lo, Node *hi, Node *body);
[[nodiscard]] Node *node_f_range(Arena *a, Node *lo, Node *hi, Node *body);
[[nodiscard]] Node *node_f(Arena *a, Node *arg);
[[nodiscard]] Node *node_g(Arena *a, Node *arg);
[[nodiscard]] Node *node_u(Arena *a, Node *lhs, Node *rhs);
[[nodiscard]] Node *node_r(Arena *a, Node *lhs, Node *rhs);
[[nodiscard]] Node *node_w(Arena *a, Node *lhs, Node *rhs);
[[nodiscard]] Node *node_m(Arena *a, Node *lhs, Node *rhs);

void node_set_bounded(Node *n, BoundedTemporalOrigin origin, int64_t lo,
                      int64_t hi, Node *body);
void node_copy_bounded(Node *dst, const Node *src);

// ---------------------------------------------------------------------------
// Node predicates
// ---------------------------------------------------------------------------

/// True for operators that are safety-compatible (no liveness modality).
static inline bool node_kind_is_safety(NodeKind k) {
  return k != NODE_F && k != NODE_U && k != NODE_M;
}

/// True for temporal operators (any LTL modality).
static inline bool node_kind_is_temporal(NodeKind k) {
  return k == NODE_X || k == NODE_X_STRONG || k == NODE_F || k == NODE_G ||
         k == NODE_U || k == NODE_R || k == NODE_W || k == NODE_M;
}

/// True for pre-expansion nodes that must not appear after expand().
static inline bool node_kind_is_high_level(NodeKind k) {
  return k == NODE_DEF_CALL || k == NODE_BUS_INDEX || k == NODE_PATTERN ||
         k == NODE_INT_VAR || k == NODE_SIZEOF || k == NODE_ITE ||
         k == NODE_NEXT_N || k == NODE_G_RANGE || k == NODE_F_RANGE ||
         (k >= NODE_CMP_EQ && k <= NODE_CMP_GE) || k == NODE_SET ||
         k == NODE_SET_ENUM || k == NODE_FORALL || k == NODE_EXISTS;
}

#endif // TLSF_AST_H
