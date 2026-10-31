#ifndef TLSF_DPA_INTERNAL_H
#define TLSF_DPA_INTERNAL_H
#include "tlsf/dpa.h"
#include "oxidd_common.h"
#include "oxidd_runtime.h"
#include <stdlib.h>
#include <limits.h>

#define DPA_BAD UINT32_MAX
enum {
  DPA_FINITE = 1,
  DPA_SAFETY = 2,
  DPA_COSAFETY = 4,
  DPA_PI2 = 8,
  DPA_SIGMA2 = 16,
  DPA_ALL = 31
};
typedef struct {
  uint64_t hash;
  uint32_t next;
} DpaKey;
typedef struct {
  void **items;
  uint32_t *buckets;
  uint32_t n, cap, bins;
} DpaTable;
typedef struct DpaAllocation DpaAllocation;
typedef struct {
  DpaKey key;
  Bdd bdd;
  uint32_t unfold, step, dag, remainder, label, dual, acceptance;
  uint32_t var, low, high;
  unsigned tags, quick_low, quick_high;
  unsigned char flat[2]; // cached q/r membership: 0 unknown, 1 no, 2 yes
  TlsfDpaLabelNode description;
  uint64_t epoch;
  uint32_t mapped;
} DpaClass;
typedef struct {
  DpaKey key;
  TlsfAstKind op;
  uint32_t lhs, rhs, cls, dual, factored;
  unsigned tags;
  uint64_t epoch;
} DpaTerm;
typedef struct {
  DpaKey key;
  TlsfAstKind op;
  uint32_t lhs, rhs, cls; // modal operands are owned syntax IDs
  unsigned tags;
  bool exact_tags;
} DpaAtom;
typedef struct {
  DpaKey key;
  uint32_t tuple, leaf;
  TlsfDpaEdge *edges;
  size_t count;
} DpaState;
typedef struct {
  DpaKey key;
  uint32_t kind, var, low, high; // 0: class, 1: decision, 2: edge, 3: component
} DpaDag;
typedef struct {
  DpaKey key;
  uint32_t lhs, rhs, dag;
} DpaProduct;
typedef struct {
  DpaKey key;
  const TlsfAstNode *node; // constructor-only traversal memo, never an identity
  bool neg;
  uint32_t formula, next;
} DpaSyntax;
typedef struct {
  DpaKey key;
  uint32_t formula, dual, colour;
} DpaComponent;
typedef struct {
  DpaKey key;
  uint32_t all, rejecting, dag;
} DpaPair;
typedef struct {
  DpaKey key;
  uint32_t values[];
} DpaTuple;
typedef struct {
  DpaKey key;
  uint64_t *colours;
  uint32_t *children, count;
} DpaTreeNode;
typedef struct {
  DpaKey key;
  uint32_t node, parent, position, depth;
} DpaPath;
struct TlsfDpa {
  TlsfDpaStatus status;
  TlsfDpaBudget budget;
  DpaAllocation *allocations;
  size_t bytes;
  oxidd_bdd_manager_t manager;
  DpaTable classes, atoms, terms, states, dags, products, syntax;
  DpaTable components, pairs, tuples, joints, trees, paths, unfolds;
  char **names;
  uint32_t aps, initial, formula_term;
  uint32_t acceptance, root, leftmost, max_priority;
  size_t colour_words;
  bool root_accepts, started;
  uint64_t epoch;
  unsigned recursion;
};

bool dpa_poll(TlsfDpa *c);
bool dpa_enter(TlsfDpa *c);
uint32_t dpa_decline(TlsfDpa *c, TlsfDpaReason reason);
void *dpa_alloc(TlsfDpa *c, size_t count, size_t size);
void dpa_release(TlsfDpa *c, void *ptr);
uint64_t dpa_hash(uint32_t a, uint32_t b, uint32_t d, uint32_t e);
uint32_t dpa_bucket(DpaTable *t, uint64_t hash);
bool dpa_insert(TlsfDpa *c, DpaTable *t, void *item);
uint32_t dpa_class(TlsfDpa *c, Bdd owned);
uint32_t dpa_atom(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b);
uint32_t dpa_boolean(TlsfDpa *c, bool conjunction, uint32_t a, uint32_t b);
uint32_t dpa_ite(TlsfDpa *c, uint32_t v, uint32_t hi, uint32_t lo);
uint32_t dpa_formula(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                     unsigned depth);
unsigned dpa_tags(TlsfDpa *c, uint32_t f);
bool dpa_has_tags(TlsfDpa *c, uint32_t f, unsigned mask);
bool dpa_admitted(TlsfDpa *c, uint32_t f);
bool dpa_children(TlsfDpa *c, uint32_t f);
uint32_t dpa_unfold(TlsfDpa *c, uint32_t f);
uint32_t dpa_step_dag(TlsfDpa *c, uint32_t f);
uint32_t dpa_remainder(TlsfDpa *c, uint32_t f);
uint32_t dpa_dag(TlsfDpa *c, uint32_t kind, uint32_t var, uint32_t lo,
                 uint32_t hi);
uint32_t dpa_product(TlsfDpa *c, uint32_t a, uint32_t r);
uint32_t dpa_state(TlsfDpa *c, uint32_t tuple, uint32_t leaf);
uint32_t dpa_pair(TlsfDpa *c, uint32_t a, uint32_t r);
uint32_t dpa_tuple(TlsfDpa *c, const uint32_t *values);
uint32_t dpa_acceptance(TlsfDpa *c, uint32_t f);
uint32_t dpa_grouped_acceptance(TlsfDpa *c, uint32_t f);
uint32_t dpa_dual(TlsfDpa *c, uint32_t f);
uint32_t dpa_dela_step(TlsfDpa *c, uint32_t tuple, uint32_t leaf);
uint32_t dpa_dela_initial(TlsfDpa *c);
uint32_t dpa_export(TlsfDpa *c, uint32_t f);
void dpa_tree_init(TlsfDpa *c);
uint32_t dpa_tree_step(TlsfDpa *c, uint32_t *leaf, const uint64_t *colours);

static inline bool dpa_colour(const uint64_t *set, uint32_t i) {
  return (set[i / 64] >> (i % 64)) & 1;
}
static inline void dpa_set_colour(uint64_t *set, uint32_t i) {
  set[i / 64] |= UINT64_C(1) << (i % 64);
}
static inline DpaClass *dpa_cls(TlsfDpa *c, uint32_t f) {
  return c->classes.items[f];
}
#endif
