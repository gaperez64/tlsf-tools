#include "tlsf/gr.h"

// ===========================================================================
// Generalized Reactivity GR(k) recognition.
//
// A spec is in the GR fragment when every section conjunct is one of:
//   - init      θ : a propositional formula;
//   - safety    G ρ : G of a transition predicate (Boolean over current and
//                     single-next signal values);
//   - justice   G F J : "infinitely often" a Boolean; or
//   - a Streett pair  (⋀ G F P) -> (⋀ G F Q)  /  (⋀ G F P) <-> (⋀ G F Q)
//     on the system (guarantee) side.
//
// The level k is the number of *distinct* effective antecedent sets among the
// system liveness conjuncts, where the effective antecedent of a conjunct is
// (the global assumption justices) ∪ (its own G F antecedents); a plain
// justice has the global assumptions as its antecedent.  k = 0 (GR(0)) when
// there is no system liveness at all.  Returns -1 outside the fragment.
// ===========================================================================

#define GR_MAX 64

typedef struct {
  const Node *items[GR_MAX];
  int count;
} GFSet;

// ---------------------------------------------------------------------------
// Structural formula equality (atoms are interned, so compared by pointer)
// ---------------------------------------------------------------------------

static bool node_eq(const Node *a, const Node *b) {
  if (a == b)
    return true;
  if (a->kind != b->kind)
    return false;
  switch (a->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_AP:
    return a->name == b->name;
  case NODE_INT:
    return a->ival == b->ival;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return node_eq(a->arg, b->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return node_eq(a->lhs, b->lhs) && node_eq(a->rhs, b->rhs);
  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// Boolean / transition tests
// ---------------------------------------------------------------------------

static bool is_prop(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return is_prop(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return is_prop(n->lhs) && is_prop(n->rhs);
  default:
    return false;
  }
}

static bool is_trans(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return is_trans(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return is_trans(n->lhs) && is_trans(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    return is_prop(n->arg);
  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// GF-set helpers
// ---------------------------------------------------------------------------

// If n is `G F b`, return b; otherwise nullptr.
static const Node *as_justice(const Node *n) {
  if (n->kind == NODE_G && n->arg->kind == NODE_F)
    return n->arg->arg;
  return nullptr;
}

static bool gfset_add(GFSet *s, const Node *inner) {
  for (int i = 0; i < s->count; i++)
    if (node_eq(s->items[i], inner))
      return true; // already present
  if (s->count >= GR_MAX)
    return false;
  s->items[s->count++] = inner;
  return true;
}

// Collect the inner formulas of a conjunction of justice conditions
// (G F b1 ∧ G F b2 ∧ ...) into `dst`.  Returns false if any leaf is not a
// justice condition.
static bool collect_justice_conj(const Node *n, GFSet *dst) {
  if (n->kind == NODE_AND)
    return collect_justice_conj(n->lhs, dst) &&
           collect_justice_conj(n->rhs, dst);
  const Node *inner = as_justice(n);
  if (!inner || !is_trans(inner))
    return false;
  return gfset_add(dst, inner);
}

static bool gfset_eq(const GFSet *a, const GFSet *b) {
  if (a->count != b->count)
    return false;
  for (int i = 0; i < a->count; i++) {
    bool found = false;
    for (int j = 0; j < b->count && !found; j++)
      found = node_eq(a->items[i], b->items[j]);
    if (!found)
      return false;
  }
  return true;
}

// ===========================================================================
// Analysis
// ===========================================================================

typedef struct {
  GFSet global;          // assumption justices (A_global)
  GFSet antecedents[GR_MAX]; // distinct system antecedent sets
  int n_antecedents;
  bool overflow;
} GrCtx;

static void add_antecedent(GrCtx *c, const GFSet *ant) {
  for (int i = 0; i < c->n_antecedents; i++)
    if (gfset_eq(&c->antecedents[i], ant))
      return;
  if (c->n_antecedents >= GR_MAX) {
    c->overflow = true;
    return;
  }
  c->antecedents[c->n_antecedents++] = *ant;
}

// Effective antecedent set = global ∪ extra.
static GFSet effective(const GrCtx *c, const GFSet *extra) {
  GFSet s = c->global;
  if (extra)
    for (int i = 0; i < extra->count; i++)
      gfset_add(&s, extra->items[i]);
  return s;
}

// Process one assumption-side conjunct (no implicit G).  Adds justices to the
// global set.  Returns false outside the fragment.
static bool assume_conjunct(GrCtx *c, const Node *n) {
  if (is_prop(n))
    return true; // initial
  if (n->kind == NODE_G) {
    const Node *inner = as_justice(n);
    if (inner && is_trans(inner))
      return gfset_add(&c->global, inner); // G F b
    if (is_trans(n->arg))
      return true; // G ρ safety
  }
  return false;
}

// Process one invariant conjunct (REQUIRE/ASSERT): the formula n stands for
// G n.  `system` selects whether a justice is a system consequent or a global
// assumption.
static bool invariant_conjunct(GrCtx *c, const Node *n, bool system) {
  if (is_trans(n))
    return true; // G(transition) safety

  const Node *just = nullptr;
  if (n->kind == NODE_F && is_trans(n->arg)) {
    just = n->arg; // G F b  (from F b under the implicit G)
  } else if (n->kind == NODE_G) {
    const Node *gj = as_justice(n); // n written as G(F b)
    if (gj && is_trans(gj))
      just = gj;
    else if (is_trans(n->arg))
      return true; // G(transition) safety
    else
      return false;
  }

  if (!just)
    return false;
  if (system) {
    GFSet ant = effective(c, nullptr);
    add_antecedent(c, &ant);
  } else {
    return gfset_add(&c->global, just);
  }
  return true;
}

// Process one system (guarantee) conjunct.  Returns false outside fragment.
static bool guarantee_conjunct(GrCtx *c, const Node *n) {
  if (is_prop(n))
    return true; // initial
  if (n->kind == NODE_G) {
    const Node *inner = as_justice(n);
    if (inner && is_trans(inner)) {
      GFSet ant = effective(c, nullptr); // plain justice
      add_antecedent(c, &ant);
      return true;
    }
    if (is_trans(n->arg))
      return true; // safety
    return false;
  }
  if (n->kind == NODE_IMPL || n->kind == NODE_EQUIV) {
    GFSet lhs = {0}, rhs = {0};
    if (!collect_justice_conj(n->lhs, &lhs) ||
        !collect_justice_conj(n->rhs, &rhs))
      return false;
    GFSet a1 = effective(c, &lhs);
    add_antecedent(c, &a1);
    if (n->kind == NODE_EQUIV) {
      GFSet a2 = effective(c, &rhs); // both directions
      add_antecedent(c, &a2);
    }
    return true;
  }
  return false;
}

// ---------------------------------------------------------------------------

// Apply `fn` to each conjunct of a formula (flattening top-level ∧).
static bool each_conjunct(const Node *n, GrCtx *c,
                          bool (*fn)(GrCtx *, const Node *)) {
  if (n->kind == NODE_AND)
    return each_conjunct(n->lhs, c, fn) && each_conjunct(n->rhs, c, fn);
  return fn(c, n);
}

// Conjunct wrappers (the function-pointer signature is GrCtx*, const Node*).
static bool require_conjunct(GrCtx *c, const Node *n) {
  return invariant_conjunct(c, n, /*system=*/false);
}
static bool assert_conjunct(GrCtx *c, const Node *n) {
  return invariant_conjunct(c, n, /*system=*/true);
}
static bool initial_conjunct(GrCtx *c, const Node *n) {
  (void)c;
  return is_prop(n);
}

static bool process_list(const FormulaList *l, GrCtx *c,
                         bool (*fn)(GrCtx *, const Node *)) {
  for (uint32_t i = 0; i < l->count; i++)
    if (!each_conjunct(l->formulas[i], c, fn))
      return false;
  return true;
}

int gr_level(const TlsfSpec *spec) {
  GrCtx c = {0};

  // Pass 1: assumption side — collect the global justices and validate.
  if (!process_list(&spec->initially, &c, initial_conjunct) ||
      !process_list(&spec->assume, &c, assume_conjunct) ||
      !process_list(&spec->require, &c, require_conjunct))
    return -1;

  // Pass 2: system side — validate and collect distinct antecedent sets.
  if (!process_list(&spec->preset, &c, initial_conjunct) ||
      !process_list(&spec->guarantee, &c, guarantee_conjunct) ||
      !process_list(&spec->assert_, &c, assert_conjunct))
    return -1;

  if (c.overflow)
    return -1; // too complex for our fixed-size analysis

  // k = number of distinct system antecedent sets; 0 means GR(0).
  return c.n_antecedents;
}
