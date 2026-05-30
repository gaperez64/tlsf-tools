#include "tlsf/gr.h"

// ===========================================================================
// Generalized Reactivity GR(k) recognition.
//
// Every section conjunct must be one of: an initial condition (propositional),
// a safety invariant (G of a transition predicate), or a liveness condition (a
// Boolean combination of G F / F G literals).  The level k is the number of
// distinct antecedents in the CNF of the liveness implication
//
//     (⋀ assumption liveness)  ->  (⋀ guarantee liveness)
//
// over the GF literals, where F G x is treated as ¬G F ¬x.  The antecedent of
// a CNF clause is the set of GF literals occurring negatively in it; k counts
// the distinct antecedent sets.  k = 0 means GR(0) (no liveness).  Returns -1
// outside the fragment (or if the analysis overflows its fixed limits).
// ===========================================================================

#define GR_ATOMS 64
#define GR_CLAUSES 256

// ---------------------------------------------------------------------------
// Structural equality, propositional / transition tests
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

// G F m or F G m (with m a transition predicate)?
static bool is_livelit_shape(const Node *n) {
  if (n->kind == NODE_G && n->arg->kind == NODE_F)
    return is_trans(n->arg->arg);
  if (n->kind == NODE_F && n->arg->kind == NODE_G)
    return is_trans(n->arg->arg);
  return false;
}

// A Boolean combination whose leaves are all GF/FG literals (or true/false).
static bool is_live_combo(const Node *n) {
  if (is_livelit_shape(n))
    return true;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_NOT:
    return is_live_combo(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return is_live_combo(n->lhs) && is_live_combo(n->rhs);
  default:
    return false;
  }
}

// ---------------------------------------------------------------------------
// Atom table: each atom is GF(base) or GF(!base)
// ---------------------------------------------------------------------------

typedef struct {
  const Node *base;
  bool ineg; // the atom is GF(!base) when true
} Atom;

typedef struct {
  Atom atoms[GR_ATOMS];
  int n;
  bool overflow;
} AtomTab;

static int atom_index(AtomTab *t, const Node *base, bool ineg) {
  for (int i = 0; i < t->n; i++)
    if (t->atoms[i].ineg == ineg && node_eq(t->atoms[i].base, base))
      return i;
  if (t->n >= GR_ATOMS) {
    t->overflow = true;
    return -1;
  }
  t->atoms[t->n] = (Atom){base, ineg};
  return t->n++;
}

// If n is a GF/FG literal, set *idx to its atom and *lneg to whether the
// literal is negated (true for F G, which is ¬GF¬).  Returns false otherwise.
static bool literal(const Node *n, AtomTab *t, int *idx, bool *lneg) {
  if (n->kind == NODE_G && n->arg->kind == NODE_F) {
    const Node *m = n->arg->arg; // GF m
    if (!is_trans(m))
      return false;
    if (m->kind == NODE_NOT)
      *idx = atom_index(t, m->arg, true);
    else
      *idx = atom_index(t, m, false);
    *lneg = false;
    return true;
  }
  if (n->kind == NODE_F && n->arg->kind == NODE_G) {
    const Node *m = n->arg->arg; // FG m = ¬GF¬m
    if (!is_trans(m))
      return false;
    if (m->kind == NODE_NOT)
      *idx = atom_index(t, m->arg, false); // GF(¬¬x)=GF x
    else
      *idx = atom_index(t, m, true); // GF(¬m)
    *lneg = true;
    return true;
  }
  return false;
}

// ---------------------------------------------------------------------------
// CNF over the atoms, clauses as (positive, negative) bitmasks
// ---------------------------------------------------------------------------

typedef struct {
  uint64_t pos, neg;
} Clause;

typedef struct {
  Clause cl[GR_CLAUSES];
  int n;
  bool overflow;
} Cnf;

static void cnf_true(Cnf *c) {
  c->n = 0;
  c->overflow = false;
}

static void cnf_add(Cnf *c, Clause k) {
  if (k.pos & k.neg)
    return; // tautology
  for (int i = 0; i < c->n; i++)
    if (c->cl[i].pos == k.pos && c->cl[i].neg == k.neg)
      return; // duplicate
  if (c->n >= GR_CLAUSES) {
    c->overflow = true;
    return;
  }
  c->cl[c->n++] = k;
}

static void cnf_false(Cnf *c) {
  cnf_true(c);
  cnf_add(c, (Clause){0, 0});
}

// dst = a ∧ b
static void cnf_and(Cnf *dst, const Cnf *a, const Cnf *b) {
  cnf_true(dst);
  for (int i = 0; i < a->n; i++)
    cnf_add(dst, a->cl[i]);
  for (int i = 0; i < b->n; i++)
    cnf_add(dst, b->cl[i]);
  if (a->overflow || b->overflow)
    dst->overflow = true;
}

// dst = a ∨ b  (distribution)
static void cnf_or(Cnf *dst, const Cnf *a, const Cnf *b) {
  cnf_true(dst);
  for (int i = 0; i < a->n; i++)
    for (int j = 0; j < b->n; j++)
      cnf_add(dst, (Clause){a->cl[i].pos | b->cl[j].pos,
                            a->cl[i].neg | b->cl[j].neg});
  if (a->overflow || b->overflow)
    dst->overflow = true;
}

// CNF of `n` under polarity `pos` (n is a Boolean combination of GF/FG).
static void cnf_of(const Node *n, bool pos, AtomTab *t, Cnf *out) {
  int idx;
  bool lneg;
  if (literal(n, t, &idx, &lneg)) {
    cnf_true(out);
    if (idx < 0) {
      out->overflow = true;
      return;
    }
    bool neg = lneg ^ !pos;
    cnf_add(out, neg ? (Clause){0, 1ull << idx} : (Clause){1ull << idx, 0});
    return;
  }

  switch (n->kind) {
  case NODE_TRUE:
    pos ? cnf_true(out) : cnf_false(out);
    return;
  case NODE_FALSE:
    pos ? cnf_false(out) : cnf_true(out);
    return;
  case NODE_NOT:
    cnf_of(n->arg, !pos, t, out);
    return;
  case NODE_AND: {
    Cnf l, r;
    cnf_of(n->lhs, pos, t, &l);
    cnf_of(n->rhs, pos, t, &r);
    pos ? cnf_and(out, &l, &r) : cnf_or(out, &l, &r);
    return;
  }
  case NODE_OR: {
    Cnf l, r;
    cnf_of(n->lhs, pos, t, &l);
    cnf_of(n->rhs, pos, t, &r);
    pos ? cnf_or(out, &l, &r) : cnf_and(out, &l, &r);
    return;
  }
  case NODE_IMPL: { // a -> b  ==  ¬a ∨ b
    Cnf l, r;
    cnf_of(n->lhs, !pos, t, &l);
    cnf_of(n->rhs, pos, t, &r);
    pos ? cnf_or(out, &l, &r) : cnf_and(out, &l, &r);
    return;
  }
  case NODE_EQUIV: {
    // pos: (¬a∨b) ∧ (¬b∨a);  neg: (a∧¬b) ∨ (¬a∧b)
    Cnf a0, a1, b0, b1, c1, c2;
    if (pos) {
      cnf_of(n->lhs, false, t, &a0);
      cnf_of(n->rhs, true, t, &b1);
      cnf_or(&c1, &a0, &b1);
      cnf_of(n->rhs, false, t, &b0);
      cnf_of(n->lhs, true, t, &a1);
      cnf_or(&c2, &b0, &a1);
      cnf_and(out, &c1, &c2);
    } else {
      cnf_of(n->lhs, true, t, &a1);
      cnf_of(n->rhs, false, t, &b0);
      cnf_and(&c1, &a1, &b0);
      cnf_of(n->lhs, false, t, &a0);
      cnf_of(n->rhs, true, t, &b1);
      cnf_and(&c2, &a0, &b1);
      cnf_or(out, &c1, &c2);
    }
    return;
  }
  default:
    cnf_true(out);
    out->overflow = true;
    return;
  }
}

// ===========================================================================
// Fragment classification & liveness collection
// ===========================================================================

// 0 = no liveness (init/safety), 1 = liveness (set *live), -1 = not in fragment.
static int classify_general(const Node *n, const Node **live) {
  if (is_prop(n))
    return 0;
  if (is_live_combo(n)) {
    *live = n;
    return 1;
  }
  if (n->kind == NODE_G && is_trans(n->arg))
    return 0; // safety
  return -1;
}

// Invariant section conjunct: the formula f stands for G f.
static int classify_invariant(TlsfSpec *sp, const Node *f, const Node **live) {
  if (is_trans(f))
    return 0; // G(transition) safety
  if (is_live_combo(f)) {
    *live = f; // G of a stable liveness combination is the combination
    return 1;
  }
  if (f->kind == NODE_F && is_trans(f->arg)) {
    *live = node_g(sp->arena, (Node *)f); // G F b
    return 1;
  }
  if (f->kind == NODE_G)
    return classify_invariant(sp, f->arg, live); // G(G m) = G m
  return -1;
}

// Push G through conjunction (G(x ∧ y) = G x ∧ G y) and collapse G(G x)=G x,
// so compact generalized-Büchi like G(F a ∧ F b) becomes G F a ∧ G F b.
static Node *gnorm(Arena *a, const Node *n) {
  switch (n->kind) {
  case NODE_G: {
    Node *m = gnorm(a, n->arg);
    if (m->kind == NODE_AND)
      return node_and(a, gnorm(a, node_g(a, m->lhs)),
                      gnorm(a, node_g(a, m->rhs)));
    if (m->kind == NODE_G)
      return m;
    return node_g(a, m);
  }
  case NODE_NOT:
    return node_not(a, gnorm(a, n->arg));
  case NODE_X:
    return node_x(a, gnorm(a, n->arg));
  case NODE_X_STRONG:
    return node_x_strong(a, gnorm(a, n->arg));
  case NODE_F:
    return node_f(a, gnorm(a, n->arg));
  case NODE_AND:
    return node_and(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_OR:
    return node_or(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_IMPL:
    return node_impl(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_EQUIV:
    return node_equiv(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_U:
    return node_u(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_R:
    return node_r(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_W:
    return node_w(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  case NODE_M:
    return node_m(a, gnorm(a, n->lhs), gnorm(a, n->rhs));
  default:
    return (Node *)n;
  }
}

// ===========================================================================

int gr_level(TlsfSpec *spec) {
  const Node *env_live[GR_CLAUSES];
  const Node *sys_live[GR_CLAUSES];
  int n_env = 0, n_sys = 0;

#define COLLECT(formula, is_sys, classify_call)                                \
  do {                                                                         \
    const Node *_l = nullptr;                                                  \
    int _r = (classify_call);                                                  \
    if (_r < 0)                                                                \
      return -1;                                                               \
    if (_r == 1) {                                                             \
      if ((is_sys) ? n_sys >= GR_CLAUSES : n_env >= GR_CLAUSES)                \
        return -1;                                                             \
      if (is_sys)                                                              \
        sys_live[n_sys++] = _l;                                                \
      else                                                                     \
        env_live[n_env++] = _l;                                                \
    }                                                                          \
  } while (0)

  // Flatten each section's formulas into conjuncts and classify them.
#define WALK(list, is_sys, SECKIND)                                            \
  for (uint32_t _i = 0; _i < (list).count; _i++) {                             \
    const Node *_stack[64];                                                    \
    int _sp = 0;                                                               \
    _stack[_sp++] = gnorm(spec->arena, (list).formulas[_i]);                   \
    while (_sp > 0) {                                                          \
      const Node *_n = _stack[--_sp];                                          \
      if (_n->kind == NODE_AND) {                                              \
        if (_sp + 2 > 64)                                                      \
          return -1;                                                           \
        _stack[_sp++] = _n->lhs;                                               \
        _stack[_sp++] = _n->rhs;                                               \
        continue;                                                              \
      }                                                                        \
      if ((SECKIND) == 0)                                                      \
        COLLECT(_n, is_sys, is_prop(_n) ? 0 : -1);                             \
      else if ((SECKIND) == 1)                                                 \
        COLLECT(_n, is_sys, classify_general(_n, &_l));                        \
      else                                                                     \
        COLLECT(_n, is_sys, classify_invariant(spec, _n, &_l));               \
    }                                                                          \
  }

  WALK(spec->initially, false, 0);
  WALK(spec->preset, true, 0);
  WALK(spec->require, false, 2);
  WALK(spec->assert_, true, 2);
  WALK(spec->assume, false, 1);
  WALK(spec->guarantee, true, 1);
#undef WALK
#undef COLLECT

  // Build CNF of  (⋀ env_live) -> (⋀ sys_live).
  AtomTab t = {0};
  Cnf cnf_b;
  cnf_true(&cnf_b);
  for (int i = 0; i < n_sys; i++) {
    Cnf tmp, acc;
    cnf_of(sys_live[i], true, &t, &tmp);
    cnf_and(&acc, &cnf_b, &tmp);
    cnf_b = acc;
  }

  Cnf cnf_not_a;
  cnf_false(&cnf_not_a); // ¬(empty conjunction) = false
  for (int i = 0; i < n_env; i++) {
    Cnf tmp, acc;
    cnf_of(env_live[i], false, &t, &tmp);
    cnf_or(&acc, &cnf_not_a, &tmp);
    cnf_not_a = acc;
  }

  Cnf result;
  cnf_or(&result, &cnf_not_a, &cnf_b);

  if (t.overflow || cnf_b.overflow || cnf_not_a.overflow || result.overflow)
    return -1;

  // k = number of distinct antecedents (negative-literal masks).
  uint64_t seen[GR_CLAUSES];
  int k = 0;
  for (int i = 0; i < result.n; i++) {
    uint64_t a = result.cl[i].neg;
    bool found = false;
    for (int j = 0; j < k && !found; j++)
      found = seen[j] == a;
    if (!found)
      seen[k++] = a;
  }
  return k;
}
