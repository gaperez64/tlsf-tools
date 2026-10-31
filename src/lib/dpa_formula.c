#include "dpa_internal.h"

uint32_t dpa_class(TlsfDpa *c, Bdd owned) {
  if (bdd_invalid(owned))
    return dpa_decline(c, TLSF_DPA_BDD_LIMIT);
  if (!dpa_poll(c)) {
    oxidd_bdd_unref(owned);
    return DPA_BAD;
  }
  uintptr_t p = (uintptr_t)owned._p;
  uint64_t h =
      dpa_hash((uint32_t)p, (uint32_t)((uint64_t)p >> 32), (uint32_t)owned._i,
               (uint32_t)((uint64_t)owned._i >> 32));
  for (uint32_t i = dpa_bucket(&c->classes, h); i != DPA_BAD;) {
    DpaClass *cl = dpa_cls(c, i);
    if (bdd_same_identity(cl->bdd, owned)) {
      oxidd_bdd_unref(owned);
      return i;
    }
    if (!dpa_poll(c)) {
      oxidd_bdd_unref(owned);
      return DPA_BAD;
    }
    i = cl->key.next;
  }
  DpaClass *cl = dpa_alloc(c, 1, sizeof *cl);
  if (!cl) {
    oxidd_bdd_unref(owned);
    return DPA_BAD;
  }
  *cl = (DpaClass){.key.hash = h,
                   .bdd = owned,
                   .unfold = DPA_BAD,
                   .step = DPA_BAD,
                   .dag = DPA_BAD,
                   .remainder = DPA_BAD,
                   .label = DPA_BAD,
                   .dual = DPA_BAD,
                   .acceptance = DPA_BAD,
                   .var = DPA_BAD,
                   .low = DPA_BAD,
                   .high = DPA_BAD};
  if (!dpa_insert(c, &c->classes, cl)) {
    oxidd_bdd_unref(owned);
    return DPA_BAD;
  }
  return c->classes.n - 1;
}

uint32_t dpa_boolean(TlsfDpa *c, bool conjunction, uint32_t a, uint32_t b) {
  if (!dpa_poll(c))
    return DPA_BAD;
  Bdd x = dpa_cls(c, a)->bdd, y = dpa_cls(c, b)->bdd;
  return dpa_class(c, conjunction ? oxidd_bdd_and(x, y) : oxidd_bdd_or(x, y));
}

uint32_t dpa_ite(TlsfDpa *c, uint32_t v, uint32_t hi, uint32_t lo) {
  if (!dpa_poll(c))
    return DPA_BAD;
  return dpa_class(c, oxidd_bdd_ite(dpa_cls(c, v)->bdd, dpa_cls(c, hi)->bdd,
                                    dpa_cls(c, lo)->bdd));
}

bool dpa_children(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return false;
  if (f < 2)
    return true;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->var != DPA_BAD)
    return true;
  cl->var = oxidd_bdd_node_var(cl->bdd);
  cl->low = dpa_class(c, oxidd_bdd_cofactor_false(cl->bdd));
  if (!dpa_poll(c))
    return false;
  cl->high = dpa_class(c, oxidd_bdd_cofactor_true(cl->bdd));
  return dpa_poll(c);
}

static uint32_t materialize(TlsfDpa *c, uint32_t f);
static unsigned tags_impl(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return 0;
  if (f < 2)
    return DPA_ALL;
  DpaClass *cl = dpa_cls(c, f);
  // tags+1 distinguishes a computed empty fragment intersection.
  if (cl->tags)
    return cl->tags - 1;
  if (!dpa_children(c, f))
    return 0;
  DpaAtom *atom = c->atoms.items[cl->var];
  if ((c->started || !(atom->tags & (c->budget.allow_unproved
                                         ? DPA_PI2 | DPA_SIGMA2
                                         : DPA_SAFETY | DPA_COSAFETY))) &&
      !atom->exact_tags && atom->op != TLSF_AST_AP &&
      atom->op != TLSF_AST_KIND_COUNT) {
    unsigned tags = dpa_tags(c, materialize(c, atom->lhs));
    if (atom->op >= TLSF_AST_U)
      tags &= dpa_tags(c, materialize(c, atom->rhs));
    if (atom->op == TLSF_AST_F || atom->op == TLSF_AST_U ||
        atom->op == TLSF_AST_M)
      tags = (tags & (DPA_COSAFETY | DPA_SIGMA2)) |
             ((tags & DPA_COSAFETY) ? DPA_PI2 : 0);
    if (atom->op == TLSF_AST_G || atom->op == TLSF_AST_R ||
        atom->op == TLSF_AST_W)
      tags = (tags & (DPA_SAFETY | DPA_PI2)) |
             ((tags & DPA_SAFETY) ? DPA_SIGMA2 : 0);
    atom->tags = tags;
    atom->exact_tags = true;
  }
  unsigned tags = atom->tags & dpa_tags(c, cl->low) & dpa_tags(c, cl->high);
  cl->tags = tags + 1;
  return tags;
}

unsigned dpa_tags(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return 0;
  unsigned result = tags_impl(c, f);
  --c->recursion;
  return result;
}

// Cached lower/upper bounds only. An undecided predicate still uses exact tags.
static void tag_bounds(TlsfDpa *c, uint32_t f, unsigned *lo, unsigned *hi) {
  if (!dpa_enter(c)) {
    *lo = 0;
    *hi = DPA_ALL;
    return;
  }
  DpaClass *cl = dpa_cls(c, f);
  if (!cl->quick_high) {
    unsigned l = DPA_ALL, h = DPA_ALL;
    if (f > 1 && dpa_children(c, f)) {
      DpaAtom *a = c->atoms.items[cl->var];
      l = a->tags;
      if (a->op == TLSF_AST_F || a->op == TLSF_AST_U || a->op == TLSF_AST_M)
        h = DPA_COSAFETY | DPA_PI2 | DPA_SIGMA2;
      else if (a->op == TLSF_AST_G || a->op == TLSF_AST_R ||
               a->op == TLSF_AST_W)
        h = DPA_SAFETY | DPA_PI2 | DPA_SIGMA2;
      unsigned ll, lh, hl, hh;
      tag_bounds(c, cl->low, &ll, &lh);
      tag_bounds(c, cl->high, &hl, &hh);
      l &= ll & hl;
      h &= lh & hh;
    }
    cl->quick_low = l + 1;
    cl->quick_high = h + 1;
  }
  *lo = cl->quick_low - 1;
  *hi = cl->quick_high - 1;
  --c->recursion;
}
bool dpa_has_tags(TlsfDpa *c, uint32_t f, unsigned mask) {
  if (!dpa_poll(c))
    return false;
  unsigned lo, hi;
  tag_bounds(c, f, &lo, &hi);
  if (lo & mask)
    return true;
  if (!(hi & mask))
    return false;
  return dpa_tags(c, f) & mask;
}
// Positive Boolean bodies over finite windows and F(window), or their G duals.
static bool flat_body(TlsfDpa *c, uint32_t f, bool eventual) {
  if (!dpa_enter(c))
    return false;
  DpaClass *cl = dpa_cls(c, f);
  if (!cl->flat[eventual]) {
    bool flat = dpa_tags(c, f) & DPA_FINITE;
    if (!flat && dpa_children(c, f)) {
      DpaAtom *atom = c->atoms.items[cl->var];
      flat = ((atom->tags & DPA_FINITE) ||
              (atom->op == (eventual ? TLSF_AST_F : TLSF_AST_G) &&
               (dpa_tags(c, materialize(c, atom->lhs)) & DPA_FINITE))) &&
             flat_body(c, cl->low, eventual) &&
             flat_body(c, cl->high, eventual);
    }
    cl->flat[eventual] = flat ? 2 : 1;
  }
  --c->recursion;
  return cl->flat[eventual] == 2;
}

bool dpa_admitted(TlsfDpa *c, uint32_t f) {
  unsigned tags = dpa_tags(c, f);
  if (c->budget.allow_unproved)
    return tags & (DPA_PI2 | DPA_SIGMA2);
  if (tags & (DPA_SAFETY | DPA_COSAFETY))
    return true;
  if (!dpa_children(c, f))
    return false;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->low != 0 || cl->high != 1)
    return false;
  DpaAtom *outer = c->atoms.items[cl->var];
  if (outer->op != TLSF_AST_G && outer->op != TLSF_AST_F)
    return false;
  uint32_t body = materialize(c, outer->lhs);
  return dpa_poll(c) && flat_body(c, body, outer->op == TLSF_AST_G);
}

uint32_t dpa_atom(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b) {
  if (!dpa_poll(c))
    return DPA_BAD;
  // Constant temporal operands retain their language under X/F/G.
  if (op != TLSF_AST_AP && a < 2 &&
      (op == TLSF_AST_X || op == TLSF_AST_F || op == TLSF_AST_G))
    return a;
  uint64_t h = dpa_hash((uint32_t)op, a, b, 0);
  for (uint32_t i = dpa_bucket(&c->atoms, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaAtom *atom = c->atoms.items[i];
    if (atom->op == op && atom->lhs == a && atom->rhs == b)
      return atom->cls;
    i = atom->key.next;
  }
  if (c->atoms.n == UINT32_MAX - 1)
    return dpa_decline(c, TLSF_DPA_HOST_LIMIT);
  DpaAtom *atom = dpa_alloc(c, 1, sizeof *atom);
  if (!atom)
    return DPA_BAD;
  unsigned tags = op == TLSF_AST_AP ? DPA_ALL : 0;
  if (op != TLSF_AST_AP && op != TLSF_AST_KIND_COUNT) {
    tags = ((DpaTerm *)c->terms.items[a])->tags;
    if (op == TLSF_AST_U || op == TLSF_AST_R || op == TLSF_AST_W ||
        op == TLSF_AST_M)
      tags &= ((DpaTerm *)c->terms.items[b])->tags;
    if (op == TLSF_AST_F || op == TLSF_AST_U || op == TLSF_AST_M)
      tags = (tags & (DPA_COSAFETY | DPA_SIGMA2)) |
             ((tags & DPA_COSAFETY) ? DPA_PI2 : 0);
    if (op == TLSF_AST_G || op == TLSF_AST_R || op == TLSF_AST_W)
      tags = (tags & (DPA_SAFETY | DPA_PI2)) |
             ((tags & DPA_SAFETY) ? DPA_SIGMA2 : 0);
  }
  *atom = (DpaAtom){.key.hash = h, .op = op, .lhs = a, .rhs = b, .tags = tags};
  uint32_t var = c->atoms.n;
  if (!dpa_insert(c, &c->atoms, atom))
    return DPA_BAD;
  oxidd_bdd_manager_add_vars(c->manager, 1);
  if (!dpa_poll(c))
    return DPA_BAD;
  atom->cls = dpa_class(c, oxidd_bdd_var(c->manager, var));
  return atom->cls;
}

// Owned, hash-consed NNF syntax keeps modal operands frozen until needed.
// Compiling those Boolean classes during admission can itself be exponential.
static uint32_t term(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b) {
  if (!dpa_poll(c))
    return DPA_BAD;
  if (!c->terms.n) {
    for (uint32_t i = 0; i < 2; ++i) {
      DpaTerm *t = dpa_alloc(c, 1, sizeof *t);
      if (!t)
        return DPA_BAD;
      *t = (DpaTerm){.op = i ? TLSF_AST_TRUE : TLSF_AST_FALSE,
                     .cls = i,
                     .dual = 1 - i,
                     .tags = DPA_ALL};
      if (!dpa_insert(c, &c->terms, t))
        return DPA_BAD;
    }
  }
  if (op == TLSF_AST_TRUE || op == TLSF_AST_FALSE)
    return op == TLSF_AST_TRUE;
  if (op == TLSF_AST_AND || op == TLSF_AST_OR) {
    if (a > b) {
      uint32_t tmp = a;
      a = b;
      b = tmp;
    }
    if (a == b)
      return a;
    if (op == TLSF_AST_AND && a < 2)
      return a ? b : 0;
    if (op == TLSF_AST_OR && a < 2)
      return a ? 1 : b;
  }
  if ((op == TLSF_AST_X || op == TLSF_AST_F || op == TLSF_AST_G) && a < 2)
    return a;
  uint64_t h = dpa_hash((uint32_t)op, a, b, 0);
  for (uint32_t i = dpa_bucket(&c->terms, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaTerm *t = c->terms.items[i];
    if (t->op == op && t->lhs == a && t->rhs == b)
      return i;
    i = t->key.next;
  }
  DpaTerm *t = dpa_alloc(c, 1, sizeof *t);
  if (!t)
    return DPA_BAD;
  unsigned tags = DPA_ALL;
  if (op != TLSF_AST_AP) {
    tags = ((DpaTerm *)c->terms.items[a])->tags;
    if (op == TLSF_AST_AND || op == TLSF_AST_OR || op >= TLSF_AST_U)
      tags &= ((DpaTerm *)c->terms.items[b])->tags;
    if (op == TLSF_AST_F || op == TLSF_AST_U || op == TLSF_AST_M)
      tags = (tags & (DPA_COSAFETY | DPA_SIGMA2)) |
             ((tags & DPA_COSAFETY) ? DPA_PI2 : 0);
    if (op == TLSF_AST_G || op == TLSF_AST_R || op == TLSF_AST_W)
      tags = (tags & (DPA_SAFETY | DPA_PI2)) |
             ((tags & DPA_SAFETY) ? DPA_SIGMA2 : 0);
  }
  *t = (DpaTerm){.key.hash = h,
                 .op = op,
                 .lhs = a,
                 .rhs = b,
                 .tags = tags,
                 .cls = DPA_BAD,
                 .dual = DPA_BAD};
  return dpa_insert(c, &c->terms, t) ? c->terms.n - 1 : DPA_BAD;
}
static TlsfAstKind dual_op(TlsfAstKind op) {
  switch (op) {
  case TLSF_AST_AND:
    return TLSF_AST_OR;
  case TLSF_AST_OR:
    return TLSF_AST_AND;
  case TLSF_AST_F:
    return TLSF_AST_G;
  case TLSF_AST_G:
    return TLSF_AST_F;
  case TLSF_AST_U:
    return TLSF_AST_R;
  case TLSF_AST_R:
    return TLSF_AST_U;
  case TLSF_AST_W:
    return TLSF_AST_M;
  case TLSF_AST_M:
    return TLSF_AST_W;
  default:
    return op;
  }
}
static uint32_t term_dual(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return DPA_BAD;
  DpaTerm *t = c->terms.items[f];
  uint32_t result = t->dual;
  if (result == DPA_BAD) {
    if (t->op == TLSF_AST_NOT)
      result = t->lhs;
    else if (t->op == TLSF_AST_AP)
      result = term(c, TLSF_AST_NOT, f, 0);
    else {
      bool binary =
          t->op == TLSF_AST_AND || t->op == TLSF_AST_OR || t->op >= TLSF_AST_U;
      result = term(c, dual_op(t->op), term_dual(c, t->lhs),
                    binary ? term_dual(c, t->rhs) : 0);
    }
    if (dpa_poll(c)) {
      t->dual = result;
      ((DpaTerm *)c->terms.items[result])->dual = f;
    }
  }
  --c->recursion;
  return result;
}
static uint32_t materialize(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return DPA_BAD;
  DpaTerm *t = c->terms.items[f];
  uint32_t result = t->cls;
  if (result == DPA_BAD) {
    if (t->op == TLSF_AST_AND || t->op == TLSF_AST_OR)
      result = dpa_boolean(c, t->op == TLSF_AST_AND, materialize(c, t->lhs),
                           materialize(c, t->rhs));
    else if (t->op == TLSF_AST_NOT) {
      uint32_t a = materialize(c, t->lhs);
      if (dpa_poll(c))
        result = dpa_class(c, oxidd_bdd_not(dpa_cls(c, a)->bdd));
    } else
      result = dpa_atom(c, t->op, t->lhs, t->rhs);
    t->cls = result;
  }
  --c->recursion;
  return result;
}
static uint32_t transport(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                          unsigned depth, unsigned next);
static uint32_t wrap_next(TlsfDpa *c, uint32_t f, unsigned next) {
  while (next-- && dpa_poll(c))
    f = term(c, TLSF_AST_X, f, 0);
  return f;
}

static uint32_t formula_impl(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                             unsigned depth, unsigned next) {
  if (!dpa_poll(c))
    return DPA_BAD;
  if (depth > 1024)
    return dpa_decline(c, TLSF_DPA_UNSUPPORTED);
  if (!n) {
    c->status.code = TLSF_DPA_INVALID;
    return DPA_BAD;
  }
  TlsfAstKind op = tlsf_ast_node_kind(n);
  if (op == TLSF_AST_TRUE || op == TLSF_AST_FALSE)
    return (op == TLSF_AST_TRUE) != neg;
  if (op == TLSF_AST_AP) {
    const char *name = tlsf_ast_node_ap_name(n);
    for (uint32_t i = 0; i < c->aps && dpa_poll(c); ++i)
      if (name && !strcmp(c->names[i], name)) {
        uint32_t f = term(c, TLSF_AST_AP, i, 0);
        if (neg)
          f = term(c, TLSF_AST_NOT, f, 0);
        return wrap_next(c, f, next);
      }
    if (dpa_poll(c))
      c->status.code = TLSF_DPA_INVALID;
    return DPA_BAD;
  }
  const TlsfAstNode *left = tlsf_ast_node_child(n, 0);
  if (op == TLSF_AST_NOT)
    return transport(c, left, !neg, depth + 1, next);
  if (op == TLSF_AST_X)
    return transport(c, left, neg, depth + 1, next + 1);
  if (op == TLSF_AST_X_STRONG || op >= TLSF_AST_KIND_COUNT)
    return dpa_decline(c, TLSF_DPA_UNSUPPORTED);
  const TlsfAstNode *right = tlsf_ast_node_child(n, 1);
  uint32_t a, b;
  if (op == TLSF_AST_IMPL || op == TLSF_AST_EQUIV) {
    a = transport(c, left, !neg, depth + 1, next);
    b = transport(c, right, neg, depth + 1, next);
    uint32_t first = term(c, neg ? TLSF_AST_AND : TLSF_AST_OR, a, b);
    if (op == TLSF_AST_IMPL)
      return first;
    a = transport(c, left, neg, depth + 1, next);
    b = transport(c, right, !neg, depth + 1, next);
    return term(c, neg ? TLSF_AST_OR : TLSF_AST_AND, first,
                term(c, neg ? TLSF_AST_AND : TLSF_AST_OR, a, b));
  }
  if (op == TLSF_AST_AND || op == TLSF_AST_OR) {
    a = transport(c, left, neg, depth + 1, next);
    b = transport(c, right, neg, depth + 1, next);
    return term(c, ((op == TLSF_AST_AND) != neg) ? TLSF_AST_AND : TLSF_AST_OR,
                a, b);
  }
  a = transport(c, left, neg, depth + 1, 0);
  if (op == TLSF_AST_U || op == TLSF_AST_R || op == TLSF_AST_W ||
      op == TLSF_AST_M)
    b = transport(c, right, neg, depth + 1, 0);
  else
    b = 0;
  if (neg) {
    switch (op) {
    case TLSF_AST_F:
      op = TLSF_AST_G;
      break;
    case TLSF_AST_G:
      op = TLSF_AST_F;
      break;
    case TLSF_AST_U:
      op = TLSF_AST_R;
      break;
    case TLSF_AST_R:
      op = TLSF_AST_U;
      break;
    case TLSF_AST_W:
      op = TLSF_AST_M;
      break;
    case TLSF_AST_M:
      op = TLSF_AST_W;
      break;
    default:
      break;
    }
  }
  return wrap_next(c, term(c, op, a, b), next);
}

// NNF and X-through-Boolean transport share the input traversal memo. Modal
// duals remain separate atoms; only AP negation uses the manager's complement.
static uint32_t transport(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                          unsigned depth, unsigned next) {
  if (!dpa_poll(c))
    return DPA_BAD;
  uintptr_t p = (uintptr_t)n;
  uint64_t h = dpa_hash((uint32_t)p, (uint32_t)((uint64_t)p >> 32), neg, next);
  for (uint32_t i = dpa_bucket(&c->syntax, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaSyntax *entry = c->syntax.items[i];
    if (entry->node == n && entry->neg == neg && entry->next == next)
      return entry->formula;
    i = entry->key.next;
  }
  uint32_t f = formula_impl(c, n, neg, depth, next);
  DpaSyntax *entry = dpa_alloc(c, 1, sizeof *entry);
  if (!entry)
    return DPA_BAD;
  *entry = (DpaSyntax){
      .key.hash = h, .node = n, .neg = neg, .formula = f, .next = next};
  return dpa_insert(c, &c->syntax, entry) ? f : DPA_BAD;
}

// Validate the original canonical support before changing its representation.
static bool check_admission(TlsfDpa *c, uint32_t f, uint64_t epoch) {
  if (!dpa_enter(c))
    return false;
  bool result = true;
  if (f > 1 && dpa_children(c, f)) {
    DpaClass *cl = dpa_cls(c, f);
    if (cl->epoch != epoch) {
      cl->epoch = epoch;
      if (!dpa_admitted(c, f)) {
        DpaAtom *atom = c->atoms.items[cl->var];
        result = dpa_admitted(c, atom->cls) &&
                 check_admission(c, cl->low, epoch) &&
                 check_admission(c, cl->high, epoch);
      }
    }
  }
  --c->recursion;
  return dpa_poll(c) && result;
}
static uint32_t factor_term(TlsfDpa *c, uint32_t id) {
  if (!dpa_enter(c))
    return DPA_BAD;
  DpaTerm *t = c->terms.items[id];
  uint32_t result = id;
  // Compatible fragments already belong in one monitor.
  if (id > 1 && !t->factored && !(t->tags & (DPA_SAFETY | DPA_COSAFETY))) {
    uint32_t a = factor_term(c, t->lhs);
    bool binary =
        t->op == TLSF_AST_AND || t->op == TLSF_AST_OR || t->op >= TLSF_AST_U;
    uint32_t b = binary ? factor_term(c, t->rhs) : 0;
    if (dpa_poll(c)) {
      DpaTerm *body = c->terms.items[a];
      if ((t->op == TLSF_AST_G && body->op == TLSF_AST_AND) ||
          (t->op == TLSF_AST_F && body->op == TLSF_AST_OR))
        result = factor_term(c, term(c, body->op, term(c, t->op, body->lhs, 0),
                                     term(c, t->op, body->rhs, 0)));
      else
        result = term(c, t->op, a, b);
      if (dpa_poll(c))
        t->factored = result + 1;
    }
  } else if (t->factored)
    result = t->factored - 1;
  --c->recursion;
  return result;
}
// Check every leaf that flattening could expose, before allocating components.
static bool groupable(TlsfDpa *c, uint32_t id, uint64_t epoch) {
  if (!dpa_enter(c))
    return false;
  DpaTerm *t = c->terms.items[id];
  bool result = t->op == TLSF_AST_AND || t->op == TLSF_AST_OR
                    ? groupable(c, t->lhs, epoch) && groupable(c, t->rhs, epoch)
                    : check_admission(c, materialize(c, id), epoch);
  --c->recursion;
  return result;
}
static uint32_t syntax_acceptance(TlsfDpa *c, uint32_t id);
static void group_operands(TlsfDpa *c, uint32_t id, TlsfAstKind op,
                           uint32_t *safety, uint32_t *cosafety,
                           uint32_t *finite, uint32_t *rest) {
  if (!dpa_enter(c))
    return;
  DpaTerm *t = c->terms.items[id];
  bool conjunction = op == TLSF_AST_AND;
  if (t->op == op) {
    group_operands(c, t->lhs, op, safety, cosafety, finite, rest);
    group_operands(c, t->rhs, op, safety, cosafety, finite, rest);
  } else if (t->tags & DPA_FINITE)
    *finite = dpa_boolean(c, conjunction, *finite, materialize(c, id));
  else if (t->tags & DPA_SAFETY)
    *safety = dpa_boolean(c, conjunction, *safety, materialize(c, id));
  else if (t->tags & DPA_COSAFETY)
    *cosafety = dpa_boolean(c, conjunction, *cosafety, materialize(c, id));
  else
    *rest = dpa_boolean(c, conjunction, *rest, syntax_acceptance(c, id));
  --c->recursion;
}
static uint32_t syntax_acceptance(TlsfDpa *c, uint32_t id) {
  if (!dpa_enter(c))
    return DPA_BAD;
  DpaTerm *t = c->terms.items[id];
  uint32_t f = materialize(c, id), result = DPA_BAD;
  if (!dpa_poll(c))
    goto done;
  if (f < 2 || dpa_admitted(c, f))
    result = dpa_acceptance(c, f);
  else if (t->op == TLSF_AST_AND || t->op == TLSF_AST_OR) {
    bool conjunction = t->op == TLSF_AST_AND;
    uint32_t safety = conjunction, cosafety = conjunction, finite = conjunction,
             rest = conjunction;
    group_operands(c, id, t->op, &safety, &cosafety, &finite, &rest);
    if (cosafety != (uint32_t)conjunction)
      cosafety = dpa_boolean(c, conjunction, cosafety, finite);
    else
      safety = dpa_boolean(c, conjunction, safety, finite);
    result = dpa_boolean(c, conjunction, rest,
                         dpa_boolean(c, conjunction, dpa_acceptance(c, safety),
                                     dpa_acceptance(c, cosafety)));
  } else
    result = dpa_acceptance(c, f);
done:
  --c->recursion;
  return result;
}
uint32_t dpa_grouped_acceptance(TlsfDpa *c, uint32_t f) {
  if (!check_admission(c, f, ++c->epoch))
    return dpa_decline(c, TLSF_DPA_UNSUPPORTED);
  uint32_t id = factor_term(c, c->formula_term);
  bool grouped = dpa_poll(c) && groupable(c, id, ++c->epoch);
  if (!dpa_poll(c))
    return DPA_BAD;
  return grouped ? syntax_acceptance(c, id) : dpa_acceptance(c, f);
}
uint32_t dpa_formula(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                     unsigned depth) {
  if (!c->terms.n)
    term(c, TLSF_AST_FALSE, 0, 0);
  uint32_t f = transport(c, n, neg, depth, 0);
  c->formula_term = f;
  return dpa_poll(c) ? materialize(c, f) : DPA_BAD;
}

enum { STEP, REDUCE, DROP_X };
static uint32_t map_impl(TlsfDpa *c, uint32_t f, unsigned mode, uint64_t epoch,
                         const bool *protect);
static uint32_t map_class(TlsfDpa *c, uint32_t f, unsigned mode, uint64_t epoch,
                          const bool *protect) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = map_impl(c, f, mode, epoch, protect);
  --c->recursion;
  return result;
}
static uint32_t map_impl(TlsfDpa *c, uint32_t f, unsigned mode, uint64_t epoch,
                         const bool *protect) {
  if (!dpa_poll(c) || f < 2)
    return f;
  DpaClass *cl = dpa_cls(c, f);
  if (mode >= REDUCE && cl->epoch != epoch) {
    cl->epoch = epoch;
    cl->mapped = DPA_BAD;
  }
  uint32_t *slot = mode == STEP ? &cl->step : &cl->mapped;
  if (slot && *slot != DPA_BAD)
    return *slot;
  if (!dpa_children(c, f))
    return DPA_BAD;
  DpaAtom *atom = c->atoms.items[cl->var];
  uint32_t v = atom->cls;
  if (mode == STEP && atom->op == TLSF_AST_X)
    v = materialize(c, atom->lhs);
  else if (mode == REDUCE && atom->op != TLSF_AST_AP &&
           !dpa_has_tags(c, atom->cls, DPA_COSAFETY))
    v = 1;
  else if (mode == DROP_X && atom->op == TLSF_AST_X && !protect[cl->var])
    v = 1;

  uint32_t low = map_class(c, cl->low, mode, epoch, protect);
  uint32_t high = map_class(c, cl->high, mode, epoch, protect);
  uint32_t result = dpa_ite(c, v, high, low);
  if (slot)
    *slot = result;
  return result;
}

static uint32_t unfold_care(TlsfDpa *c, uint32_t id, uint32_t cube,
                            signed char *care, bool syntax);
static uint32_t unfold_term_care(TlsfDpa *c, uint32_t id, uint32_t cube,
                                 signed char *care);
static uint32_t unfold_atom_care(TlsfDpa *c, DpaAtom *atom, uint32_t cube,
                                 signed char *care) {
  if (atom->op == TLSF_AST_AP)
    return care[atom->lhs] < 0 ? atom->cls : (uint32_t)care[atom->lhs];
  if (atom->op == TLSF_AST_X)
    return atom->cls;
  uint32_t a = unfold_care(c, atom->lhs, cube, care, true);
  uint32_t b =
      atom->op >= TLSF_AST_U ? unfold_care(c, atom->rhs, cube, care, true) : 0;
  uint32_t v = atom->cls;
  switch (atom->op) {
  case TLSF_AST_F:
    return dpa_boolean(c, false, a, v);
  case TLSF_AST_G:
    return dpa_boolean(c, true, a, v);
  case TLSF_AST_U:
  case TLSF_AST_W:
    return dpa_boolean(c, false, b, dpa_boolean(c, true, a, v));
  case TLSF_AST_R:
  case TLSF_AST_M:
    return dpa_boolean(c, true, b, dpa_boolean(c, false, a, v));
  default:
    c->status.code = TLSF_DPA_INTERNAL;
    return DPA_BAD;
  }
}
static uint32_t unfold_term_care(TlsfDpa *c, uint32_t id, uint32_t cube,
                                 signed char *care) {
  if (!dpa_enter(c))
    return DPA_BAD;
  DpaTerm *t = c->terms.items[id];
  uint32_t result = DPA_BAD;
  if (id < 2)
    result = id;
  else if (t->op == TLSF_AST_NOT) {
    uint32_t a = unfold_care(c, t->lhs, cube, care, true);
    if (dpa_poll(c))
      result = dpa_class(c, oxidd_bdd_not(dpa_cls(c, a)->bdd));
  } else if (t->op == TLSF_AST_AND || t->op == TLSF_AST_OR) {
    bool conjunction = t->op == TLSF_AST_AND;
    uint32_t a = unfold_care(c, t->lhs, cube, care, true);
    if (a == (uint32_t)!conjunction)
      result = a;
    else
      result = dpa_boolean(c, conjunction, a,
                           unfold_care(c, t->rhs, cube, care, true));
  } else {
    uint32_t f = materialize(c, id);
    if (dpa_poll(c)) {
      DpaAtom *atom = NULL;
      if (f < 2)
        result = f;
      else if (dpa_children(c, f)) {
        atom = c->atoms.items[dpa_cls(c, f)->var];
        result = unfold_atom_care(c, atom, cube, care);
      }
    }
  }
  --c->recursion;
  return result;
}
static uint32_t unfold_class_care(TlsfDpa *c, uint32_t f, uint32_t cube,
                                  signed char *care) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = f;
  unsigned lo, hi;
  tag_bounds(c, f, &lo, &hi);
  if (!(lo & DPA_FINITE) && f > 1 && dpa_children(c, f)) {
    DpaClass *cl = dpa_cls(c, f);
    DpaAtom *atom = c->atoms.items[cl->var];
    uint32_t low, high, v;
    if (atom->op == TLSF_AST_AP) {
      signed char old = care[atom->lhs];
      care[atom->lhs] = 0;
      low =
          unfold_care(c, cl->low, dpa_ite(c, atom->cls, 0, cube), care, false);
      care[atom->lhs] = 1;
      high =
          unfold_care(c, cl->high, dpa_ite(c, atom->cls, cube, 0), care, false);
      care[atom->lhs] = old;
      v = atom->cls;
    } else {
      v = unfold_atom_care(c, atom, cube, care);
      low = unfold_care(c, cl->low, cube, care, false);
      high = unfold_care(c, cl->high, cube, care, false);
    }
    result = dpa_ite(c, v, high, low);
  }
  --c->recursion;
  return result;
}
// The cube records only CURRENT AP choices; X and continuations stay frozen.
static uint32_t unfold_care(TlsfDpa *c, uint32_t id, uint32_t cube,
                            signed char *care, bool syntax) {
  if (!dpa_poll(c))
    return DPA_BAD;
  if (id < 2)
    return id;
  uint64_t h = dpa_hash(id, cube, syntax, 0);
  for (uint32_t i = dpa_bucket(&c->unfolds, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaDag *p = c->unfolds.items[i];
    if (p->kind == (uint32_t)syntax && p->var == id && p->low == cube)
      return p->high;
    i = p->key.next;
  }
  uint32_t result = syntax ? unfold_term_care(c, id, cube, care)
                           : unfold_class_care(c, id, cube, care);
  DpaDag *p = dpa_alloc(c, 1, sizeof *p);
  if (!p)
    return DPA_BAD;
  *p = (DpaDag){
      .key.hash = h, .kind = syntax, .var = id, .low = cube, .high = result};
  return dpa_insert(c, &c->unfolds, p) ? result : DPA_BAD;
}
uint32_t dpa_unfold(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return DPA_BAD;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->unfold != DPA_BAD)
    return cl->unfold;
  signed char *care = dpa_alloc(c, c->aps, sizeof *care);
  if (!care)
    return DPA_BAD;
  memset(care, -1, c->aps);
  uint32_t result = unfold_care(c, f, 1, care, false);
  dpa_release(c, care);
  if (dpa_poll(c))
    cl->unfold = result;
  return result;
}

uint32_t dpa_dag(TlsfDpa *c, uint32_t kind, uint32_t var, uint32_t lo,
                 uint32_t hi) {
  if (!dpa_poll(c))
    return DPA_BAD;
  if (kind == 1 && lo == hi)
    return lo;
  uint64_t h = dpa_hash(kind, var, lo, hi);
  for (uint32_t i = dpa_bucket(&c->dags, h); i != DPA_BAD;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    DpaDag *d = c->dags.items[i];
    if (d->kind == kind && d->var == var && d->low == lo && d->high == hi)
      return i;
    i = d->key.next;
  }
  DpaDag *d = dpa_alloc(c, 1, sizeof *d);
  if (!d)
    return DPA_BAD;
  *d = (DpaDag){.key.hash = h, .kind = kind, .var = var, .low = lo, .high = hi};
  return dpa_insert(c, &c->dags, d) ? c->dags.n - 1 : DPA_BAD;
}

static uint32_t step_dag_impl(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return DPA_BAD;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->dag != DPA_BAD)
    return cl->dag;
  if (!dpa_children(c, f))
    return DPA_BAD;
  uint32_t result;
  if (f < 2 || cl->var >= c->aps) {
    uint32_t residual = map_class(c, f, STEP, 0, nullptr);
    result = dpa_dag(c, 0, 0, residual, 0);
  } else {
    uint32_t low = dpa_step_dag(c, cl->low), high = dpa_step_dag(c, cl->high);
    result = dpa_dag(c, 1, cl->var, low, high);
  }
  cl->dag = result;
  return result;
}

uint32_t dpa_step_dag(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = step_dag_impl(c, f);
  --c->recursion;
  return result;
}

static uint32_t substitute(TlsfDpa *c, uint32_t f, unsigned mode,
                           const bool *protect) {
  return map_class(c, f, mode, ++c->epoch, protect);
}

// Visit current support only; inside a modal protector traverse its full DAG.
static void protected_impl(TlsfDpa *c, uint32_t f, bool inside, bool *protect,
                           uint64_t epoch);
static void protected_x(TlsfDpa *c, uint32_t f, bool inside, bool *protect,
                        uint64_t epoch) {
  if (!dpa_enter(c))
    return;
  protected_impl(c, f, inside, protect, epoch);
  --c->recursion;
}
static void protected_impl(TlsfDpa *c, uint32_t f, bool inside, bool *protect,
                           uint64_t epoch) {
  if (!dpa_poll(c) || f < 2)
    return;
  unsigned char bit = inside ? 2 : 1;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->epoch != epoch) {
    cl->epoch = epoch;
    cl->visited = 0;
  }
  if (cl->visited & bit)
    return;
  cl->visited |= bit;
  if (!dpa_children(c, f))
    return;
  DpaAtom *atom = c->atoms.items[cl->var];
  if (atom->op == TLSF_AST_X && inside)
    protect[cl->var] = true;
  if (atom->op != TLSF_AST_AP && (inside || atom->op != TLSF_AST_X)) {
    protected_x(c, materialize(c, atom->lhs), true, protect, epoch);
    if (atom->op >= TLSF_AST_U)
      protected_x(c, materialize(c, atom->rhs), true, protect, epoch);
  }
  protected_x(c, cl->low, inside, protect, epoch);
  protected_x(c, cl->high, inside, protect, epoch);
}

uint32_t dpa_remainder(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return DPA_BAD;
  DpaClass *cl = dpa_cls(c, f);
  if (cl->remainder != DPA_BAD)
    return cl->remainder;
  uint32_t r = substitute(c, f, REDUCE, nullptr);
  for (;;) {
    if (!dpa_poll(c))
      return DPA_BAD;
    // Protection may materialize frozen operands; each syntax term adds at
    // most one atom, and this walk creates no new syntax.
    bool *protect =
        dpa_alloc(c, (size_t)c->atoms.n + c->terms.n, sizeof *protect);
    if (!protect) {
      dpa_release(c, protect);
      return DPA_BAD;
    }
    protected_x(c, r, false, protect, ++c->epoch);
    uint32_t next = substitute(c, r, DROP_X, protect);
    dpa_release(c, protect);
    if (next == r)
      break;
    r = next;
  }
  r = dpa_unfold(c, r);
  uint32_t unfolded = dpa_unfold(c, f);
  if (dpa_has_tags(c, r, DPA_FINITE) && unfolded != f)
    r = dpa_remainder(c, unfolded);
  cl->remainder = r;
  return r;
}

uint32_t dpa_dual(TlsfDpa *c, uint32_t f) {
  if (!dpa_enter(c))
    return DPA_BAD;
  uint32_t result = DPA_BAD;
  if (f < 2)
    result = 1 - f;
  else if (dpa_cls(c, f)->dual != DPA_BAD)
    result = dpa_cls(c, f)->dual;
  else if (dpa_children(c, f)) {
    DpaClass *cl = dpa_cls(c, f);
    DpaAtom *atom = c->atoms.items[cl->var];
    uint32_t v;
    if (atom->op == TLSF_AST_AP)
      v = dpa_class(c, oxidd_bdd_not(dpa_cls(c, atom->cls)->bdd));
    else {
      TlsfAstKind op = dual_op(atom->op);
      uint32_t rhs = op >= TLSF_AST_U ? term_dual(c, atom->rhs) : 0;
      v = dpa_atom(c, op, term_dual(c, atom->lhs), rhs);
    }
    result = dpa_ite(c, v, dpa_dual(c, cl->low), dpa_dual(c, cl->high));
    if (dpa_poll(c)) {
      cl->dual = result;
      dpa_cls(c, result)->dual = f;
    }
  }
  --c->recursion;
  return result;
}
