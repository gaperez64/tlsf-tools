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

static unsigned tags_impl(TlsfDpa *c, uint32_t f) {
  if (!dpa_poll(c))
    return 0;
  if (f < 2)
    return DPA_FINITE | DPA_SAFETY | DPA_COSAFETY;
  DpaClass *cl = dpa_cls(c, f);
  // tags+1 distinguishes a computed empty fragment intersection.
  if (cl->tags)
    return cl->tags - 1;
  if (!dpa_children(c, f))
    return 0;
  DpaAtom *atom = c->atoms.items[cl->var];
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
  unsigned tags = DPA_FINITE | DPA_SAFETY | DPA_COSAFETY;
  if (op != TLSF_AST_AP) {
    tags = dpa_tags(c, a);
    if (op == TLSF_AST_U || op == TLSF_AST_R || op == TLSF_AST_W ||
        op == TLSF_AST_M)
      tags &= dpa_tags(c, b);
    if (op == TLSF_AST_F || op == TLSF_AST_U || op == TLSF_AST_M)
      tags &= DPA_COSAFETY;
    if (op == TLSF_AST_G || op == TLSF_AST_R || op == TLSF_AST_W)
      tags &= DPA_SAFETY;
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

static uint32_t transport(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                          unsigned depth, unsigned next);
static uint32_t wrap_next(TlsfDpa *c, uint32_t f, unsigned next) {
  while (next-- && dpa_poll(c))
    f = dpa_atom(c, TLSF_AST_X, f, 0);
  return f;
}

static uint32_t formula_impl(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                             unsigned depth, unsigned next) {
  if (!dpa_poll(c))
    return DPA_BAD;
  if (depth > 256)
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
        DpaAtom *atom = c->atoms.items[i];
        uint32_t f =
            neg ? dpa_class(c, oxidd_bdd_not(dpa_cls(c, atom->cls)->bdd))
                : atom->cls;
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
    uint32_t first = dpa_boolean(c, neg, a, b);
    if (op == TLSF_AST_IMPL)
      return first;
    a = transport(c, left, neg, depth + 1, next);
    b = transport(c, right, !neg, depth + 1, next);
    return dpa_boolean(c, !neg, first, dpa_boolean(c, neg, a, b));
  }
  if (op == TLSF_AST_AND || op == TLSF_AST_OR) {
    a = transport(c, left, neg, depth + 1, next);
    b = transport(c, right, neg, depth + 1, next);
    return dpa_boolean(c, (op == TLSF_AST_AND) != neg, a, b);
  }
  a = dpa_formula(c, left, neg, depth + 1);
  if (op == TLSF_AST_U || op == TLSF_AST_R || op == TLSF_AST_W ||
      op == TLSF_AST_M)
    b = dpa_formula(c, right, neg, depth + 1);
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
  return wrap_next(c, dpa_atom(c, op, a, b), next);
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

uint32_t dpa_formula(TlsfDpa *c, const TlsfAstNode *n, bool neg,
                     unsigned depth) {
  return transport(c, n, neg, depth, 0);
}

enum { UNFOLD, STEP, REDUCE, DROP_X };
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
  uint32_t *slot = mode == UNFOLD ? &cl->unfold
                   : mode == STEP ? &cl->step
                                  : &cl->mapped;
  if (slot && *slot != DPA_BAD)
    return *slot;
  if (!dpa_children(c, f))
    return DPA_BAD;
  DpaAtom *atom = c->atoms.items[cl->var];
  uint32_t v = atom->cls;
  if (mode == STEP && atom->op == TLSF_AST_X)
    v = atom->lhs;
  else if (mode == REDUCE && atom->op != TLSF_AST_AP &&
           !(atom->tags & DPA_COSAFETY))
    v = 1;
  else if (mode == DROP_X && atom->op == TLSF_AST_X && !protect[cl->var])
    v = 1;
  else if (mode == UNFOLD && atom->op != TLSF_AST_AP &&
           atom->op != TLSF_AST_X) {
    uint32_t a = dpa_unfold(c, atom->lhs);
    uint32_t b = dpa_unfold(c, atom->rhs);
    switch (atom->op) {
    case TLSF_AST_F:
      v = dpa_boolean(c, false, a, v);
      break;
    case TLSF_AST_G:
      v = dpa_boolean(c, true, a, v);
      break;
    case TLSF_AST_U:
    case TLSF_AST_W:
      v = dpa_boolean(c, false, b, dpa_boolean(c, true, a, v));
      break;
    case TLSF_AST_R:
    case TLSF_AST_M:
      v = dpa_boolean(c, true, b, dpa_boolean(c, false, a, v));
      break;
    default:
      c->status.code = TLSF_DPA_INTERNAL;
      return DPA_BAD;
    }
  }
  uint32_t low = map_class(c, cl->low, mode, epoch, protect);
  uint32_t high = map_class(c, cl->high, mode, epoch, protect);
  uint32_t result = dpa_ite(c, v, high, low);
  if (slot)
    *slot = result;
  return result;
}

uint32_t dpa_unfold(TlsfDpa *c, uint32_t f) {
  return map_class(c, f, UNFOLD, 0, nullptr);
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
    protected_x(c, atom->lhs, true, protect, epoch);
    protected_x(c, atom->rhs, true, protect, epoch);
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
    bool *protect = dpa_alloc(c, c->atoms.n, sizeof *protect);
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
  if ((dpa_tags(c, r) & DPA_FINITE) && unfolded != f)
    r = dpa_remainder(c, unfolded);
  cl->remainder = r;
  return r;
}
