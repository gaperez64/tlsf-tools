#include "tlsf/recognize.h"

// ---------------------------------------------------------------------------
// Small AST-shape helpers (matching is on the original formula, not the NNF, so
// that `->` and `<->` shapes survive).
// ---------------------------------------------------------------------------

static int32_t ap_idx(ConstraintCover *cov, const Node *n) {
  return n->kind == NODE_AP ? ap_table_find(&cov->aps, n->name) : -1;
}
static bool is_output(ConstraintCover *cov, const Node *n) {
  int32_t i = ap_idx(cov, n);
  return i >= 0 && (ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT);
}

// G(r -> F g)  or  G(!r || F g)
static void match_response(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  const Node *guard = nullptr, *cons = nullptr;
  if (body->kind == NODE_IMPL) {
    guard = body->lhs;
    cons = body->rhs;
  } else if (body->kind == NODE_OR && body->lhs->kind == NODE_NOT) {
    guard = body->lhs->arg;
    cons = body->rhs;
  } else {
    return;
  }
  if (cons->kind != NODE_F)
    return;
  constraint_add_candidate(cov, c, "response");
  c->resp_guard = ap_idx(cov, guard);
  c->resp_target = ap_idx(cov, cons->arg);
}

// G F x  (records the target output when x is a plain output AP)
static void match_recurrence(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G || c->formula->arg->kind != NODE_F)
    return;
  constraint_add_candidate(cov, c, "pure-recurrence");
  const Node *x = c->formula->arg->arg;
  if (is_output(cov, x))
    c->rec_output = ap_idx(cov, x);
}

// F G x  (records the target output when x is a plain output AP)
static void match_persistence(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_F || c->formula->arg->kind != NODE_G)
    return;
  constraint_add_candidate(cov, c, "persistence");
  const Node *x = c->formula->arg->arg;
  if (is_output(cov, x))
    c->pers_output = ap_idx(cov, x);
}

// F g  (one-shot reachability of an output)
static void match_reachability(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_F)
    return;
  const Node *g = c->formula->arg;
  if (!is_output(cov, g))
    return;
  constraint_add_candidate(cov, c, "reachability");
  c->reach_output = ap_idx(cov, g);
}

// G(alpha -> o) / G(alpha -> !o)  (immediate reaction; o an output literal,
// consequent neither F nor X — those are response/guarded-next).
static void match_reaction(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_IMPL)
    return;
  const Node *o = body->rhs;
  if (o->kind == NODE_NOT)
    o = o->arg;
  if (o->kind != NODE_AP || !is_output(cov, o))
    return;
  constraint_add_candidate(cov, c, "reaction");
}

// G(X o <-> theta) / G(theta <-> X o)  (delayed definition / register), o
// output
static void match_delayed_definition(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_EQUIV)
    return;
  const Node *xside = body->lhs->kind == NODE_X   ? body->lhs
                      : body->rhs->kind == NODE_X ? body->rhs
                                                  : nullptr;
  if (!xside || !is_output(cov, xside->arg))
    return;
  constraint_add_candidate(cov, c, "delayed-definition");
  c->ddef_output = ap_idx(cov, xside->arg);
}

// G(alpha -> X o) / G(alpha -> X !o)
static void match_guarded_next(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_IMPL)
    return;
  const Node *cons = body->rhs;
  if (cons->kind != NODE_X)
    return;
  const Node *o = cons->arg;
  if (o->kind == NODE_NOT)
    o = o->arg;
  if (is_output(cov, o))
    constraint_add_candidate(cov, c, "guarded-next-assignment");
}

// G(o <-> theta), o an output
static void match_definition(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_EQUIV)
    return;
  if (is_output(cov, body->lhs)) {
    constraint_add_candidate(cov, c, "definition");
    c->def_output = ap_idx(cov, body->lhs);
  } else if (is_output(cov, body->rhs)) {
    constraint_add_candidate(cov, c, "definition");
    c->def_output = ap_idx(cov, body->rhs);
  }
}

// True if `n` mentions any temporal operator (so it is not purely Boolean).
static bool has_temporal(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return true;
  case NODE_NOT:
    return has_temporal(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return has_temporal(n->lhs) || has_temporal(n->rhs);
  default:
    return false;
  }
}

// G(B) with B a temporal-free Boolean body: a stateless safety invariant.
static void match_invariant(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  if (has_temporal(c->formula->arg))
    return;
  constraint_add_candidate(cov, c, "safety-invariant");
}

// Collect a mutex written as a conjunction of !(x && y) leaves.
static bool mutex_leaves(ConstraintCover *cov, Constraint *c, const Node *n) {
  if (n->kind == NODE_AND)
    return mutex_leaves(cov, c, n->lhs) && mutex_leaves(cov, c, n->rhs);
  if (n->kind == NODE_NOT && n->arg->kind == NODE_AND) {
    const Node *p = n->arg;
    int32_t li = ap_idx(cov, p->lhs), ri = ap_idx(cov, p->rhs);
    if (li < 0 || ri < 0)
      return false;
    apset_set(&c->mutex_members, (uint32_t)li);
    apset_set(&c->mutex_members, (uint32_t)ri);
    return true;
  }
  return false;
}

static void match_mutex(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  if (!mutex_leaves(cov, c, c->formula->arg))
    return;
  if (apset_count(&c->mutex_members) < 2)
    return;
  c->has_mutex = true;
  constraint_add_candidate(cov, c, "mutex");
}

// ---------------------------------------------------------------------------
// Block grouping over a common mutex:
//   responses    whose grant target is a mutex member  -> arbiter_candidate
//   recurrences  whose target output is a mutex member -> round_robin_candidate
// ---------------------------------------------------------------------------

// Members of constraint `mx`'s mutex whose `field` (resp_target / rec_output)
// matches; appends the matching constraint ids and finally the mutex id.
static void build_blocks(ConstraintCover *cov) {
  // Upper bound: two blocks (arbiter + round-robin) per mutex constraint.
  uint32_t nmutex = 0;
  for (uint32_t i = 0; i < cov->count; i++)
    if (cov->items[i].has_mutex)
      nmutex++;
  if (nmutex == 0)
    return;

  cov->blocks = ARENA_ALLOC_N(cov->arena, TemplateBlock, (size_t)2 * nmutex);
  cov->block_count = 0;

  for (uint32_t m = 0; m < cov->count; m++) {
    Constraint *mx = &cov->items[m];
    if (!mx->has_mutex)
      continue;

    // Arbiter: responses targeting a mutex member.
    uint32_t *aids = ARENA_ALLOC_N(cov->arena, uint32_t, cov->count);
    uint32_t an = 0;
    for (uint32_t r = 0; r < cov->count; r++)
      if (cov->items[r].resp_target >= 0 &&
          apset_test(&mx->mutex_members, (uint32_t)cov->items[r].resp_target))
        aids[an++] = cov->items[r].id;
    if (an >= 2) {
      aids[an++] = mx->id;
      cov->blocks[cov->block_count++] =
          (TemplateBlock){.template_name = "arbiter_candidate",
                          .constraint_ids = aids,
                          .count = an};
    }

    // Round-robin: recurrences whose target output is a mutex member.
    uint32_t *rids = ARENA_ALLOC_N(cov->arena, uint32_t, cov->count);
    uint32_t rn = 0;
    for (uint32_t r = 0; r < cov->count; r++)
      if (cov->items[r].rec_output >= 0 &&
          apset_test(&mx->mutex_members, (uint32_t)cov->items[r].rec_output))
        rids[rn++] = cov->items[r].id;
    if (rn >= 2) {
      rids[rn++] = mx->id;
      cov->blocks[cov->block_count++] =
          (TemplateBlock){.template_name = "round_robin_candidate",
                          .constraint_ids = rids,
                          .count = rn};
    }
  }
}

void recognize_all(ConstraintCover *cov) {
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *c = &cov->items[i];
    match_response(cov, c);
    match_recurrence(cov, c);
    match_persistence(cov, c);
    match_reachability(cov, c);
    match_guarded_next(cov, c);
    match_definition(cov, c);
    match_delayed_definition(cov, c);
    match_reaction(cov, c);
    match_mutex(cov, c);
    match_invariant(cov, c);
  }
  build_blocks(cov);
}
