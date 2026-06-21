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
static bool is_next_kind(NodeKind k) {
  return k == NODE_X || k == NODE_X_STRONG;
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

static bool has_output_ref(ConstraintCover *cov, const Node *n) {
  switch (n->kind) {
  case NODE_AP:
    return is_output(cov, n);
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return has_output_ref(cov, n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return has_output_ref(cov, n->lhs) || has_output_ref(cov, n->rhs);
  default:
    return false;
  }
}

static const Node *next_chain_target(const Node *n, uint32_t *steps,
                                     bool *strong) {
  *steps = 0;
  *strong = false;
  while (is_next_kind(n->kind)) {
    if (n->kind == NODE_X_STRONG)
      *strong = true;
    (*steps)++;
    n = n->arg;
  }
  return n;
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
  TemplateCandidate *tc =
      constraint_add_candidate_payload(cov, c, CAND_RESPONSE);
  if (tc) {
    tc->u.response.guard = ap_idx(cov, guard);
    tc->u.response.target = ap_idx(cov, cons->arg);
  }
}

// G F x  (records the target output when x is a plain output AP)
static void match_recurrence(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G || c->formula->arg->kind != NODE_F)
    return;
  constraint_add_candidate(cov, c, "pure-recurrence");
  const Node *x = c->formula->arg->arg;
  if (is_output(cov, x)) {
    TemplateCandidate *tc =
        constraint_add_candidate_payload(cov, c, CAND_RECURRENCE);
    if (tc)
      tc->u.recurrence.output = ap_idx(cov, x);
  }
}

// F G x  (records the target output when x is a plain output AP)
static void match_persistence(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_F || c->formula->arg->kind != NODE_G)
    return;
  constraint_add_candidate(cov, c, "persistence");
  const Node *x = c->formula->arg->arg;
  if (is_output(cov, x)) {
    TemplateCandidate *tc =
        constraint_add_candidate_payload(cov, c, CAND_PERSISTENCE);
    if (tc)
      tc->u.persistence.output = ap_idx(cov, x);
  }
}

// F g  (one-shot reachability of an output)
static void match_reachability(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_F)
    return;
  const Node *g = c->formula->arg;
  if (!is_output(cov, g))
    return;
  constraint_add_candidate(cov, c, "reachability");
  TemplateCandidate *tc =
      constraint_add_candidate_payload(cov, c, CAND_REACHABILITY);
  if (tc)
    tc->u.reachability.output = ap_idx(cov, g);
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

// G(alpha -> X^k o), k >= 2.  The k=1 case is handled by guarded-next.
static void match_fixed_delay_response(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_IMPL &&
      !(body->kind == NODE_OR && body->lhs->kind == NODE_NOT))
    return;
  const Node *cons = body->rhs;

  uint32_t steps;
  bool strong;
  const Node *target = next_chain_target(cons, &steps, &strong);
  (void)strong;
  if (steps < 2 || !is_output(cov, target))
    return;
  constraint_add_candidate(cov, c, "fixed-delay-response");
  TemplateCandidate *tc =
      constraint_add_candidate_payload(cov, c, CAND_FIXED_DELAY);
  if (tc) {
    tc->u.fixed_delay.output = ap_idx(cov, target);
    tc->u.fixed_delay.steps = steps;
  }
}

static bool recurrence_side(ConstraintCover *cov, const Node *n) {
  return n->kind == NODE_G && n->arg->kind == NODE_F &&
         is_output(cov, n->arg->arg);
}

static const Node *global_guard_side(const Node *n) {
  return n->kind == NODE_G ? n->arg : nullptr;
}

// G(phi) <-> G F o: a one-bit controller can output o until phi first fails.
static void match_global_recurrence_switch(ConstraintCover *cov,
                                           Constraint *c) {
  if (c->formula->kind != NODE_EQUIV)
    return;
  const Node *rec = nullptr;
  const Node *guard = nullptr;
  if (recurrence_side(cov, c->formula->lhs)) {
    rec = c->formula->lhs;
    guard = global_guard_side(c->formula->rhs);
  } else if (recurrence_side(cov, c->formula->rhs)) {
    rec = c->formula->rhs;
    guard = global_guard_side(c->formula->lhs);
  }
  if (!rec || !guard || has_temporal(guard) || has_output_ref(cov, guard))
    return;
  constraint_add_candidate(cov, c, "global-recurrence-switch");
}

// G(X o <-> theta) / G(theta <-> X o)  (also X[!]); delayed definition /
// register, o output.
static void match_delayed_definition(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_EQUIV)
    return;
  const Node *xside = is_next_kind(body->lhs->kind)   ? body->lhs
                      : is_next_kind(body->rhs->kind) ? body->rhs
                                                      : nullptr;
  if (!xside || !is_output(cov, xside->arg))
    return;
  constraint_add_candidate(cov, c, "delayed-definition");
  TemplateCandidate *tc =
      constraint_add_candidate_payload(cov, c, CAND_DELAYED_DEF);
  if (tc)
    tc->u.delayed_def.output = ap_idx(cov, xside->arg);
}

// G(alpha -> X o) / G(alpha -> X !o)  (also X[!])
static void match_guarded_next(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_IMPL)
    return;
  const Node *cons = body->rhs;
  if (!is_next_kind(cons->kind))
    return;
  const Node *o = cons->arg;
  if (o->kind == NODE_NOT)
    o = o->arg;
  if (is_output(cov, o))
    constraint_add_candidate(cov, c, "guarded-next-assignment");
}

// G(t -> (X o <-> !o)) / G(t -> (!o <-> X o))
static void match_toggle_register(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  const Node *body = c->formula->arg;
  if (body->kind != NODE_IMPL || body->rhs->kind != NODE_EQUIV)
    return;
  const Node *eq = body->rhs;
  const Node *lhs = eq->lhs;
  const Node *rhs = eq->rhs;
  if (!is_next_kind(lhs->kind)) {
    const Node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  if (!is_next_kind(lhs->kind) || lhs->arg->kind != NODE_AP ||
      rhs->kind != NODE_NOT || rhs->arg->kind != NODE_AP ||
      lhs->arg->name != rhs->arg->name || !is_output(cov, lhs->arg))
    return;
  constraint_add_candidate(cov, c, "toggle-register");
  TemplateCandidate *tc = constraint_add_candidate_payload(cov, c, CAND_TOGGLE);
  if (tc)
    tc->u.toggle.output = ap_idx(cov, lhs->arg);
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
    TemplateCandidate *tc =
        constraint_add_candidate_payload(cov, c, CAND_DEFINITION);
    if (tc)
      tc->u.definition.output = ap_idx(cov, body->lhs);
  } else if (is_output(cov, body->rhs)) {
    constraint_add_candidate(cov, c, "definition");
    TemplateCandidate *tc =
        constraint_add_candidate_payload(cov, c, CAND_DEFINITION);
    if (tc)
      tc->u.definition.output = ap_idx(cov, body->rhs);
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
static bool mutex_leaves(ConstraintCover *cov, ApSet *members, const Node *n) {
  if (n->kind == NODE_AND)
    return mutex_leaves(cov, members, n->lhs) &&
           mutex_leaves(cov, members, n->rhs);
  if (n->kind == NODE_NOT && n->arg->kind == NODE_AND) {
    const Node *p = n->arg;
    int32_t li = ap_idx(cov, p->lhs), ri = ap_idx(cov, p->rhs);
    if (li < 0 || ri < 0)
      return false;
    apset_set(members, (uint32_t)li);
    apset_set(members, (uint32_t)ri);
    return true;
  }
  return false;
}

static void match_mutex(ConstraintCover *cov, Constraint *c) {
  if (c->formula->kind != NODE_G)
    return;
  ApSet members;
  apset_init(&members, cov->arena, cov->aps.count);
  if (!mutex_leaves(cov, &members, c->formula->arg))
    return;
  if (apset_count(&members) < 2)
    return;
  constraint_add_candidate(cov, c, "mutex");
  TemplateCandidate *tc = constraint_add_candidate_payload(cov, c, CAND_MUTEX);
  if (tc)
    tc->u.mutex.members = members;
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
    if (constraint_find_candidate_payload(cov, &cov->items[i], CAND_MUTEX))
      nmutex++;
  if (nmutex == 0)
    return;

  cov->blocks = ARENA_ALLOC_N(cov->arena, TemplateBlock, (size_t)2 * nmutex);
  cov->block_count = 0;

  for (uint32_t m = 0; m < cov->count; m++) {
    Constraint *mx = &cov->items[m];
    const TemplateCandidate *mutex =
        constraint_find_candidate_payload(cov, mx, CAND_MUTEX);
    if (!mutex)
      continue;

    // Arbiter: responses targeting a mutex member.
    uint32_t *aids = ARENA_ALLOC_N(cov->arena, uint32_t, cov->count);
    uint32_t an = 0;
    for (uint32_t r = 0; r < cov->count; r++) {
      const TemplateCandidate *resp =
          constraint_find_candidate_payload(cov, &cov->items[r], CAND_RESPONSE);
      if (resp && resp->u.response.target >= 0 &&
          apset_test(&mutex->u.mutex.members,
                     (uint32_t)resp->u.response.target))
        aids[an++] = cov->items[r].id;
    }
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
    for (uint32_t r = 0; r < cov->count; r++) {
      const TemplateCandidate *rec = constraint_find_candidate_payload(
          cov, &cov->items[r], CAND_RECURRENCE);
      if (rec && rec->u.recurrence.output >= 0 &&
          apset_test(&mutex->u.mutex.members,
                     (uint32_t)rec->u.recurrence.output))
        rids[rn++] = cov->items[r].id;
    }
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
    match_fixed_delay_response(cov, c);
    match_global_recurrence_switch(cov, c);
    match_toggle_register(cov, c);
    match_guarded_next(cov, c);
    match_definition(cov, c);
    match_delayed_definition(cov, c);
    match_reaction(cov, c);
    match_mutex(cov, c);
    match_invariant(cov, c);
  }
  build_blocks(cov);
}
