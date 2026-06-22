// templates_certify.c — per-template recognizers and certifiers for the CSNF
// model.  Each certify_* scans the constraint cover for one template family's
// syntactic shape and, when certifying, records the matching controller
// artifacts in its Block.  The recognizer helpers (parse_*, has_*, guard_*) are
// private to this file; the certifiers are dispatched from templates_certify()
// in templates.c.  Shared model types (Block, Csnf) live in
// templates_internal.h.

#include "tlsf/templates_internal.h"

#include "tlsf/apset.h"
#include "tlsf/arena.h"
#include "tlsf/rewrite.h"

#include <stdlib.h>
#include <string.h>

static Block *new_block(Csnf *c) {
  if (c->nblocks == c->bcap) {
    uint32_t ncap = c->bcap ? c->bcap * 2 : 8;
    Block *nb = realloc(c->blocks, ncap * sizeof(Block));
    if (!nb)
      return nullptr; // OOM: caller skips this block
    c->blocks = nb;
    c->bcap = ncap;
  }
  Block *b = &c->blocks[c->nblocks++];
  *b = (Block){.dec_output = -1,
               .nsf_output = -1,
               .sr_output = -1,
               .tog_output = -1,
               .fdelay_output = -1,
               .db_output = -1,
               .one_output = -1,
               .hold_output = -1,
               .resp_output = -1,
               .asg_output = -1,
               .reg_output = -1};
  return b;
}

static int32_t candidate_output(ConstraintCover *cov, const Constraint *c,
                                CandidateKind kind) {
  const TemplateCandidate *tc = constraint_find_candidate_payload(cov, c, kind);
  if (!tc)
    return -1;
  switch (kind) {
  case CAND_DEFINITION:
    return tc->u.definition.output;
  case CAND_RECURRENCE:
    return tc->u.recurrence.output;
  case CAND_REACHABILITY:
    return tc->u.reachability.output;
  case CAND_PERSISTENCE:
    return tc->u.persistence.output;
  case CAND_DELAYED_DEF:
    return tc->u.delayed_def.output;
  case CAND_TOGGLE:
    return tc->u.toggle.output;
  case CAND_FIXED_DELAY:
    return tc->u.fixed_delay.output;
  default:
    return -1;
  }
}

static const ResponseCandidate *response_candidate(ConstraintCover *cov,
                                                   const Constraint *c) {
  const TemplateCandidate *tc =
      constraint_find_candidate_payload(cov, c, CAND_RESPONSE);
  return tc ? &tc->u.response : nullptr;
}

static void guard_literals(ConstraintCover *cov, const Node *n, ApSet *pos,
                           ApSet *neg) {
  if (n->kind == NODE_AND) {
    guard_literals(cov, n->lhs, pos, neg);
    guard_literals(cov, n->rhs, pos, neg);
  } else if (n->kind == NODE_AP) {
    int32_t i = ap_table_find(&cov->aps, n->name);
    if (i >= 0)
      apset_set(pos, (uint32_t)i);
  } else if (n->kind == NODE_NOT && n->arg->kind == NODE_AP) {
    int32_t i = ap_table_find(&cov->aps, n->arg->name);
    if (i >= 0)
      apset_set(neg, (uint32_t)i);
  }
}

static bool sets_intersect(const ApSet *a, const ApSet *b) {
  for (uint32_t i = 0; i < a->nbits; i++)
    if (apset_test(a, i) && apset_test(b, i))
      return true;
  return false;
}

static bool guard_pairs_exclusive(ConstraintCover *cov, const Node **pos,
                                  uint32_t npos, const Node **neg,
                                  uint32_t nneg) {
  uint32_t A = cov->aps.count;
  for (uint32_t a = 0; a < npos; a++)
    for (uint32_t b = 0; b < nneg; b++) {
      ApSet ap, an, bp, bn;
      apset_init(&ap, cov->arena, A);
      apset_init(&an, cov->arena, A);
      apset_init(&bp, cov->arena, A);
      apset_init(&bn, cov->arena, A);
      guard_literals(cov, pos[a], &ap, &an);
      guard_literals(cov, neg[b], &bp, &bn);
      if (!sets_intersect(&ap, &bn) && !sets_intersect(&an, &bp))
        return false;
    }
  return true;
}

static bool is_next_kind(NodeKind k) {
  return k == NODE_X || k == NODE_X_STRONG;
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

// Parse G(alpha -> X o) / G(alpha -> X !o) (also X[!]); returns guard, output
// index, sign, and whether the next operator is strong.
static bool parse_guarded_next(ConstraintCover *cov, const Constraint *c,
                               const Node **alpha, int32_t *out, bool *neg,
                               bool *strong) {
  if (constraint_match_formula(c)->kind != NODE_G ||
      constraint_match_formula(c)->arg->kind != NODE_IMPL)
    return false;
  const Node *body = constraint_match_formula(c)->arg;
  if (!is_next_kind(body->rhs->kind))
    return false;
  *strong = body->rhs->kind == NODE_X_STRONG;
  const Node *t = body->rhs->arg;
  *neg = false;
  if (t->kind == NODE_NOT) {
    *neg = true;
    t = t->arg;
  }
  if (t->kind != NODE_AP)
    return false;
  int32_t i = ap_table_find(&cov->aps, t->name);
  if (i < 0 || !(ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT))
    return false;
  *alpha = body->lhs;
  *out = i;
  return true;
}

// Parse G(t -> (X o <-> !o)) / G(t -> (!o <-> X o)); returns trigger, output
// index, and whether the next operator is strong.
static bool parse_toggle(ConstraintCover *cov, const Constraint *c,
                         const Node **trigger, int32_t *out, bool *strong) {
  if (constraint_match_formula(c)->kind != NODE_G ||
      constraint_match_formula(c)->arg->kind != NODE_IMPL)
    return false;
  const Node *body = constraint_match_formula(c)->arg;
  if (body->rhs->kind != NODE_EQUIV)
    return false;
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
      lhs->arg->name != rhs->arg->name)
    return false;
  *strong = lhs->kind == NODE_X_STRONG;
  int32_t i = ap_table_find(&cov->aps, lhs->arg->name);
  if (i < 0 || !(ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT))
    return false;
  *trigger = body->lhs;
  *out = i;
  return true;
}

// Parse G(alpha -> X^k o), k >= 2.  The k=1 case is the guarded-next template.
static bool parse_fixed_delay_response(ConstraintCover *cov,
                                       const Constraint *c, const Node **guard,
                                       int32_t *out, uint32_t *steps,
                                       bool *strong) {
  if (constraint_match_formula(c)->kind != NODE_G)
    return false;
  const Node *body = constraint_match_formula(c)->arg;
  const Node *cons = nullptr;
  if (body->kind == NODE_IMPL) {
    *guard = body->lhs;
    cons = body->rhs;
  } else if (body->kind == NODE_OR && body->lhs->kind == NODE_NOT) {
    *guard = body->lhs->arg;
    cons = body->rhs;
  } else {
    return false;
  }

  const Node *target = next_chain_target(cons, steps, strong);
  if (*steps < 2 || target->kind != NODE_AP)
    return false;
  int32_t i = ap_table_find(&cov->aps, target->name);
  if (i < 0 || !(ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT))
    return false;
  *out = i;
  return true;
}

static bool has_cand(const Constraint *c, const char *name) {
  for (uint16_t i = 0; i < c->candidate_count; i++)
    if (strcmp(c->candidates[i], name) == 0)
      return true;
  return false;
}

// True if output `o` appears in no constraint outside the given block.  This is
// the "free output" side condition: when it holds, a controller for `o` cannot
// violate any other constraint, so the block can be solved in isolation.
static bool output_is_free(ConstraintCover *cov, const uint32_t *block_ids,
                           uint32_t nblk, uint32_t o) {
  for (uint32_t i = 0; i < cov->count; i++) {
    bool inblk = false;
    for (uint32_t k = 0; k < nblk; k++)
      if (block_ids[k] == i)
        inblk = true;
    if (inblk)
      continue;
    if (apset_test(&cov->items[i].outputs, o))
      return false;
  }
  return true;
}

// True if `n` mentions a next operator (decoder/assignment causality check).
static bool has_next(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
    return true;
  case NODE_NOT:
  case NODE_F:
  case NODE_G:
    return has_next(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return has_next(n->lhs) || has_next(n->rhs);
  default:
    return false;
  }
}

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
  case NODE_AP: {
    int32_t i = ap_table_find(&cov->aps, n->name);
    return i >= 0 && (ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT);
  }
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

// Parse G(alpha -> o) / G(alpha -> !o); returns guard, output index, sign.
static bool parse_reaction(ConstraintCover *cov, const Constraint *c,
                           const Node **alpha, int32_t *out, bool *neg) {
  if (constraint_match_formula(c)->kind != NODE_G ||
      constraint_match_formula(c)->arg->kind != NODE_IMPL)
    return false;
  const Node *body = constraint_match_formula(c)->arg;
  const Node *t = body->rhs;
  *neg = false;
  if (t->kind == NODE_NOT) {
    *neg = true;
    t = t->arg;
  }
  if (t->kind != NODE_AP)
    return false;
  int32_t i = ap_table_find(&cov->aps, t->name);
  if (i < 0 || !(ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT))
    return false;
  *alpha = body->lhs;
  *out = i;
  return true;
}

static bool parse_global_recurrence_switch(ConstraintCover *cov,
                                           const Constraint *c,
                                           const Node **guard, int32_t *out) {
  if (constraint_match_formula(c)->kind != NODE_EQUIV)
    return false;
  const Node *lhs = constraint_match_formula(c)->lhs;
  const Node *rhs = constraint_match_formula(c)->rhs;
  const Node *rec = nullptr;
  const Node *gside = nullptr;
  if (lhs->kind == NODE_G && lhs->arg->kind == NODE_F) {
    rec = lhs;
    gside = rhs;
  } else if (rhs->kind == NODE_G && rhs->arg->kind == NODE_F) {
    rec = rhs;
    gside = lhs;
  } else {
    return false;
  }
  if (gside->kind != NODE_G)
    return false;
  const Node *target = rec->arg->arg;
  if (target->kind != NODE_AP)
    return false;
  int32_t i = ap_table_find(&cov->aps, target->name);
  if (i < 0 || !(ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT))
    return false;
  const Node *body = gside->arg;
  if (has_temporal(body) || has_output_ref(cov, body))
    return false;
  *guard = body;
  *out = i;
  return true;
}

// ---------------------------------------------------------------------------
// Certification
// ---------------------------------------------------------------------------

void certify_round_robin(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_ROUND_ROBIN))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t b = 0; b < cov->block_count; b++) {
    TemplateBlock *tb = &cov->blocks[b];
    if (strcmp(tb->template_name, "round_robin_candidate") != 0)
      continue;

    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "round-robin";
    blk->ncids = tb->count;
    blk->cids = malloc(tb->count * sizeof(uint32_t));
    memcpy(blk->cids, tb->constraint_ids, tb->count * sizeof(uint32_t));

    // Recurrence outputs in this block.
    int32_t *outs = malloc(tb->count * sizeof(int32_t));
    uint32_t no = 0;
    for (uint32_t k = 0; k < tb->count; k++) {
      Constraint *m = &cov->items[tb->constraint_ids[k]];
      int32_t rec_output = candidate_output(cov, m, CAND_RECURRENCE);
      if (rec_output >= 0)
        outs[no++] = rec_output;
    }

    // Side condition: those outputs occur in no constraint outside the block.
    bool disjoint = true;
    if (certify) {
      for (uint32_t i = 0; i < cov->count && disjoint; i++) {
        bool inblk = false;
        for (uint32_t k = 0; k < tb->count; k++)
          if (tb->constraint_ids[k] == i)
            inblk = true;
        if (inblk)
          continue;
        for (uint32_t j = 0; j < no; j++)
          if (apset_test(&cov->items[i].outputs, (uint32_t)outs[j])) {
            disjoint = false;
            break;
          }
      }
    }

    if (certify && disjoint) {
      blk->status = CSNF_SOLVED;
      blk->cert = "round_robin_scheduler";
      blk->cyc_outputs = outs;
      blk->cyc_n = no;
      for (uint32_t k = 0; k < tb->count; k++) {
        c->solved[tb->constraint_ids[k]] = true;
        c->claimed[tb->constraint_ids[k]] = true;
      }
    } else {
      blk->status = CSNF_CANDIDATE;
      blk->cyc_outputs = outs;
      blk->cyc_n = no;
      for (uint32_t k = 0; k < tb->count; k++)
        c->claimed[tb->constraint_ids[k]] = true; // mutex consumed regardless
    }
  }
}

void certify_definition(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_DEFINITION))
    return;
  ConstraintCover *cov = c->cov;
  bool moore = semantics_is_moore(cov->spec->info.semantics);
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    int32_t def_output = candidate_output(cov, cc, CAND_DEFINITION);
    if (c->claimed[i] || !has_cand(cc, "definition") || def_output < 0)
      continue;
    const Node *eq = constraint_match_formula(cc)->arg; // G(<eq>)
    const char *oname = ap_table_name(&cov->aps, (uint32_t)def_output);
    const Node *theta = (eq->lhs->kind == NODE_AP && eq->lhs->name == oname)
                            ? eq->rhs
                            : eq->lhs;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "definition";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    // Sound iff Mealy, combinational (theta has no X), and acyclic (o not in
    // theta).  Unlike the constant controllers, a decoder sets o to its defined
    // value, so other constraints that only *read* o are fine; only a separate
    // constraint on o's value could conflict (see caveat in BENCHGRAPH.md).
    if (certify && !moore && !has_next(theta) && !occurs_in(theta, oname)) {
      blk->status = CSNF_SOLVED;
      blk->cert = "definition_decoder";
      blk->dec_output = def_output;
      blk->dec_theta = theta;
      c->solved[i] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
      blk->dec_output = def_output;
      blk->dec_theta = theta;
    }
    c->claimed[i] = true;
  }
}

void certify_set_reset_register(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_SET_RESET))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;

  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;

    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    const Node **sets = malloc(cov->count * sizeof(Node *));
    const Node **resets = malloc(cov->count * sizeof(Node *));
    uint32_t nid = 0, ns = 0, nr = 0;
    bool strong_next_sound = true;

    for (uint32_t i = 0; i < cov->count; i++) {
      if (c->claimed[i] || !has_cand(&cov->items[i], "guarded-next-assignment"))
        continue;
      const Node *alpha;
      int32_t out;
      bool neg, strong;
      if (!parse_guarded_next(cov, &cov->items[i], &alpha, &out, &neg,
                              &strong) ||
          (uint32_t)out != o)
        continue;
      ids[nid++] = i;
      if (neg)
        resets[nr++] = alpha;
      else
        sets[ns++] = alpha;
      if (strong && semantics_is_finite(cov->spec->info.semantics))
        strong_next_sound = false;
    }

    if (ns == 0 || nr == 0) {
      free(ids);
      free(sets);
      free(resets);
      continue;
    }

    bool exclusive = true;
    if (certify)
      exclusive = guard_pairs_exclusive(cov, sets, ns, resets, nr);

    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      free(sets);
      free(resets);
      return;
    }
    blk->name = "set-reset-register";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->sr_output = (int32_t)o;
    blk->sr_set_guards = malloc(ns * sizeof(Node *));
    blk->sr_reset_guards = malloc(nr * sizeof(Node *));
    memcpy(blk->sr_set_guards, sets, ns * sizeof(Node *));
    memcpy(blk->sr_reset_guards, resets, nr * sizeof(Node *));
    blk->sr_nsets = ns;
    blk->sr_nresets = nr;

    if (certify && exclusive && strong_next_sound) {
      blk->status = CSNF_SOLVED;
      blk->cert = "set_reset_register";
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }

    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
    free(sets);
    free(resets);
  }
}

void certify_toggle_register(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_TOGGLE))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;

  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;

    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    const Node **triggers = malloc(cov->count * sizeof(Node *));
    uint32_t nid = 0, nt = 0;
    bool strong_next_sound = true;

    for (uint32_t i = 0; i < cov->count; i++) {
      if (c->claimed[i] || !has_cand(&cov->items[i], "toggle-register"))
        continue;
      const Node *trigger;
      int32_t out;
      bool strong;
      if (!parse_toggle(cov, &cov->items[i], &trigger, &out, &strong) ||
          (uint32_t)out != o)
        continue;
      ids[nid++] = i;
      triggers[nt++] = trigger;
      if (strong && semantics_is_finite(cov->spec->info.semantics))
        strong_next_sound = false;
    }

    if (nid == 0) {
      free(ids);
      free(triggers);
      continue;
    }

    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      free(triggers);
      return;
    }
    blk->name = "toggle-register";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->tog_output = (int32_t)o;
    blk->tog_guards = malloc(nt * sizeof(Node *));
    memcpy(blk->tog_guards, triggers, nt * sizeof(Node *));
    blk->tog_nguards = nt;

    if (certify && strong_next_sound) {
      blk->status = CSNF_SOLVED;
      blk->cert = "toggle_register";
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }

    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
    free(triggers);
  }
}

void certify_fixed_delay_response(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_FIXED_DELAY))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;

  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;

    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    const Node **guards = malloc(cov->count * sizeof(Node *));
    uint32_t *steps = malloc(cov->count * sizeof(uint32_t));
    uint32_t nid = 0, nd = 0;
    bool strong_next_sound = true;

    for (uint32_t i = 0; i < cov->count; i++) {
      if (c->claimed[i] || !has_cand(&cov->items[i], "fixed-delay-response"))
        continue;
      const Node *guard;
      int32_t out;
      uint32_t delay;
      bool strong;
      if (!parse_fixed_delay_response(cov, &cov->items[i], &guard, &out, &delay,
                                      &strong) ||
          (uint32_t)out != o)
        continue;
      ids[nid++] = i;
      guards[nd] = guard;
      steps[nd++] = delay;
      if (strong && semantics_is_finite(cov->spec->info.semantics))
        strong_next_sound = false;
    }

    if (nid == 0) {
      free(ids);
      free(guards);
      free(steps);
      continue;
    }

    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      free(guards);
      free(steps);
      return;
    }
    blk->name = "fixed-delay-response";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->fdelay_output = (int32_t)o;
    blk->fdelay_guards = malloc(nd * sizeof(Node *));
    blk->fdelay_steps = malloc(nd * sizeof(uint32_t));
    memcpy(blk->fdelay_guards, guards, nd * sizeof(Node *));
    memcpy(blk->fdelay_steps, steps, nd * sizeof(uint32_t));
    blk->fdelay_n = nd;

    if (certify && strong_next_sound && output_is_free(cov, ids, nid, o)) {
      blk->status = CSNF_SOLVED;
      blk->cert = "fixed_delay_response";
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }

    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
    free(guards);
    free(steps);
  }
}

void certify_global_recurrence_switch(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_GLOBAL_RECURRENCE))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    if (c->claimed[i] || !has_cand(cc, "global-recurrence-switch"))
      continue;
    const Node *guard;
    int32_t out;
    if (!parse_global_recurrence_switch(cov, cc, &guard, &out))
      continue;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "global-recurrence-switch";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    blk->db_output = out;
    blk->db_guard = guard;
    if (certify && !semantics_is_finite(cov->spec->info.semantics) &&
        output_is_free(cov, &i, 1, (uint32_t)out)) {
      blk->status = CSNF_SOLVED;
      blk->cert = "global_recurrence_switch";
      c->solved[i] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    c->claimed[i] = true;
  }
}

void certify_guarded_next(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_GUARDED_NEXT))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;

  // Group guarded-next constraints by their assigned output.
  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;
    // collect force-true / force-false members for output o
    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    const Node **trues = malloc(cov->count * sizeof(Node *));
    const Node **falses = malloc(cov->count * sizeof(Node *));
    uint32_t nid = 0, nt = 0, nf = 0;
    bool strong_next_sound = true;
    for (uint32_t i = 0; i < cov->count; i++) {
      if (c->claimed[i] || !has_cand(&cov->items[i], "guarded-next-assignment"))
        continue;
      const Node *alpha;
      int32_t out;
      bool neg, strong;
      if (!parse_guarded_next(cov, &cov->items[i], &alpha, &out, &neg,
                              &strong) ||
          (uint32_t)out != o)
        continue;
      ids[nid++] = i;
      if (neg)
        falses[nf++] = alpha;
      else
        trues[nt++] = alpha;
      if (strong && semantics_is_finite(cov->spec->info.semantics))
        strong_next_sound = false;
    }
    if (nid == 0) {
      free(ids);
      free(trues);
      free(falses);
      continue;
    }

    // Exclusivity: every (true-guard, false-guard) pair shares an opposite
    // literal (sufficient for the assignment o' := OR(true-guards) to be
    // consistent).  Trivially satisfied when there are no force-false guards.
    bool exclusive = true;
    if (certify)
      exclusive = guard_pairs_exclusive(cov, trues, nt, falses, nf);

    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      free(trues);
      free(falses);
      return;
    }
    blk->name = "guarded-next-assignment";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->nsf_output = (int32_t)o;
    if (certify && exclusive && strong_next_sound) {
      blk->status = CSNF_SOLVED;
      blk->cert = "guarded_assignment_consistency";
      blk->nsf_guards = malloc((nt ? nt : 1) * sizeof(Node *));
      memcpy(blk->nsf_guards, trues, nt * sizeof(Node *));
      blk->nsf_nguards = nt;
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
    free(trues);
    free(falses);
  }
}

void certify_mutex(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_MUTEX))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    if (c->claimed[i] ||
        !constraint_find_candidate_payload(cov, cc, CAND_MUTEX))
      continue;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "mutex";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    // A mutex is a certified safety invariant, but not solved on its own.
    blk->status = certify ? CSNF_CERTIFIED : CSNF_CANDIDATE;
    blk->cert = certify ? "mutex_safety" : nullptr;
    c->claimed[i] = true;
  }
}

// Fair arbiter: a grant-mutex with >=2 responses targeting its members.  A fair
// round-robin/queue scheduler over the grants satisfies every G(r -> F g) while
// respecting the mutex, provided the grants are controllable outputs free
// outside the block and each request is an environment input.
void certify_arbiter(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_ARBITER))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t b = 0; b < cov->block_count; b++) {
    TemplateBlock *tb = &cov->blocks[b];
    if (strcmp(tb->template_name, "arbiter_candidate") != 0)
      continue;
    bool any_claimed = false;
    for (uint32_t k = 0; k < tb->count; k++)
      if (c->claimed[tb->constraint_ids[k]])
        any_claimed = true;
    if (any_claimed)
      continue;

    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "arbiter";
    blk->ncids = tb->count;
    blk->cids = malloc(tb->count * sizeof(uint32_t));
    memcpy(blk->cids, tb->constraint_ids, tb->count * sizeof(uint32_t));

    int32_t *grants = malloc(tb->count * sizeof(int32_t));
    uint32_t ng = 0;
    bool ok = true;
    for (uint32_t k = 0; k < tb->count; k++) {
      Constraint *m = &cov->items[tb->constraint_ids[k]];
      const ResponseCandidate *resp = response_candidate(cov, m);
      if (!resp || resp->target < 0)
        continue; // the mutex member
      grants[ng++] = resp->target;
      if (resp->guard < 0 ||
          !(ap_table_flags(&cov->aps, (uint32_t)resp->guard) & AP_FLAG_INPUT))
        ok = false; // request is not a plain environment input
    }
    if (certify && ok)
      for (uint32_t j = 0; j < ng && ok; j++)
        if (!output_is_free(cov, tb->constraint_ids, tb->count,
                            (uint32_t)grants[j]))
          ok = false;

    blk->arb_outputs = grants;
    blk->arb_n = ng;
    if (certify && ok) {
      blk->status = CSNF_SOLVED;
      blk->cert = "fair_arbiter";
      for (uint32_t k = 0; k < tb->count; k++)
        c->solved[tb->constraint_ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    for (uint32_t k = 0; k < tb->count; k++)
      c->claimed[tb->constraint_ids[k]] = true; // mutex consumed regardless
  }
}

// Fair server: all responses G(rₖ -> F g) targeting the same grant g are served
// by one composable, interleavable controller (a fair scheduler over the
// pending requests) rather than the monopolizing g := true.  Grouping responses
// on a shared g into ONE block means the block drives g once -- no
// self-collision
// -- so two requests to the same resource compose instead of conflicting.
void certify_response(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_RESPONSE))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;
  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;
    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    uint32_t nid = 0;
    for (uint32_t i = 0; i < cov->count; i++) {
      const ResponseCandidate *resp = response_candidate(cov, &cov->items[i]);
      if (!c->claimed[i] && has_cand(&cov->items[i], "response") && resp &&
          resp->target == (int32_t)o)
        ids[nid++] = i;
    }
    if (nid == 0) {
      free(ids);
      continue;
    }
    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      return;
    }
    blk->name = "server";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->resp_output = (int32_t)o;
    // A fair server owns g (no closed-form value to substitute), so it composes
    // only when g is otherwise free; merging the requests on g first means a
    // shared resource is one server, not a self-collision.
    if (certify && output_is_free(cov, ids, nid, o)) {
      blk->status = CSNF_SOLVED;
      blk->cert = nid > 1 ? "fair_server" : "response_controller";
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
  }
}

// Persistence FG o: a free controllable output is held true forever.
void certify_persistence(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_PERSISTENCE))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    int32_t pers_output = candidate_output(cov, cc, CAND_PERSISTENCE);
    if (c->claimed[i] || !has_cand(cc, "persistence") || pers_output < 0)
      continue;
    uint32_t o = (uint32_t)pers_output;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "persistence";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    blk->hold_output = (int32_t)o;
    if (certify) {
      blk->status = CSNF_SOLVED;
      blk->cert = "persistence_latch";
      c->solved[i] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    c->claimed[i] = true;
  }
}

// Reachability F o: a free controllable output is asserted (set true at once).
void certify_reachability(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_REACHABILITY))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    int32_t reach_output = candidate_output(cov, cc, CAND_REACHABILITY);
    if (c->claimed[i] || !has_cand(cc, "reachability") || reach_output < 0)
      continue;
    uint32_t o = (uint32_t)reach_output;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "reachability";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    blk->one_output = (int32_t)o;
    if (certify) {
      blk->status = CSNF_SOLVED;
      blk->cert = "reachability_oneshot";
      c->solved[i] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    c->claimed[i] = true;
  }
}

// Immediate reaction G(a -> o) / G(b -> !o): combinational assignment
// o := OR(true-guards), sound in Mealy semantics when every (true, false) guard
// pair is provably exclusive.  The assigned output is eliminated by
// substitution during composition, so other constraints may still read it.
void certify_reaction(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_REACTION))
    return;
  ConstraintCover *cov = c->cov;
  bool moore = semantics_is_moore(cov->spec->info.semantics);
  uint32_t A = cov->aps.count;
  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;
    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    const Node **trues = malloc(cov->count * sizeof(Node *));
    const Node **falses = malloc(cov->count * sizeof(Node *));
    uint32_t nid = 0, nt = 0, nf = 0;
    for (uint32_t i = 0; i < cov->count; i++) {
      if (c->claimed[i] || !has_cand(&cov->items[i], "reaction"))
        continue;
      const Node *alpha;
      int32_t out;
      bool neg;
      if (!parse_reaction(cov, &cov->items[i], &alpha, &out, &neg) ||
          (uint32_t)out != o)
        continue;
      ids[nid++] = i;
      if (neg)
        falses[nf++] = alpha;
      else
        trues[nt++] = alpha;
    }
    if (nid == 0) {
      free(ids);
      free(trues);
      free(falses);
      continue;
    }

    bool exclusive = true;
    if (certify)
      exclusive = guard_pairs_exclusive(cov, trues, nt, falses, nf);
    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      free(trues);
      free(falses);
      return;
    }
    blk->name = "reaction";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->asg_output = (int32_t)o;
    if (certify && exclusive && !moore && output_is_free(cov, ids, nid, o)) {
      blk->status = CSNF_SOLVED;
      blk->cert = "reaction_consistency";
      blk->asg_guards = malloc((nt ? nt : 1) * sizeof(Node *));
      memcpy(blk->asg_guards, trues, nt * sizeof(Node *));
      blk->asg_nguards = nt;
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
    free(trues);
    free(falses);
  }
}

// Delayed definition G(X o <-> theta) (also X[!]): a register o' := theta.
// theta is over the current step (it may reference o — a sequential, not
// combinational, dependency), so it must be causal (no X) and o free outside
// the block.  Under finite semantics, X[!] candidates are recognized but not
// solved by this closed-form register template.
void certify_delayed_definition(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_DELAYED_DEF))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    int32_t ddef_output = candidate_output(cov, cc, CAND_DELAYED_DEF);
    if (c->claimed[i] || !has_cand(cc, "delayed-definition") || ddef_output < 0)
      continue;
    const Node *eq = constraint_match_formula(cc)->arg; // G(<eq>)
    bool strong =
        eq->lhs->kind == NODE_X_STRONG || eq->rhs->kind == NODE_X_STRONG;
    const Node *theta = is_next_kind(eq->lhs->kind) ? eq->rhs : eq->lhs;
    uint32_t o = (uint32_t)ddef_output;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "delayed-definition";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    blk->reg_output = (int32_t)o;
    blk->reg_theta = theta;
    if (certify &&
        (!strong || !semantics_is_finite(cov->spec->info.semantics)) &&
        !has_next(theta) && output_is_free(cov, &i, 1, o)) {
      blk->status = CSNF_SOLVED;
      blk->cert = "delayed_definition_register";
      c->solved[i] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    c->claimed[i] = true;
  }
}

// ---------------------------------------------------------------------------
// Stateless safety invariant: G(B), B temporal-free.  When the outputs in B are
// free, a memoryless Skolem controller realises it iff forall inputs exists
// outputs B; the outputs are then eliminated from the residual by substitution.
// ---------------------------------------------------------------------------

// Evaluate a temporal-free Boolean node under `val` (indexed by AP index).
static bool eval_bool(ConstraintCover *cov, const Node *n, const bool *val) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_FALSE:
    return false;
  case NODE_AP: {
    int32_t i = ap_table_find(&cov->aps, n->name);
    return i >= 0 && val[i];
  }
  case NODE_NOT:
    return !eval_bool(cov, n->arg, val);
  case NODE_AND:
    return eval_bool(cov, n->lhs, val) && eval_bool(cov, n->rhs, val);
  case NODE_OR:
    return eval_bool(cov, n->lhs, val) || eval_bool(cov, n->rhs, val);
  case NODE_IMPL:
    return !eval_bool(cov, n->lhs, val) || eval_bool(cov, n->rhs, val);
  case NODE_EQUIV:
    return eval_bool(cov, n->lhs, val) == eval_bool(cov, n->rhs, val);
  default:
    return false; // temporal-free guaranteed by the recognizer
  }
}

// True if `B` holds for every assignment of `vars` (a bounded tautology test).
static bool is_taut(ConstraintCover *cov, const Node *B, const uint32_t *vars,
                    uint32_t nv) {
  bool *val = calloc(cov->aps.count ? cov->aps.count : 1, sizeof(bool));
  if (!val)
    return false;
  bool taut = true;
  for (uint64_t m = 0; m < (1ull << nv) && taut; m++) {
    for (uint32_t b = 0; b < nv; b++)
      val[vars[b]] = (m >> b) & 1;
    if (!eval_bool(cov, B, val))
      taut = false;
  }
  free(val);
  return taut;
}

// forall input assignment, exists output assignment making B true.
static bool forall_exists(ConstraintCover *cov, const Node *B,
                          const uint32_t *ins, uint32_t ni,
                          const uint32_t *outs, uint32_t no) {
  bool *val = calloc(cov->aps.count ? cov->aps.count : 1, sizeof(bool));
  if (!val)
    return false;
  bool ok = true;
  for (uint64_t im = 0; im < (1ull << ni) && ok; im++) {
    for (uint32_t b = 0; b < ni; b++)
      val[ins[b]] = (im >> b) & 1;
    bool exists = false;
    for (uint64_t om = 0; om < (1ull << no) && !exists; om++) {
      for (uint32_t b = 0; b < no; b++)
        val[outs[b]] = (om >> b) & 1;
      if (eval_bool(cov, B, val))
        exists = true;
    }
    if (!exists)
      ok = false;
  }
  free(val);
  return ok;
}

// exists (outputs q[0..nq)) B == OR over their 2^nq settings of B with them
// fixed; result is a node over the remaining variables.
static const Node *exists_outputs(Csnf *c, const Node *B, const uint32_t *q,
                                  uint32_t nq) {
  Arena *a = c->cov->arena;
  const Node *acc = nullptr;
  for (uint64_t m = 0; m < (1ull << nq); m++) {
    const Node *t = B;
    for (uint32_t b = 0; b < nq; b++)
      t = node_subst(a, t, ap_table_name(&c->cov->aps, q[b]),
                     ((m >> b) & 1) ? node_true(a) : node_false(a));
    acc = acc ? node_or(a, (Node *)acc, (Node *)t) : t;
  }
  return acc ? acc : node_false(a);
}

// Sequential Skolem: fills vals[j] = an inputs-only node for output outs[j],
// such that o_j := vals[j] satisfies B given forall_exists.  outs is sorted.
static void skolem_values(Csnf *c, const Node *B, const uint32_t *outs,
                          uint32_t no, const Node **vals) {
  Arena *a = c->cov->arena;
  for (uint32_t j = 0; j < no; j++) {
    const Node *ej = exists_outputs(c, B, outs + j + 1, no - 1 - j);
    const char *oname = ap_table_name(&c->cov->aps, outs[j]);
    const Node *v =
        node_not(a, (Node *)node_subst(a, ej, oname, node_false(a)));
    for (uint32_t p = 0; p < j; p++) // ground the earlier outputs
      v = node_subst(a, v, ap_table_name(&c->cov->aps, outs[p]), vals[p]);
    vals[j] = apply_rewrites(a, (Node *)v, RW_SIMPLIFY_WEAK);
  }
}

void certify_invariant(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_INVARIANT))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;
  bool moore = semantics_is_moore(cov->spec->info.semantics);
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    if (c->claimed[i] || !has_cand(cc, "safety-invariant"))
      continue;
    const Node *B = constraint_match_formula(cc)->arg; // G(B)
    uint32_t outs[8];
    uint32_t ins[64];
    uint32_t no = 0, ni = 0;
    bool too_many = false;
    for (uint32_t a = 0; a < A; a++) {
      if (apset_test(&cc->outputs, a)) {
        if (no < 8)
          outs[no++] = a;
        else
          too_many = true;
      }
      if (apset_test(&cc->inputs, a)) {
        if (ni < 64)
          ins[ni++] = a;
        else
          too_many = true;
      }
    }
    bool freeo = true;
    for (uint32_t j = 0; j < no && freeo; j++)
      freeo = output_is_free(cov, &i, 1, outs[j]);

    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "safety-invariant";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    bool solved = false;
    if (certify && !moore && freeo && !too_many && no <= 4 && ni + no <= 18) {
      if (no == 0) {
        if (is_taut(cov, B, ins, ni)) {
          blk->status = CSNF_SOLVED;
          blk->cert = "invariant_valid";
          solved = true;
        }
      } else if (forall_exists(cov, B, ins, ni, outs, no)) {
        const Node **vals = malloc(no * sizeof(Node *));
        skolem_values(c, B, outs, no, vals);
        blk->inv_outputs = malloc(no * sizeof(int32_t));
        for (uint32_t j = 0; j < no; j++)
          blk->inv_outputs[j] = (int32_t)outs[j];
        blk->inv_values = vals;
        blk->inv_n = no;
        blk->status = CSNF_SOLVED;
        blk->cert = "safety_invariant";
        solved = true;
      }
    }
    if (solved)
      c->solved[i] = true;
    else
      blk->status = CSNF_CANDIDATE;
    c->claimed[i] = true;
  }
}
