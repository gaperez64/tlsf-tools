// compose_games.c — AbsSynthe-format `Aig` game builders for tlsfcompose.
//
// Compiles a cluster's residual formula into a safety/GR(1) game `Aig` in the
// AbsSynthe AIGER conventions (env-first / Mealy; `controllable_*` inputs;
// `bad` output; latches as state, plus justice[]/fair[] for GR(1)).  Four
// entry points: direct safety, W/R-safety, strict-safety, and unbounded GR(1).
// The AST eligibility gates that decide which builder applies live in
// compose_analysis.c; shared types in compose_internal.h.

#include "tlsf/compose_internal.h"

#include "tlsf/residual.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *controllable_name(const char *name) {
  size_t p = strlen(AIG_CONTROLLABLE_PREFIX), n = strlen(name);
  char *out = malloc(p + n + 1);
  if (!out)
    return nullptr;
  int written = snprintf(out, p + n + 1, "%s%s", AIG_CONTROLLABLE_PREFIX, name);
  if (written < 0 || (size_t)written != p + n) {
    free(out);
    return nullptr;
  }
  return out;
}

typedef struct {
  Aig *g;
  ConstraintCover *cov;
  uint32_t *hist; // (max_lag + 1) x AP table; UINT32_MAX = unavailable
  uint32_t ap_count;
} AigCtx;

static uint32_t hist_lit(const AigCtx *ctx, uint32_t lag, uint32_t ap) {
  return ctx->hist[(lag * ctx->ap_count) + ap];
}

static void hist_set(AigCtx *ctx, uint32_t lag, uint32_t ap, uint32_t lit) {
  ctx->hist[(lag * ctx->ap_count) + ap] = lit;
}

static uint32_t compile_at_lag(AigCtx *ctx, const Node *n, uint32_t lag) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_FALSE:
    return AIG_FALSE;
  case NODE_AP: {
    int32_t idx = ap_table_find(&ctx->cov->aps, n->name);
    if (idx < 0)
      return UINT32_MAX;
    return hist_lit(ctx, lag, (uint32_t)idx);
  }
  case NODE_NOT: {
    uint32_t a = compile_at_lag(ctx, n->arg, lag);
    return a == UINT32_MAX ? a : aig_not(a);
  }
  case NODE_X:
  case NODE_X_STRONG:
    if (lag == 0)
      return UINT32_MAX;
    return compile_at_lag(ctx, n->arg, lag - 1);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    uint32_t a = compile_at_lag(ctx, n->lhs, lag);
    uint32_t b = compile_at_lag(ctx, n->rhs, lag);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    switch (n->kind) {
    case NODE_AND:
      return aig_and(ctx->g, a, b);
    case NODE_OR:
      return aig_or(ctx->g, a, b);
    case NODE_IMPL:
      return aig_or(ctx->g, aig_not(a), b);
    default: { // EQUIV: sequence for determinism across compilers
      uint32_t e0 = aig_or(ctx->g, aig_not(a), b);
      uint32_t e1 = aig_or(ctx->g, a, aig_not(b));
      return aig_and(ctx->g, e0, e1);
    }
    }
  }
  default:
    return UINT32_MAX;
  }
}

static uint32_t compile_global(AigCtx *ctx, const Node *n, uint32_t lag) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_G:
    return compile_at_lag(ctx, n->arg, lag);
  case NODE_AND: {
    uint32_t a = compile_global(ctx, n->lhs, lag);
    uint32_t b = compile_global(ctx, n->rhs, lag);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return aig_and(ctx->g, a, b);
  }
  default:
    return UINT32_MAX;
  }
}

static uint32_t compile_assumption_window(AigCtx *ctx, const Node *assume,
                                          uint32_t depth) {
  uint32_t ok = AIG_TRUE;
  for (uint32_t lag = 0; lag <= depth; lag++) {
    uint32_t at_lag = compile_global(ctx, assume, lag);
    // At an early lag an X-depth assumption reaches before the window start and
    // is not yet evaluable; it is vacuously satisfied there, so skip it.  The
    // caller has already checked the assumption is encodable (finite X-depth).
    if (at_lag == UINT32_MAX)
      continue;
    ok = aig_and(ctx->g, ok, at_lag);
  }
  return ok;
}

static uint32_t compile_safety_initial(AigCtx *ctx, const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_G:
    return AIG_TRUE;
  case NODE_AND: {
    uint32_t a = compile_safety_initial(ctx, n->lhs);
    uint32_t b = compile_safety_initial(ctx, n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return aig_and(ctx->g, a, b);
  }
  default:
    return compile_at_lag(ctx, n, 0);
  }
}

static uint32_t compile_safety_global(AigCtx *ctx, const Node *n,
                                      uint32_t lag) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_G:
    return compile_at_lag(ctx, n->arg, lag);
  case NODE_AND: {
    uint32_t a = compile_safety_global(ctx, n->lhs, lag);
    uint32_t b = compile_safety_global(ctx, n->rhs, lag);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return aig_and(ctx->g, a, b);
  }
  default:
    return AIG_TRUE;
  }
}

static uint32_t guarded_current_ok(Aig *g, uint32_t guard, uint32_t ok) {
  return aig_or(g, aig_not(guard), ok);
}

// Like wr_emit_g_body but with an additional `arm_gate` that limits when new
// obligations can be armed and when invariants are checked.  Once armed, a
// response obligation remains active under `valid` regardless of `arm_gate`
// (the gate only controls arming, not the subsequent tracking/bad signal).
// This implements G(outer_req -> body): distribute outer_req over each conjunct
// so that obligations arm only when outer_req holds, yet once armed they fire
// under the original `valid`.
static bool wr_emit_g_body_gated(AigCtx *ctx, const Node *n, uint32_t depth,
                                 uint32_t valid, uint32_t arm_gate,
                                 uint32_t *bad) {
  Aig *g = ctx->g;
  switch (n->kind) {
  case NODE_G: // G(G(phi)) == G(phi); nested G absorbed by the outer G context
    return wr_emit_g_body_gated(ctx, n->arg, depth, valid, arm_gate, bad);
  case NODE_AND:
    return wr_emit_g_body_gated(ctx, n->lhs, depth, valid, arm_gate, bad) &&
           wr_emit_g_body_gated(ctx, n->rhs, depth, valid, arm_gate, bad);
  case NODE_X:
  case NODE_X_STRONG:
    if (depth == 0)
      return false;
    return wr_emit_g_body_gated(ctx, n->arg, depth - 1, valid, arm_gate, bad);
  case NODE_W: { // G(outer_req -> (a W b)) == G(outer_req -> (a|b))
    uint32_t a = compile_at_lag(ctx, n->lhs, depth);
    uint32_t b = compile_at_lag(ctx, n->rhs, depth);
    if (a != UINT32_MAX && b != UINT32_MAX) {
      *bad = aig_or(
          g, *bad,
          aig_and(g, aig_and(g, valid, arm_gate), aig_not(aig_or(g, a, b))));
      return true;
    }
    // Pattern B: G(outer_req -> ((cond -> [X](ia W/R ib)) W B)).
    // When !cond the implication is trivially true; when cond fires, arm a
    // sub-monitor for the inner W/R.  The outer B release propagates into the
    // sub-monitor so bad is never raised after B fires.
    b = compile_at_lag(ctx, n->rhs, depth); // B must be propositional
    if (b == UINT32_MAX)
      return false;
    const Node *lhs = n->lhs;
    if (lhs->kind != NODE_IMPL)
      return false;
    uint32_t cond = compile_at_lag(ctx, lhs->lhs, depth);
    if (cond == UINT32_MAX)
      return false;
    const Node *xn = lhs->rhs;
    bool xd = (xn->kind == NODE_X || xn->kind == NODE_X_STRONG);
    const Node *inner = xd ? xn->arg : xn;
    if (inner->kind != NODE_W && inner->kind != NODE_R)
      return false;
    uint32_t ia = compile_at_lag(ctx, inner->lhs, depth);
    uint32_t ib = compile_at_lag(ctx, inner->rhs, depth);
    if (ia == UINT32_MAX || ib == UINT32_MAX)
      return false;
    uint32_t sub_arm =
        aig_and(g, aig_and(g, valid, arm_gate),
                aig_and(g, cond, aig_not(b))); // arm when gate & cond & !B
    uint32_t inner_release = inner->kind == NODE_W ? ib : aig_and(g, ia, ib);
    uint32_t inner_fail = inner->kind == NODE_W
                              ? aig_and(g, aig_not(ia), aig_not(ib))
                              : aig_not(ib);
    uint32_t combined_release = aig_or(g, inner_release, b); // inner or outer B
    uint32_t owe = aig_latch(g, AIG_FALSE, AIG_FALSE);
    uint32_t active;
    if (xd) {
      active = owe;
      if (!aig_set_latch_next(
              g, owe,
              aig_or(g, sub_arm, aig_and(g, owe, aig_not(combined_release)))))
        return false;
    } else {
      active = aig_or(g, sub_arm, owe);
      if (!aig_set_latch_next(g, owe,
                              aig_and(g, active, aig_not(combined_release))))
        return false;
    }
    *bad =
        aig_or(g, *bad,
               aig_and(g, valid,
                       aig_and(g, active, aig_and(g, inner_fail, aig_not(b)))));
    return true;
  }
  case NODE_R: // G(outer_req -> (a R b)) == G(outer_req -> b): rhs may have W/R
    return wr_emit_g_body_gated(ctx, n->rhs, depth, valid, arm_gate, bad);
  case NODE_IMPL: {
    const Node *rqn, *inner;
    bool xdelay;
    if (wr_response_parts(n, &rqn, &inner, &xdelay)) {
      // G(outer_req -> req -> [X](a W/R b)): arm when both outer_req and req
      // hold; once armed, track the obligation under `valid` (no outer_req
      // gate).
      uint32_t req = compile_at_lag(ctx, rqn, depth);
      uint32_t a = compile_at_lag(ctx, inner->lhs, depth);
      uint32_t b = compile_at_lag(ctx, inner->rhs, depth);
      if (req == UINT32_MAX || a == UINT32_MAX || b == UINT32_MAX)
        return false;
      uint32_t release = inner->kind == NODE_W ? b : aig_and(g, a, b);
      uint32_t fail = inner->kind == NODE_W ? aig_and(g, aig_not(a), aig_not(b))
                                            : aig_not(b);
      uint32_t owe = aig_latch(g, AIG_FALSE, AIG_FALSE);
      uint32_t arm = aig_and(g, aig_and(g, valid, arm_gate), req);
      uint32_t active;
      if (xdelay) {
        active = owe;
        if (!aig_set_latch_next(
                g, owe, aig_or(g, arm, aig_and(g, owe, aig_not(release)))))
          return false;
      } else {
        active = aig_or(g, arm, owe);
        if (!aig_set_latch_next(g, owe, aig_and(g, active, aig_not(release))))
          return false;
      }
      // Bad under `valid` only: once armed, obligation must be satisfied even
      // when outer_req is not currently asserted.
      *bad = aig_or(g, *bad, aig_and(g, valid, aig_and(g, active, fail)));
      return true;
    }
    // Nested distributable: G(outer_req -> inner_req -> body)
    if (aig_body_ok(n->lhs)) {
      uint32_t inner_gate = compile_at_lag(ctx, n->lhs, depth);
      if (inner_gate == UINT32_MAX)
        return false;
      return wr_emit_g_body_gated(ctx, n->rhs, depth, valid,
                                  aig_and(g, arm_gate, inner_gate), bad);
    }
    [[fallthrough]];
  }
  default: {
    uint32_t ok = compile_at_lag(ctx, n, depth);
    if (ok == UINT32_MAX)
      return false;
    *bad =
        aig_or(g, *bad, aig_and(g, aig_and(g, valid, arm_gate), aig_not(ok)));
    return true;
  }
  }
}

// Accumulate the obligations of a `G(...)` body into *bad.  A Boolean conjunct
// adds `valid & !body`.  `G(a W b) == G(a|b)` and `G(a R b) == G(b)` collapse
// to invariants.  A response `G(req -> X(a W b))` re-arms a weak-until each
// time req fires: an `owe` latch (owe' = (valid & req) | (owe & !b)) tracks an
// outstanding obligation, and the system loses if a and b both fail while owed.
static bool wr_emit_g_body(AigCtx *ctx, const Node *n, uint32_t depth,
                           uint32_t valid, uint32_t *bad) {
  Aig *g = ctx->g;
  switch (n->kind) {
  case NODE_G: // G(G(phi)) == G(phi); nested G absorbed by the outer G context
    return wr_emit_g_body(ctx, n->arg, depth, valid, bad);
  case NODE_AND:
    return wr_emit_g_body(ctx, n->lhs, depth, valid, bad) &&
           wr_emit_g_body(ctx, n->rhs, depth, valid, bad);
  case NODE_W: { // G(a W b) == G(a | b)
    uint32_t a = compile_at_lag(ctx, n->lhs, depth);
    uint32_t b = compile_at_lag(ctx, n->rhs, depth);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_not(aig_or(g, a, b))));
    return true;
  }
  case NODE_R: // G(a R b) == G(b): rhs may itself contain W/R
    return wr_emit_g_body(ctx, n->rhs, depth, valid, bad);
  case NODE_IMPL: {
    const Node *rqn, *inner;
    bool xdelay;
    if (wr_response_parts(n, &rqn, &inner, &xdelay)) {
      // G(req -> [X](a W/R b)): a re-armed response monitor.  An `owe` latch
      // tracks an outstanding obligation; `a W b` releases on b (fails on
      // !a&!b), `a R b` releases on a&b (fails on !b).  Without X the
      // obligation is active the same step req fires; with X it is delayed one
      // step.
      uint32_t req = compile_at_lag(ctx, rqn, depth);
      uint32_t a = compile_at_lag(ctx, inner->lhs, depth);
      uint32_t b = compile_at_lag(ctx, inner->rhs, depth);
      if (req == UINT32_MAX || a == UINT32_MAX || b == UINT32_MAX)
        return false;
      uint32_t release =
          inner->kind == NODE_W ? b : aig_and(g, a, b); // W: b; R: a&b
      uint32_t fail = inner->kind == NODE_W ? aig_and(g, aig_not(a), aig_not(b))
                                            : aig_not(b); // W: !a&!b; R: !b
      uint32_t owe = aig_latch(g, AIG_FALSE, AIG_FALSE);
      uint32_t active; // obligation active this step
      if (xdelay) {
        active = owe;
        uint32_t owe_next = aig_or(g, aig_and(g, valid, req),
                                   aig_and(g, owe, aig_not(release)));
        if (!aig_set_latch_next(g, owe, owe_next))
          return false;
      } else {
        active = aig_or(g, aig_and(g, valid, req), owe);
        if (!aig_set_latch_next(g, owe, aig_and(g, active, aig_not(release))))
          return false;
      }
      *bad = aig_or(g, *bad, aig_and(g, valid, aig_and(g, active, fail)));
      return true;
    }
    // Distributable: G(outer_req -> body) — delegate to the gated emitter which
    // arms obligations under outer_req but tracks them under the original
    // valid.
    if (aig_body_ok(n->lhs)) {
      uint32_t outer = compile_at_lag(ctx, n->lhs, depth);
      if (outer == UINT32_MAX)
        return false;
      return wr_emit_g_body_gated(ctx, n->rhs, depth, valid, outer, bad);
    }
    [[fallthrough]];
  }
  default: {
    uint32_t ok = compile_at_lag(ctx, n, depth);
    if (ok == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_not(ok)));
    return true;
  }
  }
}

// Accumulate a safety guarantee's obligations into *bad.  `G(body)` adds the
// combinational `valid & !body@depth` (W/R inside the body collapse to
// invariants).  A top-level weak-until `a W b` (a holds until b, or forever)
// and release `a R b` (b holds until a&b, or forever) are genuine safety
// properties: each gets a "released" monitor latch and the system loses only if
// the obligation fails before the release.  A bare Boolean conjunct is an
// initial-state constraint, charged only on the first valid step (`first`).
// Returns false on an unsupported conjunct.
// step_one: AIG literal that is 1 only at the logical step immediately after
// `first` (i.e., when X-delayed initial constraints should be checked).
// AIG_FALSE means no X-initial constraints exist.
static bool wr_emit_guarantee(AigCtx *ctx, const Node *n, uint32_t depth,
                              uint32_t valid, uint32_t first, uint32_t step_one,
                              uint32_t *bad) {
  Aig *g = ctx->g;
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_AND:
    return wr_emit_guarantee(ctx, n->lhs, depth, valid, first, step_one, bad) &&
           wr_emit_guarantee(ctx, n->rhs, depth, valid, first, step_one, bad);
  case NODE_G:
    return wr_emit_g_body(ctx, n->arg, depth, valid, bad);
  case NODE_W:
  case NODE_R: {
    uint32_t av = compile_at_lag(ctx, n->lhs, depth);
    uint32_t bv = compile_at_lag(ctx, n->rhs, depth);
    if (av == UINT32_MAX || bv == UINT32_MAX)
      return false;
    uint32_t rel = aig_latch(g, AIG_FALSE, AIG_FALSE);
    // a W b releases on b; a R b releases on (a & b).
    uint32_t release = n->kind == NODE_W ? bv : aig_and(g, av, bv);
    if (!aig_set_latch_next(g, rel, aig_or(g, rel, aig_and(g, valid, release))))
      return false;
    // a W b fails when a and b both fail before release; a R b when b fails.
    uint32_t fail =
        n->kind == NODE_W ? aig_and(g, aig_not(av), aig_not(bv)) : aig_not(bv);
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_and(g, aig_not(rel), fail)));
    return true;
  }
  default: {
    if (aig_initial_ok(n)) {
      // Bare Boolean: initial-state constraint at the first logical step.
      uint32_t ok = compile_at_lag(ctx, n, depth);
      if (ok == UINT32_MAX)
        return false;
      *bad = aig_or(g, *bad, aig_and(g, first, aig_not(ok)));
      return true;
    }
    // X-delayed initial constraint: enforced at step_one (the step after
    // first). Compile at the formula's own X-depth so X operators peel to lag=0
    // at the physical step when step_one fires (physical t=depth + x_depth).
    if (aig_initial_x_ok(n) && step_one != AIG_FALSE) {
      uint32_t ok = compile_at_lag(ctx, n, aig_x_depth(n));
      if (ok == UINT32_MAX)
        return false;
      *bad = aig_or(g, *bad, aig_and(g, step_one, aig_not(ok)));
      return true;
    }
    return false;
  }
  }
}

Aig *build_aig_game(ConstraintCover *cov, const bool *seen, const Node *root) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;
  const Node *assume = nullptr, *guarantee = root;
  if (root->kind == NODE_IMPL) {
    assume = root->lhs;
    guarantee = root->rhs;
  }
  uint32_t ass_depth = assume ? aig_global_x_depth(assume) : 0;
  uint32_t gua_depth = aig_safety_wr_x_depth(guarantee);
  if (ass_depth == UINT32_MAX || gua_depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t depth = ass_depth > gua_depth ? ass_depth : gua_depth;
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AigCtx ctx = {g, cov, hist, A ? A : 1};

  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !residual_signal_matches(cov, a, AP_FLAG_INPUT))
      continue;
    hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
  }
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    char *cname = controllable_name(ap_table_name(&cov->aps, a));
    if (!cname) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    hist_set(&ctx, 0, a, aig_input(g, cname));
    free(cname);
  }
  for (uint32_t d = 1; d <= depth; d++) {
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  }
  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);

  // The rising edge of valid (first logical step) charges initial constraints;
  // build the marker latch only when the guarantee actually has an initial.
  uint32_t first = AIG_FALSE;
  if (wr_has_initial(guarantee)) {
    uint32_t seen_valid = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, seen_valid, aig_or(g, seen_valid, valid))) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    first = aig_and(g, valid, aig_not(seen_valid));
  }

  uint32_t bad = AIG_FALSE;
  // build_aig_game uses safety_direct_ok, which
  // requires aig_initial_ok (no X) so step_one is never needed.
  if (!wr_emit_guarantee(&ctx, guarantee, depth, valid, first, AIG_FALSE,
                         &bad)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  if (assume) {
    uint32_t ass_ok = compile_global(&ctx, assume, depth);
    if (ass_ok == UINT32_MAX) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    uint32_t ass_window_ok = compile_assumption_window(&ctx, assume, depth);
    if (ass_window_ok == UINT32_MAX) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    uint32_t violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
    uint32_t violated_next =
        aig_or(g, violated, aig_and(g, valid, aig_not(ass_ok)));
    if (!aig_set_latch_next(g, violated, violated_next)) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    bad = aig_and(g, bad, aig_and(g, aig_not(violated), ass_window_ok));
  }
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}

// Antecedent of a structural IMPL: same as aig_safety_wr_ok but
// without bare NODE_W / NODE_R.  A bare `a W b` in the antecedent is only
// exact when `b` is purely env-controlled; when `b` is a system output the W
// creates a cycling liveness obligation (e.g. G(on→X(act W off)), G(off→X(!act
// W on))) that the safety game cannot model exactly, producing false UNREALs.
// Rejecting bare W/R in the antecedent causes these clusters to fall through to
// ltlsynt.  G-wrapped W/R in the antecedent (G(req→X(a W b))) is still exact.
static bool wr_antecedent_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return g_body_wr_supported(n->arg);
  case NODE_AND:
    return wr_antecedent_supported(n->lhs) && wr_antecedent_supported(n->rhs);
  default:
    return aig_initial_ok(n);
  }
}

// A safety cluster `AND(U..., IMPL(A, G))`: unconditional safety U plus one
// assume->guarantee, where U/A/G are W/R-safety (`g_body`/top-level monitors).
bool wr_structural_supported(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return wr_structural_supported(n->lhs) && wr_structural_supported(n->rhs);
  case NODE_IMPL:
    // A top-level IMPL where BOTH sides are purely Boolean+X (no G/W/R) is an
    // initial-state conditional constraint (`X(phi) -> psi`), not a structural
    // assume->guarantee.  Route it through aig_safety_wr_ok which
    // handles it via the initial-x default case.  A structural
    // assume->guarantee has at least one G-wrapped antecedent conjunct, so its
    // lhs is not fully initial_x_supported.
    if (aig_initial_x_ok(n->lhs) && aig_initial_x_ok(n->rhs))
      return aig_safety_wr_ok(n);
    return wr_antecedent_supported(n->lhs) && aig_safety_wr_ok(n->rhs);
  default:
    return aig_safety_wr_ok(n);
  }
}

static bool wr_structural_has_initial(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return wr_structural_has_initial(n->lhs) ||
           wr_structural_has_initial(n->rhs);
  case NODE_IMPL:
    return wr_has_initial(n->lhs) || wr_has_initial(n->rhs);
  default:
    return wr_has_initial(n);
  }
}

static bool wr_structural_has_x_initial(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return wr_structural_has_x_initial(n->lhs) ||
           wr_structural_has_x_initial(n->rhs);
  case NODE_IMPL:
    return wr_has_x_initial(n->lhs) || wr_has_x_initial(n->rhs);
  default:
    return wr_has_x_initial(n);
  }
}

static uint32_t wr_structural_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_AND: {
    uint32_t a = wr_structural_x_depth(n->lhs);
    uint32_t b = wr_structural_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_IMPL: {
    uint32_t a = aig_safety_wr_x_depth(n->lhs);
    uint32_t b = aig_safety_wr_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  default:
    return aig_safety_wr_x_depth(n);
  }
}

// Emit the obligations of `AND(U..., IMPL(A, G))`: unconditional U conjuncts
// into *bad, the assume A's violations into *viol_a (drive `violated`), the
// guarantee G's into *bad_cond (gated by !released).  At most one implication.
static bool wr_emit_structural(AigCtx *ctx, const Node *n, uint32_t depth,
                               uint32_t valid, uint32_t first,
                               uint32_t step_one, uint32_t *bad,
                               uint32_t *viol_a, uint32_t *bad_cond,
                               int *nimpl) {
  if (n->kind == NODE_AND)
    return wr_emit_structural(ctx, n->lhs, depth, valid, first, step_one, bad,
                              viol_a, bad_cond, nimpl) &&
           wr_emit_structural(ctx, n->rhs, depth, valid, first, step_one, bad,
                              viol_a, bad_cond, nimpl);
  if (n->kind == NODE_IMPL) {
    // Initial-state conditional: treat as a plain initial constraint charged
    // into the unconditional bad, not as a structural assume->guarantee split.
    if (aig_initial_x_ok(n->lhs) && aig_initial_x_ok(n->rhs))
      return wr_emit_guarantee(ctx, n, depth, valid, first, step_one, bad);
    if (++(*nimpl) > 1)
      return false;
    return wr_emit_guarantee(ctx, n->lhs, depth, valid, first, step_one,
                             viol_a) &&
           wr_emit_guarantee(ctx, n->rhs, depth, valid, first, step_one,
                             bad_cond);
  }
  return wr_emit_guarantee(ctx, n, depth, valid, first, step_one, bad);
}

// Safety game for `AND(U..., IMPL(A, G))` with W/R on any side.  Reuses the
// verified wr_emit_guarantee walk; the assume's violations latch `violated`
// (the system is released once the env breaks an assumption), so the guarantee
// bad is gated by `!released` while the unconditional U bad is not.
Aig *build_aig_wr_game(ConstraintCover *cov, const bool *seen,
                       const Node *root) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;
  uint32_t depth = wr_structural_x_depth(root);
  if (depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AigCtx ctx = {g, cov, hist, A ? A : 1};
  for (uint32_t a = 0; a < cov->aps.count; a++)
    if (seen[a] && residual_signal_matches(cov, a, AP_FLAG_INPUT))
      hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    char *cname = controllable_name(ap_table_name(&cov->aps, a));
    if (!cname) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    hist_set(&ctx, 0, a, aig_input(g, cname));
    free(cname);
  }
  for (uint32_t d = 1; d <= depth; d++)
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);
  // The rising edge of valid (first logical step) charges initial constraints;
  // build the marker latch only when some conjunct actually has an initial.
  uint32_t first = AIG_FALSE;
  if (wr_structural_has_initial(root) || wr_structural_has_x_initial(root)) {
    uint32_t seen_valid = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, seen_valid, aig_or(g, seen_valid, valid))) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    first = aig_and(g, valid, aig_not(seen_valid));
  }
  // step_one fires one logical step after first, gating X-delayed initial
  // constraints (depth-1 X initial).  It is a latch whose next is `first`.
  uint32_t step_one = AIG_FALSE;
  if (first != AIG_FALSE && wr_structural_has_x_initial(root)) {
    step_one = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, step_one, first)) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
  }

  uint32_t bad = AIG_FALSE, viol_a = AIG_FALSE, bad_cond = AIG_FALSE;
  int nimpl = 0;
  if (!wr_emit_structural(&ctx, root, depth, valid, first, step_one, &bad,
                          &viol_a, &bad_cond, &nimpl)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  // released = env has broken an assumption now or in the past.
  uint32_t violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
  uint32_t released = aig_or(g, violated, viol_a);
  if (!aig_set_latch_next(g, violated, released)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  bad = aig_or(g, bad, aig_and(g, aig_not(released), bad_cond));
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}

Aig *build_aig_strict_safety_game(ConstraintCover *cov, const bool *seen,
                                  const Node *sys, const Node *env) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;

  uint32_t env_depth = aig_safety_cond_x_depth(env);
  uint32_t sys_depth = aig_safety_cond_x_depth(sys);
  if (env_depth == UINT32_MAX || sys_depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t depth = env_depth > sys_depth ? env_depth : sys_depth;
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AigCtx ctx = {g, cov, hist, A ? A : 1};

  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !residual_signal_matches(cov, a, AP_FLAG_INPUT))
      continue;
    hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
  }
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    char *cname = controllable_name(ap_table_name(&cov->aps, a));
    if (!cname) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    hist_set(&ctx, 0, a, aig_input(g, cname));
    free(cname);
  }
  for (uint32_t d = 1; d <= depth; d++) {
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  }

  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);
  uint32_t past_first = aig_latch(g, AIG_TRUE, AIG_FALSE);
  uint32_t first = aig_not(past_first);

  uint32_t env_init_ok = compile_safety_initial(&ctx, env);
  uint32_t sys_init_ok = compile_safety_initial(&ctx, sys);
  uint32_t env_global_ok = compile_safety_global(&ctx, env, depth);
  uint32_t sys_global_ok = compile_safety_global(&ctx, sys, depth);
  if (env_init_ok == UINT32_MAX || sys_init_ok == UINT32_MAX ||
      env_global_ok == UINT32_MAX || sys_global_ok == UINT32_MAX) {
    free(hist);
    aig_free(g);
    return nullptr;
  }

  uint32_t env_ok = aig_and(g, guarded_current_ok(g, first, env_init_ok),
                            guarded_current_ok(g, valid, env_global_ok));
  uint32_t sys_ok = aig_and(g, guarded_current_ok(g, first, sys_init_ok),
                            guarded_current_ok(g, valid, sys_global_ok));
  uint32_t violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
  uint32_t violated_next = aig_or(g, violated, aig_not(env_ok));
  if (!aig_set_latch_next(g, violated, violated_next)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  uint32_t bad =
      aig_and(g, aig_not(violated), aig_and(g, env_ok, aig_not(sys_ok)));
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}

// Complete (unbounded) GR(1): the safety part (history latches, the valid
// window, the guarantee/assumption masking) is encoded exactly like
// build_aig_game, but liveness is emitted as real AIGER justice /
// fairness records for AbsSynthe's GR(1) solver rather than bounded counters.
// Each justice goal `J` becomes a deterministic pending monitor
// (`pending' = !violated & !grant & (pending | req)`, with `req = true` for a
// recurrence `G F J`) so its justice literal `!pending` is a STATE predicate
// and G F !pending <=> the goal is met infinitely often.  The fairness
// assumption `a` is sampled into a latch (`fa' = a`) so its fairness literal is
// a state predicate too.  State predicates are required: AbsSynthe's
// controllable predecessor (and its multi-goal justice-counter
// degeneralization) mishandle goals/assumptions that mention inputs directly.
// When the environment breaks the SAFETY assumption (`violated` latches), the
// monitors are forced to clear, lifting the liveness obligation just as the
// safety `bad` masking lifts the safety obligation -- the GR(1) implication is
// then vacuously won.
Aig *build_aig_gr1_game(ConstraintCover *cov, const bool *seen,
                        const Gr1Parts *parts) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;
  const Node *assume = parts->safety_assume, *guarantee = parts->safety_gua;
  uint32_t ass_depth = aig_global_x_depth(assume);
  uint32_t gua_depth = aig_global_x_depth(guarantee);
  if (ass_depth == UINT32_MAX || gua_depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t depth = ass_depth > gua_depth ? ass_depth : gua_depth;
  // Weak-until operands may carry their own X-depth; widen the history window.
  for (uint32_t w = 0; w < parts->nweak; w++) {
    uint32_t da = aig_x_depth(parts->weak[w].a);
    uint32_t db = aig_x_depth(parts->weak[w].b);
    if (da > depth)
      depth = da;
    if (db > depth)
      depth = db;
  }
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AigCtx ctx = {g, cov, hist, A ? A : 1};
  for (uint32_t a = 0; a < cov->aps.count; a++)
    if (seen[a] && residual_signal_matches(cov, a, AP_FLAG_INPUT))
      hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    char *cname = controllable_name(ap_table_name(&cov->aps, a));
    if (!cname) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    hist_set(&ctx, 0, a, aig_input(g, cname));
    free(cname);
  }
  for (uint32_t d = 1; d <= depth; d++)
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);
  // `first` marks t=0 (latch is 0 at t=0, 1 ever after), gating initial
  // conditions, exactly as the strict-safety encoder does.
  uint32_t past_first = aig_latch(g, AIG_TRUE, AIG_FALSE);
  uint32_t first = aig_not(past_first);

#define UGR1_FAIL()                                                            \
  do {                                                                         \
    free(hist);                                                                \
    aig_free(g);                                                               \
    return nullptr;                                                            \
  } while (0)

  uint32_t gua_ok = compile_global(&ctx, guarantee, depth);
  if (gua_ok == UINT32_MAX)
    UGR1_FAIL();
  uint32_t bad = aig_and(g, valid, aig_not(gua_ok));

  // Compile the initial conditions (Boolean, evaluated at t=0 / lag 0).
  uint32_t env_init_ok = compile_at_lag(&ctx, parts->env_init, 0);
  uint32_t sys_init_ok = compile_at_lag(&ctx, parts->sys_init, 0);
  if (env_init_ok == UINT32_MAX || sys_init_ok == UINT32_MAX)
    UGR1_FAIL();
  bool has_env_init = parts->env_init->kind != NODE_TRUE;
  bool has_sys_init = parts->sys_init->kind != NODE_TRUE;

  // Safety assumption and env-init first, so `violated` can lift the liveness
  // obligation too (a broken env assumption wins the GR(1) implication
  // vacuously).
  uint32_t violated = AIG_FALSE;
  uint32_t ass_window_ok = AIG_TRUE;
  if (assume->kind != NODE_TRUE || has_env_init) {
    uint32_t vnext;
    violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
    vnext = violated;
    if (assume->kind != NODE_TRUE) {
      uint32_t ass_ok = compile_global(&ctx, assume, depth);
      ass_window_ok = compile_assumption_window(&ctx, assume, depth);
      if (ass_ok == UINT32_MAX || ass_window_ok == UINT32_MAX)
        UGR1_FAIL();
      vnext = aig_or(g, vnext, aig_and(g, valid, aig_not(ass_ok)));
    }
    if (has_env_init)
      vnext = aig_or(g, vnext, aig_and(g, first, aig_not(env_init_ok)));
    if (!aig_set_latch_next(g, violated, vnext))
      UGR1_FAIL();
  }

  // System justice goals: each is G F !pending via a pending monitor latch.
  for (uint32_t j = 0; j < parts->njustice; j++) {
    uint32_t tgt = compile_at_lag(&ctx, parts->justice[j].target, depth);
    if (tgt == UINT32_MAX)
      UGR1_FAIL();
    uint32_t req = AIG_TRUE; // recurrence G F J == response with req = true
    if (parts->justice[j].req) {
      req = compile_at_lag(&ctx, parts->justice[j].req, depth);
      if (req == UINT32_MAX)
        UGR1_FAIL();
    }
    uint32_t p = aig_latch(g, AIG_FALSE, AIG_FALSE);
    uint32_t next = aig_and(g, aig_not(violated),
                            aig_and(g, aig_not(tgt), aig_or(g, p, req)));
    if (!aig_set_latch_next(g, p, next))
      UGR1_FAIL();
    uint32_t jlit = aig_not(p);
    aig_add_justice(g, &jlit, 1, "gr1_justice");
  }

  // Environment fairness assumptions G F a, each sampled into a latch so its
  // fairness literal is a state predicate.
  for (uint32_t i = 0; i < parts->nfairness; i++) {
    uint32_t fair = compile_at_lag(&ctx, parts->fairness[i], depth);
    if (fair == UINT32_MAX)
      UGR1_FAIL();
    uint32_t fa = aig_latch(g, fair, AIG_FALSE);
    aig_add_fairness(g, fa, "gr1_fairness");
  }

  // Weak-until guarantees `a W b`: a pure-safety obligation that a holds until
  // b (or forever).  A `released` latch records that b has held; the system
  // loses if a fails before b is ever seen.
  for (uint32_t w = 0; w < parts->nweak; w++) {
    uint32_t a_ok = compile_at_lag(&ctx, parts->weak[w].a, depth);
    uint32_t b_ok = compile_at_lag(&ctx, parts->weak[w].b, depth);
    if (a_ok == UINT32_MAX || b_ok == UINT32_MAX)
      UGR1_FAIL();
    uint32_t released = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, released,
                            aig_or(g, released, aig_and(g, valid, b_ok))))
      UGR1_FAIL();
    uint32_t weak_bad =
        aig_and(g, valid,
                aig_and(g, aig_not(released),
                        aig_and(g, aig_not(a_ok), aig_not(b_ok))));
    bad = aig_or(g, bad, weak_bad);
  }

  // The system must also satisfy its initial condition at t=0.
  if (has_sys_init)
    bad = aig_or(g, bad, aig_and(g, first, aig_not(sys_init_ok)));
  bad = aig_and(g, bad, aig_and(g, aig_not(violated), ass_window_ok));
#undef UGR1_FAIL
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}
