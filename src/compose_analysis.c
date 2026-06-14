// compose_analysis.c — pure AST/arena cluster analysis for tlsfcompose.
//
// Eligibility gates and X-depth accounting for the direct / W/R / strict-safety
// safety paths, the GR(1) decomposition (`abssynthe_gr1_parts`), liveness
// bounding (`bound_liveness`), and cluster-shape classification used to pick a
// backend / explain an ltlsynt fallback.  No `Aig` construction here — see
// compose_games.c.  Shared types live in compose_internal.h.

#include "tlsf/compose_internal.h"

#include "tlsf/gr.h"

#include <stdio.h>
#include <string.h>

bool abssynthe_body_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
    return abssynthe_body_supported(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  default:
    return false;
  }
}

bool abssynthe_initial_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return abssynthe_initial_supported(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return abssynthe_initial_supported(n->lhs) &&
           abssynthe_initial_supported(n->rhs);
  default:
    return false;
  }
}

static bool abssynthe_global_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return abssynthe_body_supported(n->arg);
  case NODE_AND:
    return abssynthe_global_supported(n->lhs) &&
           abssynthe_global_supported(n->rhs);
  default:
    return false;
  }
}

static bool abssynthe_safety_condition_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_AND:
    return abssynthe_safety_condition_supported(n->lhs) &&
           abssynthe_safety_condition_supported(n->rhs);
  case NODE_G:
    return abssynthe_body_supported(n->arg);
  default:
    return abssynthe_initial_supported(n);
  }
}

uint32_t abssynthe_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
    return 1 + abssynthe_x_depth(n->arg);
  case NODE_NOT:
    return abssynthe_x_depth(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    uint32_t a = abssynthe_x_depth(n->lhs), b = abssynthe_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return 0;
  }
}

// Like abssynthe_x_depth but also recurses into W/R operands.  Required for
// W/R-extended G bodies where X operators can appear inside W/R sub-expressions
// (e.g. G(req -> X(a R (b -> X c))): the nested X inside the R rhs contributes
// to the history-latch depth needed by abssynthe_compile_at_lag).
static uint32_t wr_body_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
    return 1 + wr_body_x_depth(n->arg);
  case NODE_NOT:
    return wr_body_x_depth(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_W:
  case NODE_R: {
    uint32_t a = wr_body_x_depth(n->lhs), b = wr_body_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return 0;
  }
}

uint32_t abssynthe_safety_condition_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_AND: {
    uint32_t a = abssynthe_safety_condition_x_depth(n->lhs);
    uint32_t b = abssynthe_safety_condition_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_G:
    return abssynthe_x_depth(n->arg);
  default:
    return abssynthe_initial_supported(n) ? 0 : UINT32_MAX;
  }
}

uint32_t abssynthe_global_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_G:
    return abssynthe_x_depth(n->arg);
  case NODE_AND: {
    uint32_t a = abssynthe_global_x_depth(n->lhs);
    uint32_t b = abssynthe_global_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return UINT32_MAX;
  }
}

// Recognize a re-armed safety response `G(req -> [X](a W b))` or
// `G(req -> [X](a R b))` with Boolean operands.  On success sets *req to the
// antecedent, *inner to the weak-until/release node, and *xdelay to whether the
// consequent is X-delayed.  These are genuine safety obligations that a monitor
// latch tracks (re-armed each time req fires).
bool wr_response_parts(const Node *impl, const Node **req, const Node **inner,
                       bool *xdelay) {
  if (impl->kind != NODE_IMPL)
    return false;
  const Node *rhs = impl->rhs;
  bool x = false;
  if (rhs->kind == NODE_X || rhs->kind == NODE_X_STRONG) {
    x = true;
    rhs = rhs->arg;
  }
  if (rhs->kind != NODE_W && rhs->kind != NODE_R)
    return false;
  if (!abssynthe_body_supported(impl->lhs) ||
      !abssynthe_body_supported(rhs->lhs) ||
      !abssynthe_body_supported(rhs->rhs))
    return false;
  *req = impl->lhs;
  *inner = rhs;
  *xdelay = x;
  return true;
}

// Strict version: W/R inside G body require both operands to be pure Boolean.
// Used by abssynthe_eligible (direct path) to avoid routing extended W/R
// patterns to build_abssynthe_game, which cannot handle them.
static bool g_body_direct_supported(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return g_body_direct_supported(n->lhs) && g_body_direct_supported(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    return g_body_direct_supported(n->arg);
  case NODE_W:
  case NODE_R:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  case NODE_IMPL: {
    const Node *req, *inner;
    bool xdelay;
    if (wr_response_parts(n, &req, &inner, &xdelay))
      return true;
    if (abssynthe_body_supported(n->lhs))
      return g_body_direct_supported(n->rhs);
    return false;
  }
  default:
    return abssynthe_body_supported(n);
  }
}

static bool abssynthe_safety_direct_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return g_body_direct_supported(n->arg);
  case NODE_AND:
    return abssynthe_safety_direct_supported(n->lhs) &&
           abssynthe_safety_direct_supported(n->rhs);
  case NODE_W:
  case NODE_R:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  default:
    return abssynthe_initial_supported(n);
  }
}

// A conjunct of a `G(...)` body: Boolean, a bare weak-until / release, or a
// re-armed response.  Under the outer G a bare W/R collapses to an invariant --
// `G(a W b) == G(a|b)`, `G(a R b) == G(b)` -- so no monitor is needed; a
// response `G(req -> [X](a W/R b))` re-arms a monitor each time req fires.
bool g_body_wr_supported(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return g_body_wr_supported(n->lhs) && g_body_wr_supported(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    return g_body_wr_supported(n->arg);
  case NODE_W: {
    // G(a W b) == G(a|b): both operands must be propositional.
    if (abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs))
      return true;
    // Pattern B: (cond -> X(a W/R b)) W B — cond, a, b, B propositional.
    // The outer W collapses because cond->X(inner) is trivially true when
    // !cond; when cond fires, arm a sub-monitor for inner W/R.
    if (!abssynthe_body_supported(n->rhs))
      return false; // B must be propositional
    const Node *lhs = n->lhs;
    if (lhs->kind != NODE_IMPL || !abssynthe_body_supported(lhs->lhs))
      return false;
    const Node *xn = lhs->rhs;
    if (xn->kind == NODE_X || xn->kind == NODE_X_STRONG)
      xn = xn->arg;
    return (xn->kind == NODE_W || xn->kind == NODE_R) &&
           abssynthe_body_supported(xn->lhs) &&
           abssynthe_body_supported(xn->rhs);
  }
  case NODE_R:
    // G(a R b) == G(b): lhs is irrelevant; rhs may itself contain W/R.
    return g_body_wr_supported(n->rhs);
  case NODE_IMPL: {
    const Node *req, *inner;
    bool xdelay;
    if (wr_response_parts(n, &req, &inner, &xdelay))
      return true;
    // Distributable: G(outer_req -> body) === AND over G(outer_req ->
    // conjunct). Supported when outer_req is propositional; each conjunct in
    // body is then checked by recursing (and resolving to bool, W/R-collapse,
    // or response).
    if (abssynthe_body_supported(n->lhs))
      return g_body_wr_supported(n->rhs);
    return false;
  }
  default:
    return abssynthe_body_supported(n);
  }
}

// Pure-safety guarantee that may also carry weak-until `a W b` or release
// `a R b` (Boolean operands): genuine safety properties.  A top-level `a W b`
// gets a "released" monitor latch; a `W`/`R` *inside* a `G` body collapses to a
// plain invariant.  Both are exactly encodable alongside `G(...)` invariants.
bool abssynthe_safety_wr_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return g_body_wr_supported(n->arg);
  case NODE_AND:
    return abssynthe_safety_wr_supported(n->lhs) &&
           abssynthe_safety_wr_supported(n->rhs);
  case NODE_W:
  case NODE_R:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  default:
    // A bare Boolean conjunct is an initial-state constraint (step 0 only).
    return abssynthe_initial_supported(n);
  }
}

uint32_t abssynthe_safety_wr_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_G:
    return wr_body_x_depth(n->arg); // must recurse into W/R for nested X
  case NODE_AND: {
    uint32_t a = abssynthe_safety_wr_x_depth(n->lhs);
    uint32_t b = abssynthe_safety_wr_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_W:
  case NODE_R: {
    uint32_t a = abssynthe_x_depth(n->lhs), b = abssynthe_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return abssynthe_initial_supported(n) ? 0 : UINT32_MAX;
  }
}

// Does this safety condition carry a bare-Boolean (initial-state) conjunct?
// Mirrors wr_emit_guarantee's structure: only the default (bare-Boolean) leaf
// is an initial constraint, so a game needs the `first` marker only when this
// holds.
bool wr_has_initial(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_G:
  case NODE_W:
  case NODE_R:
    return false;
  case NODE_AND:
    return wr_has_initial(n->lhs) || wr_has_initial(n->rhs);
  default:
    return true;
  }
}

bool abssynthe_eligible(const Node *root, bool finite) {
  if (finite)
    return false;
  if (root->kind == NODE_IMPL)
    return abssynthe_global_supported(root->lhs) &&
           abssynthe_global_x_depth(root->lhs) == 0 &&
           abssynthe_safety_direct_supported(root->rhs);
  return abssynthe_safety_direct_supported(root);
}

bool abssynthe_strict_safety_parts(const Node *root, const Node **sys,
                                   const Node **env) {
  if (root->kind != NODE_W || root->rhs->kind != NODE_NOT)
    return false;
  if (!abssynthe_safety_condition_supported(root->lhs) ||
      !abssynthe_safety_condition_supported(root->rhs->arg))
    return false;
  *sys = root->lhs;
  *env = root->rhs->arg;
  return true;
}

// ---- GR(1): `G F a` fairness assumptions + recurrence/response justice ----

// ---- GR(1): G F a fairness + recurrence/response justice decomposition ----

// `G F x` with `x` AbsSynthe-Boolean -> x, else nullptr.
static const Node *match_gf(const Node *n) {
  if (n->kind == NODE_G && n->arg->kind == NODE_F &&
      abssynthe_body_supported(n->arg->arg))
    return n->arg->arg;
  return nullptr;
}

// `G(req -> F grant)` with req, grant AbsSynthe-Boolean.
static bool match_response(const Node *n, const Node **req,
                           const Node **grant) {
  if (n->kind != NODE_G || n->arg->kind != NODE_IMPL)
    return false;
  const Node *body = n->arg;
  if (body->rhs->kind != NODE_F || !abssynthe_body_supported(body->lhs) ||
      !abssynthe_body_supported(body->rhs->arg))
    return false;
  *req = body->lhs;
  *grant = body->rhs->arg;
  return true;
}

// Classify each top-level conjunct of an assume/guarantee side into the
// fairness / justice / safety buckets of `p`.  Returns false on any conjunct
// that is neither a recognized liveness goal nor an encodable safety formula.
static bool gr1_collect(Arena *a, const Node *n, bool assume, Gr1Parts *p) {
  if (n->kind == NODE_AND)
    return gr1_collect(a, n->lhs, assume, p) &&
           gr1_collect(a, n->rhs, assume, p);
  // An initial Boolean conjunct (env-init on the assume side, sys-init on the
  // guarantee side): part of the GR(1) implication's antecedent/consequent.
  if (abssynthe_initial_supported(n)) {
    const Node **init = assume ? &p->env_init : &p->sys_init;
    *init =
        (*init)->kind == NODE_TRUE ? n : node_and(a, (Node *)*init, (Node *)n);
    return true;
  }
  const Node *gf = match_gf(n);
  if (assume) {
    if (gf) {
      if (p->nfairness >= GR1_MAX_FAIRNESS)
        return false;
      p->fairness[p->nfairness++] = gf;
      return true;
    }
  } else if (gf) {
    if (p->njustice >= GR1_MAX_JUSTICE)
      return false;
    p->justice[p->njustice++] = (Gr1Justice){nullptr, gf};
    return true;
  } else {
    const Node *req = nullptr, *grant = nullptr;
    if (match_response(n, &req, &grant)) {
      if (p->njustice >= GR1_MAX_JUSTICE)
        return false;
      p->justice[p->njustice++] = (Gr1Justice){req, grant};
      return true;
    }
    // A weak-until `a W b` (Boolean a, b) is a pure-safety guarantee: a holds
    // until b, or forever.  Encoded with a "released" monitor in the emitter.
    if (n->kind == NODE_W && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs)) {
      if (p->nweak >= GR1_MAX_WEAK)
        return false;
      p->weak[p->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
      return true;
    }
  }
  if (!abssynthe_global_supported(n))
    return false; // otherwise must be an encodable `G(safety)` conjunct
  const Node **safety = assume ? &p->safety_assume : &p->safety_gua;
  *safety = (*safety)->kind == NODE_TRUE
                ? n
                : node_and(a, (Node *)*safety, (Node *)n);
  return true;
}

// Bucket the system-safety side `S_safety` of a strict `S_safety W ¬A_safety`
// conjunct (a conjunction of `G(...)` invariants and initial Booleans) into the
// guarantee-safety / sys-init buckets.  The strict conditioning itself is
// realized by the `violated` latch (driven by the env safety A_safety, which
// reappears in the liveness antecedent E), so the `¬A_safety` release is
// redundant here and ignored.
static bool gr1_collect_strict_safety(Arena *a, const Node *n, Gr1Parts *p) {
  if (n->kind == NODE_AND)
    return gr1_collect_strict_safety(a, n->lhs, p) &&
           gr1_collect_strict_safety(a, n->rhs, p);
  if (abssynthe_initial_supported(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (!abssynthe_global_supported(n))
    return false;
  p->safety_gua = p->safety_gua->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->safety_gua, (Node *)n);
  return true;
}

// Bucket a GR(1) consequent conjunct.  A GR(1) cluster has exactly ONE
// `assume -> guarantee` implication carrying all fairness/justice; outside it
// only sys-init Booleans and unconditional safety (`G(...)`, weak-until, or a
// strict `S W ¬A` safety) are allowed.  A bare `G F`/response or a second
// implication is rejected: it would be unconditional or independent liveness,
// which is not a single GR(1) condition (it is Streett-like).
static bool gr1_collect_consequent(Arena *a, const Node *n, Gr1Parts *p,
                                   bool *found_impl) {
  if (n->kind == NODE_AND)
    return gr1_collect_consequent(a, n->lhs, p, found_impl) &&
           gr1_collect_consequent(a, n->rhs, p, found_impl);
  if (abssynthe_initial_supported(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (n->kind == NODE_IMPL) { // the single flat GR(1) implication
    if (*found_impl)
      return false; // a second independent implication is not GR(1)
    *found_impl = true;
    return gr1_collect(a, n->lhs, true, p) && gr1_collect(a, n->rhs, false, p);
  }
  if (match_gf(n))
    return false; // unconditional `G F` justice (not gated by the assume)
  if (n->kind == NODE_W && abssynthe_body_supported(n->lhs) &&
      abssynthe_body_supported(n->rhs)) {
    if (p->nweak >= GR1_MAX_WEAK)
      return false;
    p->weak[p->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
    return true;
  }
  // Strict GR(1) safety `S_safety W ¬A_safety` (the operands carry `G(...)`, so
  // the pure weak-until above did not match).  Bucket S_safety; A_safety is
  // captured from the liveness antecedent E and drives the `violated` latch.
  if (n->kind == NODE_W && n->rhs->kind == NODE_NOT)
    return gr1_collect_strict_safety(a, n->lhs, p);
  if (!abssynthe_global_supported(n))
    return false; // bare response / anything that is not unconditional safety
  p->safety_gua = p->safety_gua->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->safety_gua, (Node *)n);
  return true;
}

// Recognize a GR(1) cluster `(EnvInit & SafetyAssume & AND G F a) ->
// (SysInit & SafetyGua & AND justice)`: >= 1 fairness, >= 1 justice, safety
// parts encodable with x-depth-0 assumptions.  TLSF renders initial conditions
// as a nested `EnvInit -> (SysInit & (assume -> guarantee))`, so peel the
// initial Boolean antecedents/conjuncts first.
bool abssynthe_gr1_parts(Arena *a, const Node *root, Gr1Parts *p) {
  *p = (Gr1Parts){.nfairness = 0,
                  .env_init = node_true(a),
                  .sys_init = node_true(a),
                  .safety_assume = node_true(a),
                  .safety_gua = node_true(a),
                  .njustice = 0};
  // Peel env-init: `EnvInit -> rest` where the antecedent is purely initial
  // (a `G`/`G F` antecedent is the real assume side, so it is not peeled).
  while (root->kind == NODE_IMPL && abssynthe_initial_supported(root->lhs)) {
    p->env_init = p->env_init->kind == NODE_TRUE
                      ? root->lhs
                      : node_and(a, (Node *)p->env_init, (Node *)root->lhs);
    root = root->rhs;
  }
  // The remainder is the guarantee side: sys-init conjuncts, unconditional
  // safety, and the single `(AND G F a) -> (AND justice)` implication (anywhere
  // in the AND tree).  gr1_collect_consequent buckets them and rejects
  // non-GR(1) shapes; the fairness/justice counts below are the final gate.
  bool found_impl = false;
  if (!gr1_collect_consequent(a, root, p, &found_impl))
    return false;
  // The emitter encodes X-depth assumptions via the assumption window, so the
  // safety assume need only be encodable (finite X-depth), not x-depth 0.
  return p->nfairness > 0 && p->njustice > 0 &&
         abssynthe_global_x_depth(p->safety_assume) != UINT32_MAX;
}

// Bounded eventually: `x | Xx | ... | X^k x` ("x within the next k steps").
static Node *bounded_eventually(Arena *a, Node *x, uint32_t k) {
  Node *r = x, *xi = x;
  for (uint32_t i = 1; i <= k; i++) {
    xi = node_x(a, xi);
    r = node_or(a, r, xi);
  }
  return r;
}

// Bounded until: `⋁_{i=0}^{k} ( (⋀_{j<i} X^j p) ∧ X^i q )` ("q within the next
// k steps, with p holding until then").  Sound under-approximation of `p U q`.
static Node *bounded_until(Arena *a, Node *p, Node *q, uint32_t k) {
  Node *acc = q;            // i = 0: q
  Node *pre = node_true(a); // ⋀_{j<i} X^j p
  Node *xp = p, *xq = q;    // X^{i-1} p (next loop) / X^i q
  for (uint32_t i = 1; i <= k; i++) {
    pre = node_and(a, pre, xp); // now ⋀_{j=0}^{i-1} X^j p
    xp = node_x(a, xp);
    xq = node_x(a, xq);
    acc = node_or(a, acc, node_and(a, pre, xq));
  }
  return acc;
}

// Bound the *guarantee* liveness of a cluster: rewrite `F x` (with `x` an
// AbsSynthe-Boolean body) to `x | Xx | ... | X^k x` at *positive* polarity
// only. Bounding a guarantee is sound — forcing `x` within k steps is a
// strictly stronger obligation than `F x`, so a controller for the bounded game
// still satisfies the unbounded spec.  Bounding an assumption would be unsound,
// so an `F` at negative polarity (an antecedent / fairness assumption) is left
// intact; it then fails `abssynthe_eligible` and the cluster stays on ltlsynt.
// This turns `G F g` into `G(g|..|X^k g)` and `G(req -> F grant)` into `G(req
// -> grant|..|X^k grant)`, both pure-safety games the existing AbsSynthe safety
// encoder handles.
Node *bound_liveness(Arena *a, const Node *n, uint32_t k, bool pos) {
  switch (n->kind) {
  case NODE_F:
    if (pos && abssynthe_body_supported(n->arg))
      return bounded_eventually(a, bound_liveness(a, n->arg, k, pos), k);
    return node_f(a, bound_liveness(a, n->arg, k, pos));
  case NODE_G:
    return node_g(a, bound_liveness(a, n->arg, k, pos));
  case NODE_X:
    return node_x(a, bound_liveness(a, n->arg, k, pos));
  case NODE_X_STRONG:
    return node_x_strong(a, bound_liveness(a, n->arg, k, pos));
  case NODE_NOT:
    return node_not(a, bound_liveness(a, n->arg, k, !pos));
  case NODE_AND:
    return node_and(a, bound_liveness(a, n->lhs, k, pos),
                    bound_liveness(a, n->rhs, k, pos));
  case NODE_OR:
    return node_or(a, bound_liveness(a, n->lhs, k, pos),
                   bound_liveness(a, n->rhs, k, pos));
  case NODE_IMPL:
    return node_impl(a, bound_liveness(a, n->lhs, k, !pos),
                     bound_liveness(a, n->rhs, k, pos));
  case NODE_U:
    if (pos && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs))
      return bounded_until(a, bound_liveness(a, n->lhs, k, pos),
                           bound_liveness(a, n->rhs, k, pos), k);
    return node_u(a, bound_liveness(a, n->lhs, k, pos),
                  bound_liveness(a, n->rhs, k, pos));
  case NODE_W: // a W b: strengthen to bounded(a U b) (sound: bounded => U => W)
    if (pos && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs))
      return bounded_until(a, bound_liveness(a, n->lhs, k, pos),
                           bound_liveness(a, n->rhs, k, pos), k);
    return node_w(a, bound_liveness(a, n->lhs, k, pos),
                  bound_liveness(a, n->rhs, k, pos));
  case NODE_R: // a R b: strengthen to bounded(b U (a&b)) (sound: => R)
  case NODE_M: // a M b == b U (a&b); bounded form is sound
    if (pos && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs)) {
      Node *bl = bound_liveness(a, n->lhs, k, pos);
      Node *br = bound_liveness(a, n->rhs, k, pos);
      return bounded_until(a, br, node_and(a, bl, br), k);
    }
    return n->kind == NODE_R ? node_r(a, bound_liveness(a, n->lhs, k, pos),
                                      bound_liveness(a, n->rhs, k, pos))
                             : node_m(a, bound_liveness(a, n->lhs, k, pos),
                                      bound_liveness(a, n->rhs, k, pos));
  default:
    // AP / constant, or EQUIV left intact — a positive liveness operator
    // surviving inside it fails eligibility and the cluster stays on ltlsynt.
    return (Node *)n;
  }
}

// ---- cluster-shape classification ----

// True if n contains at least one safety temporal operator (G, W, R) and no
// liveness operators (F, U, M) — i.e., NOT(n) would be liveness.  A purely
// propositional n (no temporal operators) returns false because NOT(prop) is
// still propositional, not liveness.
static bool is_safety_temporal(const Node *n) {
  switch (n->kind) {
  case NODE_G:
  case NODE_W:
  case NODE_R:
    return true; // explicit safety temporal operator
  case NODE_X:
  case NODE_X_STRONG:
    return is_safety_temporal(n->arg);
  case NODE_AND:
    return is_safety_temporal(n->lhs) || is_safety_temporal(n->rhs);
  default:
    // Propositional (AP, TRUE, FALSE), liveness ops, NOT, OR, IMPL —
    // none qualify as "safety temporal" for this check.
    return false;
  }
}

static void cluster_shape_visit(const Node *n, ClusterShape *shape) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
  case NODE_INT:
    return;
  case NODE_X_STRONG:
    shape->has_strong_next = true;
    [[fallthrough]];
  case NODE_X:
  case NODE_G:
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_NOT:
    // NOT(safety_temporal) is liveness: the parser simplifies `G(w) -> false`
    // to NOT(G(w)) = F(!w), and NOT(AND(G(a), G(b))) similarly.  Detect this
    // so has_liveness is set correctly for routing.  Pure propositional NOT
    // (is_safety_temporal returns false) falls through to normal recursion.
    if (is_safety_temporal(n->arg)) {
      shape->has_liveness = true;
      return;
    }
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_F:
    shape->has_liveness = true;
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_W:
    shape->has_weak_until = true;
    return; // inner structure checked by wr_structural_supported; don't recurse
  case NODE_R:
    shape->has_release = true;
    return; // inner structure checked by wr_structural_supported; don't recurse
  case NODE_U:
  case NODE_M:
    shape->has_liveness = true;
    break;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    break;
  default:
    if (node_kind_is_high_level(n->kind))
      shape->has_high_level = true;
    return;
  }
  cluster_shape_visit(n->lhs, shape);
  cluster_shape_visit(n->rhs, shape);
}

ClusterShape cluster_shape(TlsfSpec *spec, const Node *root) {
  ClusterShape shape = {.gr_level = gr_level(spec)};
  cluster_shape_visit(root, &shape);
  return shape;
}

const char *cluster_ltlsynt_reason(const ClusterShape *shape, bool finite,
                                   char *buf, size_t buf_sz) {
  if (finite) {
    snprintf(buf, buf_sz, "finite semantics are not OxiDD-eligible");
  } else if (shape->gr_level >= 0 && shape->has_liveness) {
    snprintf(buf, buf_sz,
             "GR(%d) residual with liveness; no GR backend is available "
             "without ltlsynt",
             shape->gr_level);
  } else if (shape->has_liveness) {
    snprintf(buf, buf_sz, "liveness temporal operators are not OxiDD-eligible");
  } else if (shape->has_weak_until) {
    snprintf(buf, buf_sz, "weak-until safety release is not OxiDD-eligible");
  } else if (shape->has_release) {
    snprintf(buf, buf_sz, "release safety shape is not OxiDD-eligible");
  } else if (shape->has_strong_next) {
    snprintf(buf, buf_sz, "finite-only strong-next is not OxiDD-eligible");
  } else if (shape->has_high_level) {
    snprintf(buf, buf_sz,
             "unexpanded high-level operators are not backend-eligible");
  } else {
    snprintf(buf, buf_sz, "unsupported temporal shape");
  }
  return buf;
}
