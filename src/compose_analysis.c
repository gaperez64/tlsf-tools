// compose_analysis.c — pure AST/arena cluster analysis for tlsfcompose.
//
// Eligibility gates and X-depth accounting for the direct / W/R / strict-safety
// safety paths, the GR(1) decomposition (`aig_gr1_parts`), liveness
// bounding (`bound_liveness`), and cluster-shape classification used to pick a
// backend / explain an ltlsynt fallback.  No `Aig` construction here — see
// compose_games.c.  Shared types live in compose_internal.h.

#include "compose_internal.h"

#include "tlsf/gr.h"

#include <stdio.h>
#include <string.h>

bool aig_body_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
    return aig_body_ok(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return aig_body_ok(n->lhs) && aig_body_ok(n->rhs);
  default:
    return false;
  }
}

bool aig_initial_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return aig_initial_ok(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return aig_initial_ok(n->lhs) && aig_initial_ok(n->rhs);
  default:
    return false;
  }
}

// Like aig_initial_ok but also allows X/X_STRONG operators,
// for initial-state conjuncts of the form `X(phi)` or `X(phi) -> bool`.
// Used by the W/R safety path to accept X-delayed initial constraints.
bool aig_initial_x_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return aig_initial_x_ok(n->arg);
  case NODE_X:
  case NODE_X_STRONG:
    return aig_initial_x_ok(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return aig_initial_x_ok(n->lhs) && aig_initial_x_ok(n->rhs);
  default:
    return false;
  }
}

static bool global_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return aig_body_ok(n->arg);
  case NODE_AND:
    return global_ok(n->lhs) && global_ok(n->rhs);
  default:
    return false;
  }
}

static bool safety_cond_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_AND:
    return safety_cond_ok(n->lhs) && safety_cond_ok(n->rhs);
  case NODE_G:
    return aig_body_ok(n->arg);
  default:
    return aig_initial_ok(n);
  }
}

uint32_t aig_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
    return 1 + aig_x_depth(n->arg);
  case NODE_NOT:
    return aig_x_depth(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    uint32_t a = aig_x_depth(n->lhs), b = aig_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return 0;
  }
}

// Like aig_x_depth but also recurses into W/R operands.  Required for
// W/R-extended G bodies where X operators can appear inside W/R sub-expressions
// (e.g. G(req -> X(a R (b -> X c))): the nested X inside the R rhs contributes
// to the history-latch depth needed by compile_at_lag).
static uint32_t wr_body_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_G: // G(phi) in a G body: absorbed, recurse into arg
    return wr_body_x_depth(n->arg);
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

uint32_t aig_safety_cond_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_AND: {
    uint32_t a = aig_safety_cond_x_depth(n->lhs);
    uint32_t b = aig_safety_cond_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_G:
    return aig_x_depth(n->arg);
  default:
    return aig_initial_ok(n) ? 0 : UINT32_MAX;
  }
}

uint32_t aig_global_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_G:
    return aig_x_depth(n->arg);
  case NODE_AND: {
    uint32_t a = aig_global_x_depth(n->lhs);
    uint32_t b = aig_global_x_depth(n->rhs);
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
  if (!aig_body_ok(impl->lhs) || !aig_body_ok(rhs->lhs) ||
      !aig_body_ok(rhs->rhs))
    return false;
  *req = impl->lhs;
  *inner = rhs;
  *xdelay = x;
  return true;
}

// Strict version: W/R inside G body require both operands to be pure Boolean.
// Used by aig_eligible (direct path) to avoid routing extended W/R
// patterns to build_aig_game, which cannot handle them.
static bool g_body_direct_supported(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return g_body_direct_supported(n->lhs) && g_body_direct_supported(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    return g_body_direct_supported(n->arg);
  case NODE_W:
  case NODE_R:
    return aig_body_ok(n->lhs) && aig_body_ok(n->rhs);
  case NODE_IMPL: {
    const Node *req, *inner;
    bool xdelay;
    if (wr_response_parts(n, &req, &inner, &xdelay))
      return true;
    if (aig_body_ok(n->lhs))
      return g_body_direct_supported(n->rhs);
    return false;
  }
  default:
    return aig_body_ok(n);
  }
}

static bool safety_direct_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return g_body_direct_supported(n->arg);
  case NODE_AND:
    return safety_direct_ok(n->lhs) && safety_direct_ok(n->rhs);
  case NODE_W:
  case NODE_R:
    return aig_body_ok(n->lhs) && aig_body_ok(n->rhs);
  default:
    return aig_initial_ok(n);
  }
}

// A conjunct of a `G(...)` body: Boolean, a bare weak-until / release, or a
// re-armed response.  Under the outer G a bare W/R collapses to an invariant --
// `G(a W b) == G(a|b)`, `G(a R b) == G(b)` -- so no monitor is needed; a
// response `G(req -> [X](a W/R b))` re-arms a monitor each time req fires.
bool g_body_wr_supported(const Node *n) {
  switch (n->kind) {
  case NODE_G: // G(G(phi)) == G(phi); nested G in a G body is absorbed
    return g_body_wr_supported(n->arg);
  case NODE_AND:
    return g_body_wr_supported(n->lhs) && g_body_wr_supported(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    return g_body_wr_supported(n->arg);
  case NODE_W: {
    // G(a W b) == G(a|b): both operands must be propositional.
    if (aig_body_ok(n->lhs) && aig_body_ok(n->rhs))
      return true;
    // Pattern B: (cond -> X(a W/R b)) W B — cond, a, b, B propositional.
    // The outer W collapses because cond->X(inner) is trivially true when
    // !cond; when cond fires, arm a sub-monitor for inner W/R.
    if (!aig_body_ok(n->rhs))
      return false; // B must be propositional
    const Node *lhs = n->lhs;
    if (lhs->kind != NODE_IMPL || !aig_body_ok(lhs->lhs))
      return false;
    const Node *xn = lhs->rhs;
    if (xn->kind == NODE_X || xn->kind == NODE_X_STRONG)
      xn = xn->arg;
    return (xn->kind == NODE_W || xn->kind == NODE_R) && aig_body_ok(xn->lhs) &&
           aig_body_ok(xn->rhs);
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
    if (aig_body_ok(n->lhs))
      return g_body_wr_supported(n->rhs);
    return false;
  }
  default:
    return aig_body_ok(n);
  }
}

// Pure-safety guarantee that may also carry weak-until `a W b` or release
// `a R b` (Boolean operands): genuine safety properties.  A top-level `a W b`
// gets a "released" monitor latch; a `W`/`R` *inside* a `G` body collapses to a
// plain invariant.  Both are exactly encodable alongside `G(...)` invariants.
bool aig_safety_wr_ok(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return g_body_wr_supported(n->arg);
  case NODE_AND:
    return aig_safety_wr_ok(n->lhs) && aig_safety_wr_ok(n->rhs);
  case NODE_W:
  case NODE_R:
    return aig_body_ok(n->lhs) && aig_body_ok(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    if (n->arg->kind == NODE_G && g_body_wr_supported(n->arg->arg))
      return true;
    return aig_initial_x_ok(n);
  default:
    // A bare Boolean or X-delayed conjunct is an initial-state constraint.
    return aig_initial_x_ok(n);
  }
}

uint32_t aig_safety_wr_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_G:
    return wr_body_x_depth(n->arg); // must recurse into W/R for nested X
  case NODE_AND: {
    uint32_t a = aig_safety_wr_x_depth(n->lhs);
    uint32_t b = aig_safety_wr_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_W:
  case NODE_R: {
    uint32_t a = aig_x_depth(n->lhs), b = aig_x_depth(n->rhs);
    return a > b ? a : b;
  }
  case NODE_X:
  case NODE_X_STRONG:
    if (n->arg->kind == NODE_G && g_body_wr_supported(n->arg->arg))
      return 1 + wr_body_x_depth(n->arg->arg);
    if (!aig_initial_x_ok(n))
      return UINT32_MAX;
    return aig_x_depth(n);
  default:
    // X-delayed initial constraint: its X-depth sets the gate-latch offset.
    if (!aig_initial_x_ok(n))
      return UINT32_MAX;
    return aig_x_depth(n);
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
  case NODE_X:
  case NODE_X_STRONG:
    if (n->arg->kind == NODE_G && g_body_wr_supported(n->arg->arg))
      return false;
    return true;
  default:
    return true;
  }
}

// True if n has an initial-state conjunct that requires an X-delayed gate
// (i.e., aig_initial_x_ok but not aig_initial_ok).
bool wr_has_x_initial(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_G:
  case NODE_W:
  case NODE_R:
    return false;
  case NODE_AND:
    return wr_has_x_initial(n->lhs) || wr_has_x_initial(n->rhs);
  case NODE_X:
  case NODE_X_STRONG:
    if (n->arg->kind == NODE_G && g_body_wr_supported(n->arg->arg))
      return false;
    return !aig_initial_ok(n) && aig_initial_x_ok(n);
  default:
    return !aig_initial_ok(n) && aig_initial_x_ok(n);
  }
}

// True if n contains a one-step delayed invariant `X G(body)`.  The W/R game
// builder checks these from the second logical step onward.
bool wr_has_delayed_global(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
    return n->arg->kind == NODE_G && g_body_wr_supported(n->arg->arg);
  case NODE_AND:
    return wr_has_delayed_global(n->lhs) || wr_has_delayed_global(n->rhs);
  case NODE_IMPL:
    return wr_has_delayed_global(n->lhs) || wr_has_delayed_global(n->rhs);
  default:
    return false;
  }
}

// True if the top-level safety formula has a bare W/R conjunct (not inside G).
// build_aig_game encodes bare W/R with release latches compiled at lag=depth;
// when depth > 0 (from G X conjuncts) this interaction can spuriously
// over-constrain the game.  Use this to decide whether to trust an UNREALIZABLE
// result or fall back to ltlsynt.
bool wr_has_bare_wr(const Node *n) {
  switch (n->kind) {
  case NODE_W:
  case NODE_R:
    return true;
  case NODE_AND:
    return wr_has_bare_wr(n->lhs) || wr_has_bare_wr(n->rhs);
  default:
    return false; // G, initial Boolean, etc. — no bare W/R at this level
  }
}

bool aig_eligible(const Node *root, bool finite) {
  if (finite)
    return false;
  if (root->kind == NODE_IMPL)
    return global_ok(root->lhs) && aig_global_x_depth(root->lhs) == 0 &&
           safety_direct_ok(root->rhs);
  return safety_direct_ok(root);
}

bool aig_strict_safety_parts(const Node *root, const Node **sys,
                             const Node **env) {
  if (root->kind != NODE_W || root->rhs->kind != NODE_NOT)
    return false;
  if (!safety_cond_ok(root->lhs) || !safety_cond_ok(root->rhs->arg))
    return false;
  *sys = root->lhs;
  *env = root->rhs->arg;
  return true;
}

// ---- GR(1): `G F a` fairness assumptions + recurrence/response justice ----

// ---- GR(1): G F a fairness + recurrence/response justice decomposition ----

// `G F x` with `x` current-state Boolean -> x, else nullptr.
static const Node *match_gf(const Node *n) {
  if (n->kind == NODE_G && n->arg->kind == NODE_F &&
      aig_initial_ok(n->arg->arg))
    return n->arg->arg;
  return nullptr;
}

// `G(req -> F grant)` with current-state Boolean req/grant.
static bool match_response(const Node *n, const Node **req,
                           const Node **grant) {
  if (n->kind != NODE_G || n->arg->kind != NODE_IMPL)
    return false;
  const Node *body = n->arg;
  if (body->rhs->kind != NODE_F || !aig_initial_ok(body->lhs) ||
      !aig_initial_ok(body->rhs->arg))
    return false;
  *req = body->lhs;
  *grant = body->rhs->arg;
  return true;
}

static bool spec_has_input(const TlsfSpec *spec, const char *name) {
  for (uint32_t i = 0; i < spec->input_count; i++)
    if (!strcmp(spec->inputs[i].name, name))
      return true;
  return false;
}

static bool mentions_env_input(const TlsfSpec *spec, const Node *n) {
  switch (n->kind) {
  case NODE_AP:
    return spec_has_input(spec, n->name);
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_G:
  case NODE_F:
    return mentions_env_input(spec, n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_W:
  case NODE_R:
  case NODE_M:
    return mentions_env_input(spec, n->lhs) || mentions_env_input(spec, n->rhs);
  default:
    return false;
  }
}

// `F goal` with current-state Boolean goal controlled by outputs/constants.
static const Node *match_eventual(const TlsfSpec *spec, const Node *n) {
  return n->kind == NODE_F && aig_initial_ok(n->arg) &&
                 !mentions_env_input(spec, n->arg)
             ? n->arg
             : nullptr;
}

static void gr1_parts_init(Arena *a, Gr1Parts *p) {
  *p = (Gr1Parts){.nfairness = 0,
                  .env_init = node_true(a),
                  .sys_init = node_true(a),
                  .safety_assume = node_true(a),
                  .safety_gua = node_true(a),
                  .njustice = 0,
                  .nweak = 0};
}

static bool response_monitor_collect(Arena *a, const Node *n, Gr1Parts *p) {
  if (n->kind == NODE_AND)
    return response_monitor_collect(a, n->lhs, p) &&
           response_monitor_collect(a, n->rhs, p);

  if (aig_initial_ok(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }

  const Node *req = nullptr, *grant = nullptr;
  if (match_response(n, &req, &grant)) {
    if (p->njustice >= GR1_MAX_JUSTICE)
      return false;
    p->justice[p->njustice++] =
        (Gr1Justice){.req = req, .target = grant, .kind = GR1_JUSTICE_RESPONSE};
    return true;
  }

  if (!global_ok(n))
    return false;
  p->safety_gua = p->safety_gua->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->safety_gua, (Node *)n);
  return true;
}

// Recognize standalone exact response-monitor clusters:
// `AND(G(req -> F grant), safety..., init...)`, with req/grant current-state
// Boolean formulas.  This deliberately excludes unconditional `F`, `U`, and
// nested/next-bearing liveness bodies; those need a different monitor contract.
bool aig_response_monitor_parts(Arena *a, const Node *root, Gr1Parts *p) {
  gr1_parts_init(a, p);
  if (!response_monitor_collect(a, root, p))
    return false;
  return p->njustice > 0 && aig_global_x_depth(p->safety_gua) != UINT32_MAX;
}

static bool eventual_monitor_collect(TlsfSpec *spec, const Node *n,
                                     Gr1Parts *p) {
  Arena *a = spec->arena;
  if (n->kind == NODE_AND)
    return eventual_monitor_collect(spec, n->lhs, p) &&
           eventual_monitor_collect(spec, n->rhs, p);

  if (aig_initial_ok(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }

  const Node *target = match_eventual(spec, n);
  if (target) {
    if (p->njustice >= GR1_MAX_JUSTICE)
      return false;
    p->justice[p->njustice++] = (Gr1Justice){
        .req = nullptr, .target = target, .kind = GR1_JUSTICE_EVENTUAL};
    return true;
  }

  if (!global_ok(n))
    return false;
  p->safety_gua = p->safety_gua->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->safety_gua, (Node *)n);
  return true;
}

// Recognize standalone exact one-shot eventuality clusters:
// `AND(F(goal), safety..., init...)`, where goal is current-state Boolean and
// does not mention environment inputs.  A pending monitor starts armed and
// clears forever once goal holds.
bool aig_eventual_monitor_parts(TlsfSpec *spec, const Node *root, Gr1Parts *p) {
  gr1_parts_init(spec->arena, p);
  if (!eventual_monitor_collect(spec, root, p))
    return false;
  return p->njustice > 0 && aig_global_x_depth(p->safety_gua) != UINT32_MAX;
}

static bool match_until(const TlsfSpec *spec, const Node *n, const Node **p,
                        const Node **q) {
  if (n->kind != NODE_U || !aig_initial_ok(n->lhs) || !aig_initial_ok(n->rhs) ||
      mentions_env_input(spec, n->rhs))
    return false;
  *p = n->lhs;
  *q = n->rhs;
  return true;
}

static bool until_monitor_collect(TlsfSpec *spec, const Node *n,
                                  Gr1Parts *parts) {
  Arena *a = spec->arena;
  if (n->kind == NODE_AND)
    return until_monitor_collect(spec, n->lhs, parts) &&
           until_monitor_collect(spec, n->rhs, parts);

  if (aig_initial_ok(n)) {
    parts->sys_init = parts->sys_init->kind == NODE_TRUE
                          ? n
                          : node_and(a, (Node *)parts->sys_init, (Node *)n);
    return true;
  }

  const Node *p = nullptr, *q = nullptr;
  if (match_until(spec, n, &p, &q)) {
    if (parts->nweak >= GR1_MAX_WEAK || parts->njustice >= GR1_MAX_JUSTICE)
      return false;
    parts->weak[parts->nweak++] = (Gr1WeakUntil){p, q};
    parts->justice[parts->njustice++] =
        (Gr1Justice){.req = nullptr, .target = q, .kind = GR1_JUSTICE_EVENTUAL};
    return true;
  }

  if (!global_ok(n))
    return false;
  parts->safety_gua = parts->safety_gua->kind == NODE_TRUE
                          ? n
                          : node_and(a, (Node *)parts->safety_gua, (Node *)n);
  return true;
}

// Recognize positive guarantee-side until clusters.  `p U q` is compiled as
// the safety obligation `p W q` plus the one-shot eventuality `F q`; q must not
// mention environment inputs because the system must be able to force progress.
bool aig_until_monitor_parts(TlsfSpec *spec, const Node *root, Gr1Parts *p) {
  gr1_parts_init(spec->arena, p);
  if (!until_monitor_collect(spec, root, p))
    return false;
  return p->njustice > 0 && aig_global_x_depth(p->safety_gua) != UINT32_MAX;
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
  if (aig_initial_ok(n)) {
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
    p->justice[p->njustice++] = (Gr1Justice){
        .req = nullptr, .target = gf, .kind = GR1_JUSTICE_RECURRENCE};
    return true;
  } else {
    const Node *req = nullptr, *grant = nullptr;
    if (match_response(n, &req, &grant)) {
      if (p->njustice >= GR1_MAX_JUSTICE)
        return false;
      p->justice[p->njustice++] = (Gr1Justice){
          .req = req, .target = grant, .kind = GR1_JUSTICE_RESPONSE};
      return true;
    }
    // A weak-until `a W b` (Boolean a, b) is a pure-safety guarantee: a holds
    // until b, or forever.  Encoded with a "released" monitor in the emitter.
    if (n->kind == NODE_W && aig_body_ok(n->lhs) && aig_body_ok(n->rhs)) {
      if (p->nweak >= GR1_MAX_WEAK)
        return false;
      p->weak[p->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
      return true;
    }
  }
  if (!global_ok(n))
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
  if (aig_initial_ok(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (!global_ok(n))
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
                                   bool *found_impl, bool *found_bare_justice) {
  if (n->kind == NODE_AND)
    return gr1_collect_consequent(a, n->lhs, p, found_impl,
                                  found_bare_justice) &&
           gr1_collect_consequent(a, n->rhs, p, found_impl, found_bare_justice);
  if (aig_initial_ok(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (n->kind == NODE_IMPL) { // the single flat GR(1) implication
    if (*found_impl || *found_bare_justice)
      return false; // a second independent implication is not GR(1)
    *found_impl = true;
    return gr1_collect(a, n->lhs, true, p) && gr1_collect(a, n->rhs, false, p);
  }
  const Node *gf = match_gf(n);
  if (gf) {
    if (*found_impl || p->njustice >= GR1_MAX_JUSTICE)
      return false; // don't mix unconditional justice with env fairness
    *found_bare_justice = true;
    p->justice[p->njustice++] = (Gr1Justice){
        .req = nullptr, .target = gf, .kind = GR1_JUSTICE_RECURRENCE};
    return true;
  }
  if (n->kind == NODE_W && aig_body_ok(n->lhs) && aig_body_ok(n->rhs)) {
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
  if (!global_ok(n))
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
bool aig_gr1_parts(Arena *a, const Node *root, Gr1Parts *p) {
  gr1_parts_init(a, p);
  // Peel env-init: `EnvInit -> rest` where the antecedent is purely initial
  // (a `G`/`G F` antecedent is the real assume side, so it is not peeled).
  while (root->kind == NODE_IMPL && aig_initial_ok(root->lhs)) {
    p->env_init = p->env_init->kind == NODE_TRUE
                      ? root->lhs
                      : node_and(a, (Node *)p->env_init, (Node *)root->lhs);
    root = root->rhs;
  }
  // The remainder is the guarantee side: sys-init conjuncts, unconditional
  // safety, and the single `(AND G F a) -> (AND justice)` implication (anywhere
  // in the AND tree), or a recurrence-only `G F goal` with no fairness
  // implication.  gr1_collect_consequent buckets them and rejects non-GR(1)
  // shapes; the fairness/justice counts below are the final gate.
  bool found_impl = false;
  bool found_bare_justice = false;
  if (!gr1_collect_consequent(a, root, p, &found_impl, &found_bare_justice))
    return false;
  // The emitter encodes X-depth assumptions via the assumption window, so the
  // safety assume need only be encodable (finite X-depth), not x-depth 0.
  return p->njustice > 0 && (p->nfairness > 0 || !found_impl) &&
         aig_global_x_depth(p->safety_assume) != UINT32_MAX;
}

// ---- Generalized reactivity (Streett) recognition -------------------------
//
// A generalized-reactivity cluster carries several independent
// `(AND G F a_k) -> (AND G F/response g_k)` implications (Streett pairs) that
// share one safety/init/weak skeleton.  aig_gr1_parts rejects the second
// implication; aig_grk_parts instead opens a new GrPair per implication,
// leaving the single-pair (ordinary GR(1)) shape to aig_gr1_parts.

static void grk_parts_init(Arena *a, GrkParts *p) {
  *p = (GrkParts){.env_init = node_true(a),
                  .sys_init = node_true(a),
                  .safety_assume = node_true(a),
                  .safety_gua = node_true(a),
                  .nweak = 0,
                  .npairs = 0,
                  .rabin = false};
}

// Bucket one conjunct of a pair's fairness antecedent: `G F a` -> pair
// fairness, initial Booleans -> shared env-init, `G(...)` safety -> shared
// safety assume.
static bool grk_collect_assume(Arena *a, const Node *n, GrkParts *gp,
                               GrPair *pair) {
  if (n->kind == NODE_AND)
    return grk_collect_assume(a, n->lhs, gp, pair) &&
           grk_collect_assume(a, n->rhs, gp, pair);
  if (aig_initial_ok(n)) {
    gp->env_init = gp->env_init->kind == NODE_TRUE
                       ? n
                       : node_and(a, (Node *)gp->env_init, (Node *)n);
    return true;
  }
  const Node *gf = match_gf(n);
  if (gf) {
    if (pair->nfairness >= GR1_MAX_FAIRNESS)
      return false;
    pair->fairness[pair->nfairness++] = gf;
    return true;
  }
  if (!global_ok(n))
    return false;
  gp->safety_assume = gp->safety_assume->kind == NODE_TRUE
                          ? n
                          : node_and(a, (Node *)gp->safety_assume, (Node *)n);
  return true;
}

// Bucket one conjunct of a pair's justice consequent: `G F g`/response -> pair
// justice, `a W b` -> shared weak monitor, init -> shared sys-init, `G(...)`
// safety -> shared safety guarantee.
static bool grk_collect_guarantee(Arena *a, const Node *n, GrkParts *gp,
                                  GrPair *pair) {
  if (n->kind == NODE_AND)
    return grk_collect_guarantee(a, n->lhs, gp, pair) &&
           grk_collect_guarantee(a, n->rhs, gp, pair);
  if (aig_initial_ok(n)) {
    gp->sys_init = gp->sys_init->kind == NODE_TRUE
                       ? n
                       : node_and(a, (Node *)gp->sys_init, (Node *)n);
    return true;
  }
  const Node *gf = match_gf(n);
  if (gf) {
    if (pair->njustice >= GR1_MAX_JUSTICE)
      return false;
    pair->justice[pair->njustice++] = (Gr1Justice){
        .req = nullptr, .target = gf, .kind = GR1_JUSTICE_RECURRENCE};
    return true;
  }
  const Node *req = nullptr, *grant = nullptr;
  if (match_response(n, &req, &grant)) {
    if (pair->njustice >= GR1_MAX_JUSTICE)
      return false;
    pair->justice[pair->njustice++] =
        (Gr1Justice){.req = req, .target = grant, .kind = GR1_JUSTICE_RESPONSE};
    return true;
  }
  if (n->kind == NODE_W && aig_body_ok(n->lhs) && aig_body_ok(n->rhs)) {
    if (gp->nweak >= GR1_MAX_WEAK)
      return false;
    gp->weak[gp->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
    return true;
  }
  if (!global_ok(n))
    return false;
  gp->safety_gua = gp->safety_gua->kind == NODE_TRUE
                       ? n
                       : node_and(a, (Node *)gp->safety_gua, (Node *)n);
  return true;
}

// The shared no-fairness pair collects bare (unconditional) justice goals that
// appear outside any implication; they must all be met infinitely often.
static GrPair *grk_bare_pair(GrkParts *gp) {
  for (uint32_t k = 0; k < gp->npairs; k++)
    if (gp->pairs[k].nfairness == 0)
      return &gp->pairs[k];
  if (gp->npairs >= GR1_MAX_PAIRS)
    return nullptr;
  GrPair *pr = &gp->pairs[gp->npairs++];
  *pr = (GrPair){0};
  return pr;
}

// Walk the top-level conjuncts of the (env-init-peeled) cluster, opening a pair
// per `... -> ...` implication and bucketing the shared safety skeleton.
static bool grk_collect_top(Arena *a, const Node *n, GrkParts *gp) {
  if (n->kind == NODE_AND)
    return grk_collect_top(a, n->lhs, gp) && grk_collect_top(a, n->rhs, gp);
  if (aig_initial_ok(n)) {
    gp->sys_init = gp->sys_init->kind == NODE_TRUE
                       ? n
                       : node_and(a, (Node *)gp->sys_init, (Node *)n);
    return true;
  }
  if (n->kind == NODE_IMPL) {
    if (gp->npairs >= GR1_MAX_PAIRS)
      return false;
    GrPair *pr = &gp->pairs[gp->npairs];
    *pr = (GrPair){0};
    if (!grk_collect_assume(a, n->lhs, gp, pr) ||
        !grk_collect_guarantee(a, n->rhs, gp, pr))
      return false;
    // A genuine reactive pair must contribute at least one justice goal; a
    // pure-safety consequent is not generalized reactivity.
    if (pr->njustice == 0)
      return false;
    gp->npairs++;
    return true;
  }
  const Node *gf = match_gf(n);
  if (gf) {
    GrPair *pr = grk_bare_pair(gp);
    if (!pr || pr->njustice >= GR1_MAX_JUSTICE)
      return false;
    pr->justice[pr->njustice++] = (Gr1Justice){
        .req = nullptr, .target = gf, .kind = GR1_JUSTICE_RECURRENCE};
    return true;
  }
  const Node *req = nullptr, *grant = nullptr;
  if (match_response(n, &req, &grant)) {
    GrPair *pr = grk_bare_pair(gp);
    if (!pr || pr->njustice >= GR1_MAX_JUSTICE)
      return false;
    pr->justice[pr->njustice++] =
        (Gr1Justice){.req = req, .target = grant, .kind = GR1_JUSTICE_RESPONSE};
    return true;
  }
  if (n->kind == NODE_W && aig_body_ok(n->lhs) && aig_body_ok(n->rhs)) {
    if (gp->nweak >= GR1_MAX_WEAK)
      return false;
    gp->weak[gp->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
    return true;
  }
  if (!global_ok(n))
    return false;
  gp->safety_gua = gp->safety_gua->kind == NODE_TRUE
                       ? n
                       : node_and(a, (Node *)gp->safety_gua, (Node *)n);
  return true;
}

// Recognize a generalized-reactivity (Streett) cluster: >= 2 fairness->justice
// pairs over a shared safety skeleton, with at least one genuine env-fairness
// pair (otherwise it is plain conjunctive recurrence, handled by GR(1)).
bool aig_grk_parts(Arena *a, const Node *root, GrkParts *p) {
  grk_parts_init(a, p);
  while (root->kind == NODE_IMPL && aig_initial_ok(root->lhs)) {
    p->env_init = p->env_init->kind == NODE_TRUE
                      ? root->lhs
                      : node_and(a, (Node *)p->env_init, (Node *)root->lhs);
    root = root->rhs;
  }
  if (!grk_collect_top(a, root, p))
    return false;
  uint32_t total_justice = 0;
  bool any_fair = false;
  for (uint32_t k = 0; k < p->npairs; k++) {
    total_justice += p->pairs[k].njustice;
    if (p->pairs[k].nfairness > 0)
      any_fair = true;
  }
  return p->npairs >= 2 && total_justice > 0 && any_fair &&
         aig_global_x_depth(p->safety_assume) != UINT32_MAX &&
         aig_global_x_depth(p->safety_gua) != UINT32_MAX;
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
// intact; it then fails `aig_eligible` and the cluster stays on ltlsynt.
// This turns `G F g` into `G(g|..|X^k g)` and `G(req -> F grant)` into `G(req
// -> grant|..|X^k grant)`, both pure-safety games the existing AbsSynthe safety
// encoder handles.
Node *bound_liveness(Arena *a, const Node *n, uint32_t k, bool pos) {
  switch (n->kind) {
  case NODE_F:
    if (pos && aig_body_ok(n->arg))
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
    if (pos && aig_body_ok(n->lhs) && aig_body_ok(n->rhs))
      return bounded_until(a, bound_liveness(a, n->lhs, k, pos),
                           bound_liveness(a, n->rhs, k, pos), k);
    return node_u(a, bound_liveness(a, n->lhs, k, pos),
                  bound_liveness(a, n->rhs, k, pos));
  case NODE_W: // a W b: strengthen to bounded(a U b) (sound: bounded => U => W)
    if (pos && aig_body_ok(n->lhs) && aig_body_ok(n->rhs))
      return bounded_until(a, bound_liveness(a, n->lhs, k, pos),
                           bound_liveness(a, n->rhs, k, pos), k);
    return node_w(a, bound_liveness(a, n->lhs, k, pos),
                  bound_liveness(a, n->rhs, k, pos));
  case NODE_R: // a R b: strengthen to bounded(b U (a&b)) (sound: => R)
  case NODE_M: // a M b == b U (a&b); bounded form is sound
    if (pos && aig_body_ok(n->lhs) && aig_body_ok(n->rhs)) {
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
