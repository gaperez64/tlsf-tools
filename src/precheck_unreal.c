/// precheck_unreal.c — sound OVER-approximation UNREALIZABLE pre-check over the
/// propositional safety fragment of the expanded cover.  See
/// include/tlsf/precheck_unreal.h for the verdict-trust contract and the
/// one-step environment-win argument this implements.

#include "tlsf/precheck_unreal.h"

#include "tlsf/apset.h"
#include "tlsf/ast.h"
#include "tlsf/cover.h"
#include "tlsf/spec.h"

#include <oxidd/capi.h>

#include <stdbool.h>
#include <stdint.h>

// ---------------------------------------------------------------------------
// Propositional Node -> BDD (one var per cover AP; var index == ap index)
// ---------------------------------------------------------------------------

typedef struct {
  oxidd_bdd_manager_t m;
  const ApTable *aps;
  bool bail; // set on any node the builder cannot represent
} BoolCtx;

/// True iff `n` is purely propositional (boolean) over atomic propositions.
static bool propositional(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return propositional(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return propositional(n->lhs) && propositional(n->rhs);
  default:
    return false;
  }
}

/// The propositional formula a constraint requires to hold at step 0, or NULL
/// when the constraint is temporal (no usable step-0 boolean requirement).
static const Node *step0_bool_body(const Constraint *c) {
  const Node *f = c->formula;
  if (!f)
    return nullptr;
  if (propositional(f))
    // bare boolean / INITIALLY / PRESET, or a boolean invariant (REQUIRE/ASSERT
    // under an implicit G): required at step 0 either way.
    return f;
  if (c->invariant_wrapped)
    return nullptr; // implicit-G body has a temporal operator
  if (f->kind == NODE_G && propositional(f->arg))
    return f->arg; // G(boolean): the body is required at step 0
  return nullptr;  // temporal
}

/// Build the BDD of a propositional `n`.  Each call returns a fresh reference
/// the caller owns; intermediates are unref'd here.  Sets `c->bail` (and
/// returns ⊤) on an unsupported node or an AP missing from the table.
static oxidd_bdd_t node_to_bdd(BoolCtx *c, const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return oxidd_bdd_true(c->m);
  case NODE_FALSE:
    return oxidd_bdd_false(c->m);
  case NODE_AP: {
    int32_t idx = ap_table_find(c->aps, n->name);
    if (idx < 0) {
      c->bail = true;
      return oxidd_bdd_true(c->m);
    }
    return oxidd_bdd_var(c->m, (oxidd_var_no_t)idx);
  }
  case NODE_NOT: {
    oxidd_bdd_t a = node_to_bdd(c, n->arg);
    oxidd_bdd_t r = oxidd_bdd_not(a);
    oxidd_bdd_unref(a);
    return r;
  }
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    oxidd_bdd_t l = node_to_bdd(c, n->lhs);
    oxidd_bdd_t r = node_to_bdd(c, n->rhs);
    oxidd_bdd_t res;
    switch (n->kind) {
    case NODE_AND:
      res = oxidd_bdd_and(l, r);
      break;
    case NODE_OR:
      res = oxidd_bdd_or(l, r);
      break;
    case NODE_IMPL:
      res = oxidd_bdd_imp(l, r);
      break;
    default:
      res = oxidd_bdd_equiv(l, r);
      break;
    }
    oxidd_bdd_unref(l);
    oxidd_bdd_unref(r);
    return res;
  }
  default:
    c->bail = true;
    return oxidd_bdd_true(c->m);
  }
}

static inline bool invalid(oxidd_bdd_t f) { return f._p == nullptr; }

// ---------------------------------------------------------------------------
// Pre-check
// ---------------------------------------------------------------------------

bool precheck_trivially_unreal(const ConstraintCover *cov) {
  if (!cov || cov->count == 0)
    return false;
  const TlsfSpec *spec = cov->spec;
  if (spec && semantics_is_finite(spec->info.semantics))
    return false; // v1: infinite-word (Mealy/Moore) semantics only

  const ApTable *aps = &cov->aps;
  const uint32_t nap = aps->count;
  if (nap == 0)
    return false;

  // Every AP must be exactly one of input/output; a missing or ambiguous flag
  // would make the env/controller partition unsound to quantify over.
  for (uint32_t i = 0; i < nap; i++) {
    bool in = ap_table_flags(aps, i) & AP_FLAG_INPUT;
    bool out = ap_table_flags(aps, i) & AP_FLAG_OUTPUT;
    if (in == out)
      return false;
  }

  // Classify.  Bail on any temporal assumption (dropping it would strengthen
  // the environment and risk a false UNREAL).  Temporal guarantees are simply
  // ignored: doing so only weakens the spec, which keeps an UNREAL sound.
  bool any_guarantee_bool = false;
  for (uint32_t i = 0; i < cov->count; i++) {
    const Constraint *c = &cov->items[i];
    const Node *b = step0_bool_body(c);
    if (c->assumption_side) {
      if (!b)
        return false;
    } else if (c->guarantee_side && b) {
      any_guarantee_bool = true;
    }
  }
  if (!any_guarantee_bool)
    return false; // boolean fragment has nothing to violate at step 0

  // Right-size a fresh manager off the AP count (cf. safety_oxidd.c): the
  // pre-check runs before the synthesis session manager is created.
  uint32_t exp = nap + 6 < 22 ? nap + 6 : 22;
  uint32_t inner_cap = (1u << exp) < (1u << 10) ? (1u << 10) : (1u << exp);
  oxidd_bdd_manager_t m = oxidd_bdd_manager_new(inner_cap, inner_cap, 1);
  if (m._p == nullptr)
    return false;
  oxidd_bdd_manager_add_vars(m, nap);
  BoolCtx ctx = {.m = m, .aps = aps, .bail = false};

  // G = ⋀ step-0 boolean guarantee bodies; A = ⋀ step-0 boolean assumptions.
  oxidd_bdd_t G = oxidd_bdd_true(m);
  oxidd_bdd_t A = oxidd_bdd_true(m);
  for (uint32_t i = 0; i < cov->count && !ctx.bail; i++) {
    const Constraint *c = &cov->items[i];
    const Node *b = step0_bool_body(c);
    if (!b)
      continue;
    oxidd_bdd_t bb = node_to_bdd(&ctx, b);
    if (c->guarantee_side) {
      oxidd_bdd_t ng = oxidd_bdd_and(G, bb);
      oxidd_bdd_unref(G);
      G = ng;
    } else if (c->assumption_side) {
      oxidd_bdd_t na = oxidd_bdd_and(A, bb);
      oxidd_bdd_unref(A);
      A = na;
    }
    oxidd_bdd_unref(bb);
  }

  bool result = false;
  if (!ctx.bail && !invalid(G) && !invalid(A)) {
    // H = A ∧ ¬G;  EnvWin = ¬ ∃outputs. ¬H.
    oxidd_bdd_t notG = oxidd_bdd_not(G);
    oxidd_bdd_t H = oxidd_bdd_and(A, notG);
    oxidd_bdd_t notH = oxidd_bdd_not(H);

    oxidd_bdd_t out_cube = oxidd_bdd_true(m);
    for (uint32_t i = 0; i < nap; i++) {
      if (!(ap_table_flags(aps, i) & AP_FLAG_OUTPUT))
        continue;
      oxidd_bdd_t v = oxidd_bdd_var(m, (oxidd_var_no_t)i);
      oxidd_bdd_t nc = oxidd_bdd_and(out_cube, v);
      oxidd_bdd_unref(out_cube);
      oxidd_bdd_unref(v);
      out_cube = nc;
    }

    if (!invalid(notH) && !invalid(out_cube)) {
      oxidd_bdd_t ex = oxidd_bdd_exists(notH, out_cube);
      if (!invalid(ex)) {
        oxidd_bdd_t envwin = oxidd_bdd_not(ex);
        if (!invalid(envwin))
          result = oxidd_bdd_satisfiable(envwin);
        oxidd_bdd_unref(envwin);
      }
      oxidd_bdd_unref(ex);
    }
    oxidd_bdd_unref(out_cube);
    oxidd_bdd_unref(notH);
    oxidd_bdd_unref(H);
    oxidd_bdd_unref(notG);
  }

  oxidd_bdd_unref(G);
  oxidd_bdd_unref(A);
  oxidd_bdd_manager_unref(m);
  return result;
}
