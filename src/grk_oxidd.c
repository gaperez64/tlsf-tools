// grk_oxidd.c — in-process generalized-reactivity (Streett) game solver on
// OxiDD BDDs.
//
// A cluster `⋀_k (GF a_k → GF g_k)` that survives residual clustering is a
// coupled Streett game for the system.  GR(1)'s PPS fixpoint only solves the
// single-implication form, so we use the symbolic Piterman-Pnueli Rabin
// fixpoint of Banerjee-Majumdar-Mallik-Schmuck-Soudjani ("Fast Symbolic
// Algorithms for ω-Regular Games under Strong Transition Fairness",
// arXiv:2202.07480), eq (7), specialized to the no-live-edge case (Apre == Cpre
// == the existing cpre_full).
//
// Reduction (single-set Streett, k pairs): the condition is, in DNF, a
// generalized-Rabin condition with 2^k pairs ⟨R_S, G_S⟩ where R_S = ⋃_{i∈S} a_i
// and G_S = ⋀_{i∉S} GF g_i.  We degeneralize each multi-goal G_S to a single
// Büchi via a small counter latch, then run the simple-Rabin fixpoint (7).
//
// FIRST CUT: gated to k == 2 (4 Rabin pairs + a 1-bit degeneralization
// counter). This computes and reports the winning region / realizability; the
// finite-memory strategy extraction is staged (the caller falls back to ltlsynt
// meanwhile).

#include "tlsf/grk_oxidd.h"

#include "tlsf/oxidd_common.h"

#include <stdio.h>
#include <stdlib.h>

#define OXIDD_INNER_CAP (1u << 19)
#define OXIDD_CACHE_CAP (1u << 19)

// Full cpre: ∀u. ∃c. [¬bad ∧ T[s:=next]] — state predicate in, state out.
static Bdd cpre_full(Bdd T, oxidd_bdd_substitution_t *sub_lat, Bdd notbad,
                     Bdd ctrl_cube, Bdd unc_cube) {
  Bdd img = oxidd_bdd_substitute(T, sub_lat);
  Bdd t2 = oxidd_bdd_and(notbad, img);
  Bdd ec = oxidd_bdd_exists(t2, ctrl_cube);
  Bdd result = oxidd_bdd_forall(ec, unc_cube);
  oxidd_bdd_unref(img);
  oxidd_bdd_unref(t2);
  oxidd_bdd_unref(ec);
  return result;
}

// ---------------------------------------------------------------------------
// Simple-Rabin winning-region fixpoint (eq 7), recursion over pair
// permutations.
// ---------------------------------------------------------------------------

typedef struct {
  oxidd_bdd_substitution_t *sub_lat;
  Bdd notbad, ctrl_cube, unc_cube;
  uint32_t np; // number of real Rabin pairs (index 1..np; 0 is artificial)
  Bdd *R;      // R[0..np], R[0] = ⊥ (artificial)
  Bdd *G;      // G[0..np], G[0] = ⊥ (artificial)
  // Per-level recursion scratch, length np+1 (levels 0..np):
  int *pidx;    // pidx[d] = pair chosen at level d (pidx[0] = 0, artificial)
  Bdd *Yv, *Xv; // current ν/μ iterates at each level (refs owned by level d)
  Bdd *avoid;   // avoid[d] = ⋂_{i≤d} ¬R[pidx[i]] (ref owned)
  bool err;
} RabinCtx;

static Bdd rc_cpre(RabinCtx *c, Bdd T) {
  return cpre_full(T, c->sub_lat, c->notbad, c->ctrl_cube, c->unc_cube);
}

// C_j = avoid[j] ∩ [ (G[pidx[j]] ∩ Cpre(Yv[j])) ∪ Cpre(Xv[j]) ].
static Bdd rc_cterm(RabinCtx *c, uint32_t j) {
  Bdd cy = rc_cpre(c, c->Yv[j]);
  Bdd gcy = oxidd_bdd_and(c->G[c->pidx[j]], cy);
  Bdd cx = rc_cpre(c, c->Xv[j]);
  Bdd inner = oxidd_bdd_or(gcy, cx);
  Bdd res = oxidd_bdd_and(c->avoid[j], inner);
  oxidd_bdd_unref(cy);
  oxidd_bdd_unref(gcy);
  oxidd_bdd_unref(cx);
  oxidd_bdd_unref(inner);
  return res;
}

static bool pair_used(RabinCtx *c, uint32_t depth, int q) {
  for (uint32_t d = 1; d <= depth; d++)
    if (c->pidx[d] == q)
      return true;
  return false;
}

// Computes νY_d. μX_d. [body_d], given enclosing iterates Yv/Xv[0..d-1] set.
static Bdd rabin_level(RabinCtx *c, oxidd_bdd_manager_t m, uint32_t d);

// body at level d: union of deeper levels (d<np) or the C-term union (d==np).
static Bdd rabin_body(RabinCtx *c, oxidd_bdd_manager_t m, uint32_t d) {
  if (d == c->np) {
    Bdd body = oxidd_bdd_false(m);
    for (uint32_t j = 0; j <= c->np && !c->err; j++) {
      Bdd cj = rc_cterm(c, j);
      Bdd nb = oxidd_bdd_or(body, cj);
      oxidd_bdd_unref(body);
      oxidd_bdd_unref(cj);
      body = nb;
      if (bdd_invalid(body))
        c->err = true;
    }
    return body;
  }
  Bdd body = oxidd_bdd_false(m);
  for (int q = 1; q <= (int)c->np && !c->err; q++) {
    if (pair_used(c, d, q))
      continue;
    c->pidx[d + 1] = q;
    Bdd nr = oxidd_bdd_not(c->R[q]);
    c->avoid[d + 1] = oxidd_bdd_and(c->avoid[d], nr);
    oxidd_bdd_unref(nr);
    Bdd part = rabin_level(c, m, d + 1);
    oxidd_bdd_unref(c->avoid[d + 1]);
    c->avoid[d + 1] = (Bdd){0};
    Bdd nb = oxidd_bdd_or(body, part);
    oxidd_bdd_unref(body);
    oxidd_bdd_unref(part);
    body = nb;
    if (bdd_invalid(body))
      c->err = true;
  }
  return body;
}

static Bdd rabin_level(RabinCtx *c, oxidd_bdd_manager_t m, uint32_t d) {
  Bdd Y = oxidd_bdd_true(m); // ν from ⊤
  for (;;) {
    if (c->err) {
      oxidd_bdd_unref(Y);
      return oxidd_bdd_false(m);
    }
    c->Yv[d] = oxidd_bdd_ref(Y);
    Bdd X = oxidd_bdd_false(m); // μ from ⊥
    for (;;) {
      c->Xv[d] = oxidd_bdd_ref(X);
      Bdd body = rabin_body(c, m, d);
      oxidd_bdd_unref(c->Xv[d]);
      c->Xv[d] = (Bdd){0};
      if (bdd_invalid(body) || c->err) {
        oxidd_bdd_unref(X);
        oxidd_bdd_unref(body);
        c->err = true;
        oxidd_bdd_unref(c->Yv[d]);
        c->Yv[d] = (Bdd){0};
        return oxidd_bdd_false(m);
      }
      bool conv = bdd_eq(body, X);
      oxidd_bdd_unref(X);
      X = body;
      if (conv)
        break;
    }
    oxidd_bdd_unref(c->Yv[d]);
    c->Yv[d] = (Bdd){0};
    bool conv = bdd_eq(X, Y);
    oxidd_bdd_unref(Y);
    Y = X;
    if (conv)
      break;
  }
  return Y;
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

Aig *solve_grk_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  if (!game)
    return nullptr;

  uint32_t npairs = aig_num_pairs(game);
  uint32_t m_goals = aig_num_justice(game);
  uint32_t m_fair = aig_num_fairness(game);

  // FIRST CUT gate: exactly two single-set Streett pairs.
  if (npairs != 2 || m_goals != 2 || m_fair != 2) {
    aig_free(game);
    return nullptr;
  }
  // Each pair must carry exactly one justice and one fairness record.
  uint32_t jc[2] = {0, 0}, fc[2] = {0, 0};
  for (uint32_t j = 0; j < m_goals; j++) {
    uint32_t p = aig_justice_pair(game, j);
    if (p < 2)
      jc[p]++;
  }
  for (uint32_t i = 0; i < m_fair; i++) {
    uint32_t p = aig_fairness_pair(game, i);
    if (p < 2)
      fc[p]++;
  }
  if (jc[0] != 1 || jc[1] != 1 || fc[0] != 1 || fc[1] != 1) {
    aig_free(game);
    return nullptr;
  }

  uint32_t nin = aig_num_inputs(game);
  uint32_t nlat = aig_num_latches(game);
  uint32_t nand = aig_num_ands(game);

  uint32_t maxvar = 0;
  for (uint32_t i = 0; i < nin; i++) {
    uint32_t lit;
    aig_input_name(game, i, &lit);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < nlat; i++) {
    uint32_t cur;
    aig_latch_at(game, i, &cur, nullptr, nullptr);
    if (cur / 2 > maxvar)
      maxvar = cur / 2;
  }
  for (uint32_t i = 0; i < nand; i++) {
    uint32_t lhs;
    aig_and_at(game, i, &lhs, nullptr, nullptr);
    if (lhs / 2 > maxvar)
      maxvar = lhs / 2;
  }

  // BDD var layout: inputs, game latches, then 1 degeneralization-counter var.
  uint32_t nvars = nin + nlat + 1;
  uint32_t cnt_var_off = nin + nlat; // counter var index (relative to var_base)

  bool own_mgr = (oxidd_session_get()._p == NULL);
  oxidd_bdd_manager_t m;
  uint32_t var_base;
  if (own_mgr) {
    uint32_t exp = nvars + 6 < 22 ? nvars + 6 : 22;
    uint32_t cap = (1u << exp) < (1u << 10) ? (1u << 10) : (1u << exp);
    m = oxidd_bdd_manager_new(cap, cap, 1);
    oxidd_bdd_manager_add_vars(m, nvars);
    var_base = 0;
  } else {
    m = oxidd_session_get();
    var_base = oxidd_session_alloc_vars(nvars);
  }

  Bdd *var_bdd = calloc(maxvar + 1, sizeof *var_bdd);
  Bdd *next_bdd = calloc(nlat + 1, sizeof *next_bdd); // +1 for the counter
  uint32_t *cvars = nin ? calloc(nin, sizeof *cvars) : nullptr;
  uint32_t *uvars = nin ? calloc(nin, sizeof *uvars) : nullptr;
  if (!var_bdd || !next_bdd || (nin && (!cvars || !uvars))) {
    free(var_bdd);
    free(next_bdd);
    free(cvars);
    free(uvars);
    if (own_mgr)
      oxidd_bdd_manager_unref(m);
    aig_free(game);
    return nullptr;
  }

  Bdd notbad = {0}, ctrl_cube = {0}, unc_cube = {0}, bad = {0};
  Bdd a0 = {0}, a1 = {0}, g0 = {0}, g1 = {0}, cvar = {0}, c_next = {0};
  Bdd Rb[4] = {{0}}, Gb[4] = {{0}};
  oxidd_bdd_substitution_t *sub_lat = nullptr;
  uint32_t ncv = 0, nuv = 0;
  bool ok = true;

  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *name = aig_input_name(game, p, &lit);
    var_bdd[lit / 2] = oxidd_bdd_var(m, var_base + p);
    if (is_controllable(name))
      cvars[ncv++] = var_base + p;
    else
      uvars[nuv++] = var_base + p;
  }
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, nullptr);
    var_bdd[cur / 2] = oxidd_bdd_var(m, var_base + nin + j);
  }
  cvar = oxidd_bdd_var(m, var_base + cnt_var_off);

  for (uint32_t i = 0; i < nand && ok; i++) {
    uint32_t lhs, r0, r1;
    aig_and_at(game, i, &lhs, &r0, &r1);
    Bdd a = lit_to_bdd(m, var_bdd, r0);
    Bdd b = lit_to_bdd(m, var_bdd, r1);
    Bdd cc = oxidd_bdd_and(a, b);
    oxidd_bdd_unref(a);
    oxidd_bdd_unref(b);
    var_bdd[lhs / 2] = cc;
    if (bdd_invalid(cc))
      ok = false;
  }

  if (ok) {
    uint32_t badlit = aig_output_lit(game, "bad");
    bad = (badlit == UINT32_MAX) ? oxidd_bdd_false(m)
                                 : lit_to_bdd(m, var_bdd, badlit);
    notbad = oxidd_bdd_not(bad);
    if (bdd_invalid(notbad))
      ok = false;
  }
  for (uint32_t j = 0; j < nlat && ok; j++) {
    uint32_t next;
    aig_latch_at(game, j, nullptr, &next, nullptr);
    next_bdd[j] = lit_to_bdd(m, var_bdd, next);
    if (bdd_invalid(next_bdd[j]))
      ok = false;
  }

  // Pair goal/assumption BDDs (single-set, by pair tag).
  if (ok) {
    for (uint32_t j = 0; j < m_goals; j++) {
      const uint32_t *lits;
      uint32_t n;
      aig_justice_at(game, j, &lits, &n);
      Bdd gb = (n > 0) ? lit_to_bdd(m, var_bdd, lits[0]) : oxidd_bdd_true(m);
      if (aig_justice_pair(game, j) == 0)
        g0 = gb;
      else
        g1 = gb;
    }
    for (uint32_t i = 0; i < m_fair; i++) {
      Bdd fb = lit_to_bdd(m, var_bdd, aig_fairness_at(game, i));
      if (aig_fairness_pair(game, i) == 0)
        a0 = fb;
      else
        a1 = fb;
    }
    if (bdd_invalid(g0) || bdd_invalid(g1) || bdd_invalid(a0) ||
        bdd_invalid(a1))
      ok = false;
  }

  // Degeneralization counter c (reset 0): GF(c ∧ g1) ⟺ GF g0 ∧ GF g1.
  //   c_next = (¬c ∧ g0) ∨ (c ∧ ¬g1).
  if (ok) {
    Bdd nc = oxidd_bdd_not(cvar);
    Bdd ng1 = oxidd_bdd_not(g1);
    Bdd t0 = oxidd_bdd_and(nc, g0);
    Bdd t1 = oxidd_bdd_and(cvar, ng1);
    c_next = oxidd_bdd_or(t0, t1);
    oxidd_bdd_unref(nc);
    oxidd_bdd_unref(ng1);
    oxidd_bdd_unref(t0);
    oxidd_bdd_unref(t1);
    next_bdd[nlat] = c_next; // owned by next_bdd cleanup
    if (bdd_invalid(c_next))
      ok = false;
  }

  // Latch (and counter) substitution s := next.
  if (ok) {
    sub_lat = oxidd_bdd_substitution_new(nlat + 1);
    for (uint32_t j = 0; j < nlat; j++)
      oxidd_bdd_substitution_add_pair(sub_lat, var_base + nin + j, next_bdd[j]);
    oxidd_bdd_substitution_add_pair(sub_lat, var_base + cnt_var_off,
                                    next_bdd[nlat]);
    ctrl_cube = cube_of(m, cvars, ncv);
    unc_cube = cube_of(m, uvars, nuv);
    if (!sub_lat || bdd_invalid(ctrl_cube) || bdd_invalid(unc_cube))
      ok = false;
  }

  // Four simple-Rabin pairs of the Streett(2) -> generalized-Rabin reduction:
  //   S=∅    : R=⊥,        G=ĝ=(c∧g1)   (degeneralized {g0,g1})
  //   S={0}  : R=a0,       G=g1
  //   S={1}  : R=a1,       G=g0
  //   S={0,1}: R=a0∪a1,    G=⊤
  if (ok) {
    Rb[0] = oxidd_bdd_false(m);
    Gb[0] = oxidd_bdd_and(cvar, g1);
    Rb[1] = oxidd_bdd_ref(a0);
    Gb[1] = oxidd_bdd_ref(g1);
    Rb[2] = oxidd_bdd_ref(a1);
    Gb[2] = oxidd_bdd_ref(g0);
    Rb[3] = oxidd_bdd_or(a0, a1);
    Gb[3] = oxidd_bdd_true(m);
    for (int i = 0; i < 4; i++)
      if (bdd_invalid(Rb[i]) || bdd_invalid(Gb[i]))
        ok = false;
  }

  Bdd W = {0};
  if (ok) {
    // Rabin pair arrays indexed 1..4 (index 0 = artificial ⟨⊥,⊥⟩).
    Bdd R5[5], G5[5];
    R5[0] = oxidd_bdd_false(m);
    G5[0] = oxidd_bdd_false(m);
    for (int i = 0; i < 4; i++) {
      R5[i + 1] = Rb[i];
      G5[i + 1] = Gb[i];
    }
    int pidx[5] = {0, 0, 0, 0, 0};
    Bdd Yv[5] = {{0}}, Xv[5] = {{0}}, avoid[5] = {{0}};
    RabinCtx rc = {.sub_lat = sub_lat,
                   .notbad = notbad,
                   .ctrl_cube = ctrl_cube,
                   .unc_cube = unc_cube,
                   .np = 4,
                   .R = R5,
                   .G = G5,
                   .pidx = pidx,
                   .Yv = Yv,
                   .Xv = Xv,
                   .avoid = avoid,
                   .err = false};
    rc.avoid[0] = oxidd_bdd_true(m); // ⋂ of nothing
    W = rabin_level(&rc, m, 0);
    oxidd_bdd_unref(rc.avoid[0]);
    oxidd_bdd_unref(R5[0]);
    oxidd_bdd_unref(G5[0]);
    if (rc.err || bdd_invalid(W))
      ok = false;
  }

  // Realizability: W at the reset state (game latches + counter c = 0).
  int realizable = 0;
  if (ok) {
    oxidd_var_no_bool_pair_t *args = calloc(nlat + 1, sizeof *args);
    if (args) {
      for (uint32_t j = 0; j < nlat; j++) {
        uint32_t reset;
        aig_latch_at(game, j, nullptr, nullptr, &reset);
        args[j].var = var_base + nin + j;
        args[j].val = reset != 0;
      }
      args[nlat].var = var_base + cnt_var_off;
      args[nlat].val = false;
      realizable = oxidd_bdd_eval(W, args, nlat + 1) ? 1 : 0;
      free(args);
    } else {
      ok = false;
    }
  }

  if (getenv("TLSF_GRK_DEBUG"))
    fprintf(stderr, "[grk] k=2 Streett: ok=%d realizable=%d\n", ok, realizable);

  if (ok && !realizable)
    *unreal = 1;

  // Cleanup.
  oxidd_bdd_unref(W);
  for (int i = 0; i < 4; i++) {
    oxidd_bdd_unref(Rb[i]);
    oxidd_bdd_unref(Gb[i]);
  }
  oxidd_bdd_unref(a0);
  oxidd_bdd_unref(a1);
  oxidd_bdd_unref(g0);
  oxidd_bdd_unref(g1);
  oxidd_bdd_unref(cvar);
  oxidd_bdd_unref(bad);
  oxidd_bdd_unref(notbad);
  oxidd_bdd_unref(ctrl_cube);
  oxidd_bdd_unref(unc_cube);
  for (uint32_t j = 0; j <= nlat; j++)
    oxidd_bdd_unref(next_bdd[j]);
  for (uint32_t v = 0; v <= maxvar; v++)
    oxidd_bdd_unref(var_bdd[v]);
  if (sub_lat)
    oxidd_bdd_substitution_free(sub_lat);
  if (own_mgr)
    oxidd_bdd_manager_unref(m);
  else
    oxidd_session_gc();
  free(var_bdd);
  free(next_bdd);
  free(cvars);
  free(uvars);
  aig_free(game);

  // Strategy extraction is staged: even when realizable, return nullptr so the
  // caller falls back to ltlsynt for the actual controller.  The realizability
  // verdict above is validated against Spot before the strategy work lands.
  return nullptr;
}
