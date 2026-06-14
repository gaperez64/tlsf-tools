// gr1_oxidd.c — in-process GR(1) game solver on OxiDD BDDs.
//
// Implements the Piterman-Pnueli-Sa'ar (PPS) tri-nested fixpoint:
//
//   W* = νZ. ⋀_j [ μY. νX. cpre( (Z ∩ goal_j) ∪ Y ∪ (X ∩ ⋃_i ¬fair_i) ) ]
//
// The game is in the standard AbsSynthe AIGER format (see safety_oxidd.c for
// conventions); the only difference is that the Aig also carries justice[]
// (system Büchi goals) and fair[] (environment fairness assumptions) records.
//
// Strategy: the output AIG adds m one-hot goal-counter latches curr[0..m-1]
// (reset curr[0]=1, rest 0).  At each step the system picks controllables to
// make progress toward the current goal, and advances the counter when the
// current game state satisfies that goal and the state is in the winning
// region.

#include "tlsf/gr1_oxidd.h"

#include <oxidd/capi.h>

#include <stdlib.h>
#include <string.h>

#define CONTROLLABLE_PREFIX "controllable_"

#define OXIDD_INNER_CAP (1u << 19)
#define OXIDD_CACHE_CAP (1u << 19)

typedef oxidd_bdd_t Bdd;

static inline bool bdd_invalid(Bdd f) { return f._p == NULL; }

static bool is_controllable(const char *name) {
  return strncmp(name, CONTROLLABLE_PREFIX, strlen(CONTROLLABLE_PREFIX)) == 0;
}

// ---------------------------------------------------------------------------
// BDD helpers (duplicated from safety_oxidd.c — all static, no shared header)
// ---------------------------------------------------------------------------

static Bdd lit_to_bdd(oxidd_bdd_manager_t m, const Bdd *var_bdd, uint32_t lit) {
  if (lit == AIG_FALSE)
    return oxidd_bdd_false(m);
  if (lit == AIG_TRUE)
    return oxidd_bdd_true(m);
  Bdd base = var_bdd[lit / 2];
  return (lit & 1u) ? oxidd_bdd_not(base) : oxidd_bdd_ref(base);
}

static Bdd cube_of(oxidd_bdd_manager_t m, const uint32_t *vars, uint32_t n) {
  Bdd cube = oxidd_bdd_true(m);
  for (uint32_t i = 0; i < n; i++) {
    Bdd v = oxidd_bdd_var(m, vars[i]);
    Bdd nx = oxidd_bdd_and(cube, v);
    oxidd_bdd_unref(cube);
    oxidd_bdd_unref(v);
    cube = nx;
  }
  return cube;
}

static bool bdd_eq(Bdd a, Bdd b) {
  Bdd e = oxidd_bdd_equiv(a, b);
  if (bdd_invalid(e)) {
    oxidd_bdd_unref(e);
    return false;
  }
  bool r = oxidd_bdd_valid(e);
  oxidd_bdd_unref(e);
  return r;
}

// ---------------------------------------------------------------------------
// BDD-node -> AIG memo (open-addressing hash on 16-byte handle identity)
// ---------------------------------------------------------------------------

typedef struct {
  Bdd *keys;
  uint32_t *lits;
  bool *used;
  size_t cap, n;
} Memo;

static uint64_t memo_hash(Bdd k) {
  const unsigned char *p = (const unsigned char *)&k;
  uint64_t h = 1469598103934665603ull;
  for (size_t i = 0; i < sizeof k; i++) {
    h ^= p[i];
    h *= 1099511628211ull;
  }
  return h;
}

static bool memo_grow(Memo *t, size_t cap) {
  Bdd *keys = calloc(cap, sizeof *keys);
  uint32_t *lits = calloc(cap, sizeof *lits);
  bool *used = calloc(cap, sizeof *used);
  if (!keys || !lits || !used) {
    free(keys);
    free(lits);
    free(used);
    return false;
  }
  for (size_t i = 0; i < t->cap; i++) {
    if (!t->used[i])
      continue;
    size_t j = memo_hash(t->keys[i]) & (cap - 1);
    while (used[j])
      j = (j + 1) & (cap - 1);
    keys[j] = t->keys[i];
    lits[j] = t->lits[i];
    used[j] = true;
  }
  free(t->keys);
  free(t->lits);
  free(t->used);
  t->keys = keys;
  t->lits = lits;
  t->used = used;
  t->cap = cap;
  return true;
}

static bool memo_get(const Memo *t, Bdd k, uint32_t *lit) {
  if (t->cap == 0)
    return false;
  size_t j = memo_hash(k) & (t->cap - 1);
  while (t->used[j]) {
    if (memcmp(&t->keys[j], &k, sizeof k) == 0) {
      *lit = t->lits[j];
      return true;
    }
    j = (j + 1) & (t->cap - 1);
  }
  return false;
}

static bool memo_put(Memo *t, Bdd k, uint32_t lit) {
  if (t->n * 10 >= t->cap * 7)
    if (!memo_grow(t, t->cap ? t->cap * 2 : 64))
      return false;
  size_t j = memo_hash(k) & (t->cap - 1);
  while (t->used[j]) {
    if (memcmp(&t->keys[j], &k, sizeof k) == 0) {
      t->lits[j] = lit;
      return true;
    }
    j = (j + 1) & (t->cap - 1);
  }
  t->keys[j] = k;
  t->lits[j] = lit;
  t->used[j] = true;
  t->n++;
  return true;
}

static void memo_free(Memo *t) {
  free(t->keys);
  free(t->lits);
  free(t->used);
  *t = (Memo){0};
}

// ---------------------------------------------------------------------------
// BDD -> AIG (memoised ite expansion)
// ---------------------------------------------------------------------------

typedef struct {
  Aig *strat;
  const uint32_t *var2lit;
  Memo memo;
  bool error;
} Bdd2Aig;

static uint32_t bdd2aig(Bdd2Aig *ctx, Bdd f) {
  if (ctx->error)
    return AIG_FALSE;
  if (oxidd_bdd_node_level(f) == (oxidd_level_no_t)-1)
    return oxidd_bdd_satisfiable(f) ? AIG_TRUE : AIG_FALSE;
  uint32_t cached;
  if (memo_get(&ctx->memo, f, &cached))
    return cached;
  oxidd_var_no_t v = oxidd_bdd_node_var(f);
  uint32_t vlit = ctx->var2lit[v];
  if (vlit == UINT32_MAX) {
    ctx->error = true;
    return AIG_FALSE;
  }
  Bdd t = oxidd_bdd_cofactor_true(f);
  Bdd e = oxidd_bdd_cofactor_false(f);
  uint32_t at = bdd2aig(ctx, t);
  uint32_t ae = bdd2aig(ctx, e);
  oxidd_bdd_unref(t);
  oxidd_bdd_unref(e);
  uint32_t hi = aig_and(ctx->strat, vlit, at);
  uint32_t lo = aig_and(ctx->strat, aig_not(vlit), ae);
  uint32_t res = aig_or(ctx->strat, hi, lo);
  if (!memo_put(&ctx->memo, f, res))
    ctx->error = true;
  return res;
}

// ---------------------------------------------------------------------------
// Dynamic array of BDD references (for μ-fixpoint Y-levels)
// ---------------------------------------------------------------------------

typedef struct {
  Bdd *arr;
  uint32_t n, cap;
} BddVec;

static bool bddvec_push(BddVec *v, Bdd b) {
  if (v->n == v->cap) {
    uint32_t nc = v->cap ? v->cap * 2 : 4;
    Bdd *narr = realloc(v->arr, nc * sizeof *narr);
    if (!narr)
      return false;
    v->arr = narr;
    v->cap = nc;
  }
  v->arr[v->n++] = b;
  return true;
}

static void bddvec_free_all(BddVec *v) {
  for (uint32_t i = 0; i < v->n; i++)
    oxidd_bdd_unref(v->arr[i]);
  free(v->arr);
  *v = (BddVec){0};
}

// ---------------------------------------------------------------------------
// cpre helpers
// ---------------------------------------------------------------------------

// Full cpre: ∀u ∃c [¬bad ∧ T[s:=next]]  — T is a state predicate, result too.
static Bdd cpre_full(Bdd T, oxidd_bdd_substitution_t *sub_lat, Bdd notbad,
                     Bdd ctrl_cube, Bdd unc_cube) {
  Bdd img = oxidd_bdd_substitute(T, sub_lat);
  Bdd t2 = oxidd_bdd_and(notbad, img);
  Bdd ec = oxidd_bdd_exists(t2, ctrl_cube);
  Bdd result = oxidd_bdd_forall(ec, unc_cube);
  oxidd_bdd_unref(img);
  oxidd_bdd_unref(t2);
  oxidd_bdd_unref(ec);
  return result; // new ref; UINT32_MAX on error → caller checks bdd_invalid
}

// Unquantified cpre: ¬bad ∧ T[s:=next]  — result is over (s, u, c).
static Bdd cpre_unquantified(Bdd T, oxidd_bdd_substitution_t *sub_lat,
                             Bdd notbad) {
  Bdd img = oxidd_bdd_substitute(T, sub_lat);
  Bdd result = oxidd_bdd_and(notbad, img);
  oxidd_bdd_unref(img);
  return result;
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

Aig *solve_gr1_oxidd(Aig *game, int *unreal) {
  *unreal = 0;
  if (!game)
    return nullptr;

  uint32_t m_goals = aig_num_justice(game);
  uint32_t m_fair = aig_num_fairness(game);

  // A GR(1) game must have at least one justice goal.  If none, the game is
  // pure safety and should go through solve_safety_oxidd instead.
  if (m_goals == 0) {
    aig_free(game);
    return nullptr;
  }

  uint32_t nin = aig_num_inputs(game);
  uint32_t nlat = aig_num_latches(game);
  uint32_t nand = aig_num_ands(game);

  // Highest AIG variable index, to size the literal -> BDD map.
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

  // Allocations.
  // BDD var layout: 0..nin-1 = inputs, nin..nin+nlat-1 = latches,
  //                 nin+nlat..nin+nlat+m_goals-1 = goal counter curr[j].
  uint32_t nvars = nin + nlat + m_goals;

  Aig *strat = nullptr;
  Bdd *var_bdd = calloc(maxvar + 1, sizeof *var_bdd);
  Bdd *next_bdd = nlat ? calloc(nlat, sizeof *next_bdd) : nullptr;
  Bdd *goal_bdd = m_goals ? calloc(m_goals, sizeof *goal_bdd) : nullptr;
  Bdd *fair_bdd = m_fair ? calloc(m_fair, sizeof *fair_bdd) : nullptr;
  Bdd *curr_bdd = m_goals ? calloc(m_goals, sizeof *curr_bdd) : nullptr;
  uint32_t *var2lit = calloc(nvars, sizeof *var2lit);
  uint32_t *lat_lit = nlat ? calloc(nlat, sizeof *lat_lit) : nullptr;
  uint32_t *curr_latch_lit =
      m_goals ? calloc(m_goals, sizeof *curr_latch_lit) : nullptr;
  uint32_t *cvars = nin ? calloc(nin, sizeof *cvars) : nullptr;
  uint32_t *uvars = nin ? calloc(nin, sizeof *uvars) : nullptr;
  uint32_t *cinput = nin ? calloc(nin, sizeof *cinput) : nullptr;
  Bdd *strat_f = nullptr;
  BddVec *y_levels = m_goals ? calloc(m_goals, sizeof *y_levels) : nullptr;

  if (!var_bdd || (nlat && !next_bdd) || !goal_bdd || (m_fair && !fair_bdd) ||
      !curr_bdd || !var2lit || (nlat && !lat_lit) || !curr_latch_lit ||
      (nin && (!cvars || !uvars || !cinput)) || !y_levels) {
    free(var_bdd);
    free(next_bdd);
    free(goal_bdd);
    free(fair_bdd);
    free(curr_bdd);
    free(var2lit);
    free(lat_lit);
    free(curr_latch_lit);
    free(cvars);
    free(uvars);
    free(cinput);
    free(y_levels);
    aig_free(game);
    return nullptr;
  }

  oxidd_bdd_manager_t m =
      oxidd_bdd_manager_new(OXIDD_INNER_CAP, OXIDD_CACHE_CAP, 1);
  oxidd_bdd_manager_add_vars(m, nvars);

  Bdd bad = {0}, notbad = {0}, not_fair = {0}, W = {0}, ctrl_cube = {0},
      unc_cube = {0};
  oxidd_bdd_substitution_t *sub_lat = nullptr;
  uint32_t ncv = 0, nuv = 0;
  bool ok = true;

  // Variables: input p -> bdd var p; latch j -> bdd var nin+j;
  //            goal counter j -> bdd var nin+nlat+j.
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *name = aig_input_name(game, p, &lit);
    var_bdd[lit / 2] = oxidd_bdd_var(m, p);
    if (is_controllable(name)) {
      cvars[ncv] = p;
      cinput[ncv] = p;
      ncv++;
    } else {
      uvars[nuv++] = p;
    }
  }
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, nullptr);
    var_bdd[cur / 2] = oxidd_bdd_var(m, nin + j);
  }
  for (uint32_t j = 0; j < m_goals; j++)
    curr_bdd[j] = oxidd_bdd_var(m, nin + nlat + j);

  // And-gates in topological order.
  for (uint32_t i = 0; i < nand && ok; i++) {
    uint32_t lhs, r0, r1;
    aig_and_at(game, i, &lhs, &r0, &r1);
    Bdd a = lit_to_bdd(m, var_bdd, r0);
    Bdd b = lit_to_bdd(m, var_bdd, r1);
    Bdd c = oxidd_bdd_and(a, b);
    oxidd_bdd_unref(a);
    oxidd_bdd_unref(b);
    var_bdd[lhs / 2] = c;
    if (bdd_invalid(c))
      ok = false;
  }

  // bad + latch next-functions.
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

  // Justice goal BDDs (one lit per justice property, the pending-monitor
  // negation).
  for (uint32_t j = 0; j < m_goals && ok; j++) {
    const uint32_t *lits;
    uint32_t n;
    aig_justice_at(game, j, &lits, &n);
    goal_bdd[j] = (n > 0) ? lit_to_bdd(m, var_bdd, lits[0]) : oxidd_bdd_true(m);
    if (bdd_invalid(goal_bdd[j]))
      ok = false;
  }

  // Fairness BDDs + not_fair = ⋃_i ¬fair_i (env breaks at least one
  // assumption).
  not_fair = oxidd_bdd_false(m); // ⊥ when m_fair == 0: env is always "fair"
  for (uint32_t i = 0; i < m_fair && ok; i++) {
    uint32_t lit = aig_fairness_at(game, i);
    fair_bdd[i] = lit_to_bdd(m, var_bdd, lit);
    if (bdd_invalid(fair_bdd[i])) {
      ok = false;
      break;
    }
    Bdd nfi = oxidd_bdd_not(fair_bdd[i]);
    Bdd tmp = oxidd_bdd_or(not_fair, nfi);
    oxidd_bdd_unref(not_fair);
    oxidd_bdd_unref(nfi);
    not_fair = tmp;
    if (bdd_invalid(not_fair))
      ok = false;
  }

  // Latch substitution s_j := next_j (used in cpre and W-substitution).
  if (ok) {
    sub_lat = oxidd_bdd_substitution_new(nlat);
    for (uint32_t j = 0; j < nlat; j++)
      oxidd_bdd_substitution_add_pair(sub_lat, nin + j, next_bdd[j]);
    ctrl_cube = cube_of(m, cvars, ncv);
    unc_cube = cube_of(m, uvars, nuv);
    if (!sub_lat || bdd_invalid(ctrl_cube) || bdd_invalid(unc_cube))
      ok = false;
  }

  // -----------------------------------------------------------------------
  // PPS tri-nested fixpoint
  //   W* = νZ. ⋀_j [ μY. νX. cpre( (Z∩goal_j) ∪ Y ∪ (X∩not_fair) ) ]
  //
  // Y_levels[j] accumulates the μ-iterations for the last outer ν-step.
  // -----------------------------------------------------------------------

  if (ok) {
    W = oxidd_bdd_true(m); // outer ν starts at ⊤

    for (;;) { // outer ν-fixpoint over W (= Z)
      Bdd W_prev = oxidd_bdd_ref(W);
      Bdd W_new = oxidd_bdd_true(m); // ⋀_j Win_j

      for (uint32_t j = 0; j < m_goals && ok; j++) {
        bddvec_free_all(&y_levels[j]); // reset levels for this outer iteration

        Bdd Y = oxidd_bdd_false(m); // μ-fixpoint from ⊥

        for (;;) {                   // μ-fixpoint over Y
          Bdd X = oxidd_bdd_true(m); // inner ν-fixpoint from ⊤

          for (;;) { // inner ν-fixpoint over X
            // target = (W ∩ goal_j) ∪ Y ∪ (X ∩ not_fair)
            Bdd wg = oxidd_bdd_and(W, goal_bdd[j]);
            Bdd wgy = oxidd_bdd_or(wg, Y);
            Bdd xnf = oxidd_bdd_and(X, not_fair);
            Bdd target = oxidd_bdd_or(wgy, xnf);
            oxidd_bdd_unref(wg);
            oxidd_bdd_unref(wgy);
            oxidd_bdd_unref(xnf);

            Bdd X_new = cpre_full(target, sub_lat, notbad, ctrl_cube, unc_cube);
            oxidd_bdd_unref(target);

            if (bdd_invalid(X_new)) {
              oxidd_bdd_unref(X);
              ok = false;
              break;
            }
            bool inner_conv = bdd_eq(X_new, X);
            oxidd_bdd_unref(X);
            X = X_new;
            if (inner_conv)
              break;
          }
          if (!ok)
            break;

          // Save this μ-level and check μ-convergence.
          bool mu_conv = bdd_eq(X, Y);
          if (!bddvec_push(&y_levels[j], oxidd_bdd_ref(X))) {
            oxidd_bdd_unref(X);
            ok = false;
            break;
          }
          oxidd_bdd_unref(Y);
          Y = X; // Y holds the ref (bddvec holds an extra ref)
          if (mu_conv)
            break;
        }
        if (!ok)
          break;

        // Win_j = Y (converged μ); W_new ∧= Win_j.
        Bdd tmp = oxidd_bdd_and(W_new, Y);
        oxidd_bdd_unref(W_new);
        oxidd_bdd_unref(Y);
        W_new = tmp;
        if (bdd_invalid(W_new)) {
          ok = false;
          break;
        }
      }

      bool outer_conv = ok && bdd_eq(W_new, W_prev);
      oxidd_bdd_unref(W);
      oxidd_bdd_unref(W_prev);
      W = W_new;
      if (outer_conv || !ok)
        break;
    }
  }

  // Bdd W is now W* (or invalid if !ok).

  // -----------------------------------------------------------------------
  // Realizability: W* must hold at latch reset cube.
  // -----------------------------------------------------------------------

  if (ok) {
    oxidd_var_no_bool_pair_t *args =
        nlat ? calloc(nlat, sizeof *args) : nullptr;
    for (uint32_t j = 0; j < nlat; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      args[j].var = nin + j;
      args[j].val = reset != 0;
    }
    bool realizable = oxidd_bdd_eval(W, args, nlat);
    free(args);
    if (!realizable) {
      *unreal = 1;
      ok = false;
    }
  }

  // -----------------------------------------------------------------------
  // Strategy extraction
  //
  // Build M_total(s, curr[], u, c) as follows:
  //
  //   For each goal j:
  //     at_goal_j = W* ∩ goal_bdd[j]
  //     M_j = (s ∈ at_goal_j) ∧ cpre_c(W*)              // advance: any safe
  //     move
  //         ∪ (s ∈ level_j_0 \ at_goal_j) ∧ cpre_c(at_goal_j)
  //         ∪ (s ∈ level_j_k \ level_j_{k-1} \ at_goal_j) ∧ cpre_c(Y_{k-1} ∪
  //         at_goal_j)
  //         ...
  //
  //   M_total = ⋃_j [curr_bdd[j] ∧ M_j]
  //
  // Then Skolem-extract f_k(s, curr[], u) from M_total for each controllable.
  // -----------------------------------------------------------------------

  if (ok && !*unreal) {
    strat_f = ncv ? calloc(ncv, sizeof *strat_f) : nullptr;
    if (ncv && !strat_f)
      ok = false;
  }

  // Goal-counter next-functions and strategy move predicate both use
  // "effective_curr[j]": when all curr bits are 0 (initial state, all reset to
  // 0), treat it as curr[0]=1.  This avoids the AIGER reset=1 latch line that
  // Spot's parser does not accept.
  //
  //   any_curr = ⋃_j curr[j]
  //   effective_curr[j] = curr[j]       (j > 0)
  //                     = curr[0] ∨ ¬any_curr   (j = 0)
  //
  // After step 1 at least one curr latch becomes 1 (proved by case analysis),
  // so the one-hot property is maintained from step 1 onwards.
  Bdd *eff_curr = nullptr;
  if (ok && !*unreal) {
    eff_curr = calloc(m_goals, sizeof *eff_curr);
    if (!eff_curr) {
      ok = false;
    } else {
      Bdd any_curr = oxidd_bdd_false(m);
      for (uint32_t j = 0; j < m_goals && ok; j++) {
        Bdd tmp = oxidd_bdd_or(any_curr, curr_bdd[j]);
        oxidd_bdd_unref(any_curr);
        any_curr = tmp;
        if (bdd_invalid(any_curr))
          ok = false;
      }
      if (ok) {
        Bdd not_any = oxidd_bdd_not(any_curr);
        eff_curr[0] = oxidd_bdd_or(curr_bdd[0], not_any);
        oxidd_bdd_unref(not_any);
        for (uint32_t j = 1; j < m_goals; j++)
          eff_curr[j] = oxidd_bdd_ref(curr_bdd[j]);
        if (bdd_invalid(eff_curr[0]))
          ok = false;
      }
      oxidd_bdd_unref(any_curr);
    }
  }

  if (ok && !*unreal) {
    // W_star image for "any safe move" = cpre_c(W*).
    Bdd w_safe = cpre_unquantified(W, sub_lat, notbad);

    // Build M_total = ⋃_j [eff_curr[j] ∧ M_j].
    Bdd M_total = oxidd_bdd_false(m);

    for (uint32_t j = 0; j < m_goals && ok; j++) {
      Bdd at_goal = oxidd_bdd_and(W, goal_bdd[j]);

      // case_at_goal = at_goal ∧ w_safe
      Bdd case_at_goal = oxidd_bdd_and(at_goal, w_safe);
      Bdd M_j = oxidd_bdd_ref(case_at_goal);
      oxidd_bdd_unref(case_at_goal);

      // covered = at_goal (states already handled by the at-goal case)
      Bdd covered = oxidd_bdd_ref(at_goal);

      for (uint32_t k = 0; k < y_levels[j].n && ok; k++) {
        Bdd yk = y_levels[j].arr[k];

        // layer = Y_k \ covered
        Bdd ncover = oxidd_bdd_not(covered);
        Bdd layer = oxidd_bdd_and(yk, ncover);
        oxidd_bdd_unref(ncover);

        // target = strict ∨ (not_fair ∧ Y_k):
        //   strict = at_goal (rank 0) or Y_{k-1} ∪ at_goal (rank k>0).
        //   The env-unfairness escape (not_fair ∧ Y_k) allows the system to
        //   stay in Y_k when env is currently not satisfying its fairness; the
        //   system is only required to make progress when env is fair.
        Bdd strict;
        if (k == 0) {
          strict = oxidd_bdd_ref(at_goal);
        } else {
          Bdd yk_minus1 = y_levels[j].arr[k - 1];
          strict = oxidd_bdd_or(yk_minus1, at_goal);
        }
        Bdd escape = oxidd_bdd_and(not_fair, yk);
        Bdd target = oxidd_bdd_or(strict, escape);
        oxidd_bdd_unref(strict);
        oxidd_bdd_unref(escape);
        if (bdd_invalid(target)) {
          oxidd_bdd_unref(layer);
          ok = false;
          break;
        }

        Bdd move_k = cpre_unquantified(target, sub_lat, notbad);
        oxidd_bdd_unref(target);

        Bdd case_k = oxidd_bdd_and(layer, move_k);
        oxidd_bdd_unref(layer);
        oxidd_bdd_unref(move_k);

        Bdd new_mj = oxidd_bdd_or(M_j, case_k);
        oxidd_bdd_unref(M_j);
        oxidd_bdd_unref(case_k);
        M_j = new_mj;

        // covered grows to include Y_k
        Bdd new_cov = oxidd_bdd_or(covered, yk);
        oxidd_bdd_unref(covered);
        covered = new_cov;

        if (bdd_invalid(M_j) || bdd_invalid(covered))
          ok = false;
      }

      oxidd_bdd_unref(covered);
      oxidd_bdd_unref(at_goal);

      if (ok) {
        // M_total |= eff_curr[j] ∧ M_j
        Bdd piece = oxidd_bdd_and(eff_curr[j], M_j);
        oxidd_bdd_unref(M_j);
        Bdd new_total = oxidd_bdd_or(M_total, piece);
        oxidd_bdd_unref(M_total);
        oxidd_bdd_unref(piece);
        M_total = new_total;
        if (bdd_invalid(M_total))
          ok = false;
      } else {
        oxidd_bdd_unref(M_j);
      }
    }
    oxidd_bdd_unref(w_safe);

    // Skolem: f_k(s, curr[], u) = ∃(c_{k+1}...) M_total|_{c_k=1}
    if (ok) {
      Bdd R = oxidd_bdd_ref(M_total);
      for (uint32_t k = 0; k < ncv && ok; k++) {
        Bdd pos = oxidd_bdd_var(m, cvars[k]);
        Bdd rk1 = oxidd_bdd_restrict(R, pos);
        Bdd rem = cube_of(m, cvars + k + 1, ncv - k - 1);
        Bdd fk = oxidd_bdd_exists(rk1, rem);
        oxidd_bdd_unref(pos);
        oxidd_bdd_unref(rk1);
        oxidd_bdd_unref(rem);
        if (bdd_invalid(fk)) {
          oxidd_bdd_unref(fk);
          ok = false;
          break;
        }
        strat_f[k] = fk;
        oxidd_bdd_substitution_t *s1 = oxidd_bdd_substitution_new(1);
        oxidd_bdd_substitution_add_pair(s1, cvars[k], fk);
        Bdd rnew = oxidd_bdd_substitute(R, s1);
        oxidd_bdd_substitution_free(s1);
        oxidd_bdd_unref(R);
        R = rnew;
        if (bdd_invalid(R))
          ok = false;
      }
      oxidd_bdd_unref(R);
    }
    oxidd_bdd_unref(M_total);
  }

  // Goal-counter next-functions: next_curr[j] = (eff_curr[j] ∧ ¬advance_j)
  //                                           ∨ (eff_curr[prev] ∧ advance_prev)
  // where advance_j = eff_curr[j] ∧ (W* ∩ goal_j).
  Bdd *next_curr = nullptr;
  if (ok && !*unreal) {
    next_curr = m_goals ? calloc(m_goals, sizeof *next_curr) : nullptr;
    if (!next_curr) {
      ok = false;
    } else {
      Bdd *adv = calloc(m_goals, sizeof *adv);
      if (!adv) {
        ok = false;
      } else {
        for (uint32_t j = 0; j < m_goals && ok; j++) {
          Bdd wg = oxidd_bdd_and(W, goal_bdd[j]);
          adv[j] = oxidd_bdd_and(eff_curr[j], wg);
          oxidd_bdd_unref(wg);
          if (bdd_invalid(adv[j]))
            ok = false;
        }
        if (ok) {
          for (uint32_t j = 0; j < m_goals && ok; j++) {
            uint32_t prev = (j + m_goals - 1) % m_goals;
            Bdd not_adv = oxidd_bdd_not(adv[j]);
            Bdd stay = oxidd_bdd_and(eff_curr[j], not_adv);
            Bdd come = oxidd_bdd_and(eff_curr[prev], adv[prev]);
            Bdd nxt = oxidd_bdd_or(stay, come);
            oxidd_bdd_unref(not_adv);
            oxidd_bdd_unref(stay);
            oxidd_bdd_unref(come);
            next_curr[j] = nxt;
            if (bdd_invalid(nxt))
              ok = false;
          }
        }
        for (uint32_t j = 0; j < m_goals; j++)
          oxidd_bdd_unref(adv[j]);
        free(adv);
      }
    }
  }

  // -----------------------------------------------------------------------
  // Build the strategy AIG.
  // -----------------------------------------------------------------------

  if (ok && !*unreal) {
    strat = aig_new();
    for (uint32_t v = 0; v < nvars; v++)
      var2lit[v] = UINT32_MAX;

    // Uncontrollable inputs.
    for (uint32_t p = 0; p < nin; p++) {
      uint32_t lit;
      const char *name = aig_input_name(game, p, &lit);
      if (!is_controllable(name))
        var2lit[p] = aig_input(strat, name);
    }

    // Game latches (same reset values, next wired below).
    for (uint32_t j = 0; j < nlat; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      lat_lit[j] = aig_latch(strat, AIG_FALSE, reset);
      var2lit[nin + j] = lat_lit[j];
    }

    // Goal-counter latches: all reset to 0; eff_curr[0] handles initial state.
    for (uint32_t j = 0; j < m_goals; j++) {
      curr_latch_lit[j] = aig_latch(strat, AIG_FALSE, 0u);
      var2lit[nin + nlat + j] = curr_latch_lit[j];
    }

    Bdd2Aig ctx = {strat, var2lit, {0}, false};

    // Controllable outputs f_k.
    for (uint32_t k = 0; k < ncv; k++) {
      uint32_t lit;
      const char *name = aig_input_name(game, cinput[k], &lit);
      uint32_t out = bdd2aig(&ctx, strat_f[k]);
      aig_set_output(strat, name, out);
    }

    // Game latch next-functions (Skolem substitution applied).
    oxidd_bdd_substitution_t *sc =
        ncv ? oxidd_bdd_substitution_new(ncv) : nullptr;
    for (uint32_t k = 0; k < ncv; k++)
      oxidd_bdd_substitution_add_pair(sc, cvars[k], strat_f[k]);
    for (uint32_t j = 0; j < nlat && !ctx.error; j++) {
      Bdd na = ncv ? oxidd_bdd_substitute(next_bdd[j], sc)
                   : oxidd_bdd_ref(next_bdd[j]);
      if (bdd_invalid(na)) {
        oxidd_bdd_unref(na);
        ctx.error = true;
        break;
      }
      uint32_t nl = bdd2aig(&ctx, na);
      oxidd_bdd_unref(na);
      aig_set_latch_next(strat, lat_lit[j], nl);
    }
    if (sc)
      oxidd_bdd_substitution_free(sc);

    // Goal-counter latch next-functions.
    for (uint32_t j = 0; j < m_goals && !ctx.error; j++) {
      uint32_t nl = bdd2aig(&ctx, next_curr[j]);
      aig_set_latch_next(strat, curr_latch_lit[j], nl);
    }

    memo_free(&ctx.memo);
    if (ctx.error) {
      aig_free(strat);
      strat = nullptr;
    }
  }

  // -----------------------------------------------------------------------
  // Cleanup.
  // -----------------------------------------------------------------------

  if (next_curr) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(next_curr[j]);
    free(next_curr);
  }
  if (strat_f) {
    for (uint32_t k = 0; k < ncv; k++)
      oxidd_bdd_unref(strat_f[k]);
    free(strat_f);
  }
  if (y_levels) {
    for (uint32_t j = 0; j < m_goals; j++)
      bddvec_free_all(&y_levels[j]);
    free(y_levels);
  }
  if (goal_bdd) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(goal_bdd[j]);
    free(goal_bdd);
  }
  if (fair_bdd) {
    for (uint32_t i = 0; i < m_fair; i++)
      oxidd_bdd_unref(fair_bdd[i]);
    free(fair_bdd);
  }
  if (curr_bdd) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(curr_bdd[j]);
    free(curr_bdd);
  }
  for (uint32_t j = 0; j < nlat; j++)
    oxidd_bdd_unref(next_bdd[j]);
  for (uint32_t v = 0; v <= maxvar; v++)
    oxidd_bdd_unref(var_bdd[v]);
  oxidd_bdd_unref(bad);
  oxidd_bdd_unref(notbad);
  oxidd_bdd_unref(not_fair);
  oxidd_bdd_unref(W);
  oxidd_bdd_unref(ctrl_cube);
  oxidd_bdd_unref(unc_cube);
  if (sub_lat)
    oxidd_bdd_substitution_free(sub_lat);
  oxidd_bdd_manager_unref(m);

  free(var_bdd);
  free(next_bdd);
  free(var2lit);
  free(lat_lit);
  free(curr_latch_lit);
  free(cvars);
  free(uvars);
  free(cinput);
  aig_free(game);
  return strat;
}
