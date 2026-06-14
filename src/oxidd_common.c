// oxidd_common.c — BDD helpers shared by safety_oxidd.c and gr1_oxidd.c.
//
// See oxidd_common.h.  Memory: OxiDD operations do not take ownership of their
// `oxidd_bdd_t` arguments and return a *new* reference; every returned handle
// must be `oxidd_bdd_unref`'d (a no-op on the invalid/NULL handle).

#include "tlsf/oxidd_common.h"

#include <stdlib.h>

// ---------------------------------------------------------------------------
// Small BDD helpers
// ---------------------------------------------------------------------------

Bdd lit_to_bdd(oxidd_bdd_manager_t m, const Bdd *var_bdd, uint32_t lit) {
  if (lit == AIG_FALSE)
    return oxidd_bdd_false(m);
  if (lit == AIG_TRUE)
    return oxidd_bdd_true(m);
  Bdd base = var_bdd[lit / 2];
  return (lit & 1u) ? oxidd_bdd_not(base) : oxidd_bdd_ref(base);
}

Bdd cube_of(oxidd_bdd_manager_t m, const uint32_t *vars, uint32_t n) {
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

bool bdd_eq(Bdd a, Bdd b) {
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
// BDD node -> AIG memo (open-addressing hash on the 16-byte handle identity)
// ---------------------------------------------------------------------------

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

// Returns true and sets *lit if `k` is memoised; otherwise returns false.
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
  if (t->n * 10 >= t->cap * 7) // grow at load factor 0.7
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

void memo_free(Memo *t) {
  free(t->keys);
  free(t->lits);
  free(t->used);
  *t = (Memo){0};
}

// ---------------------------------------------------------------------------
// BDD -> AIG (memoised ite expansion over the strategy AIG)
// ---------------------------------------------------------------------------

uint32_t bdd2aig(Bdd2Aig *ctx, Bdd f) {
  if (ctx->error)
    return AIG_FALSE;
  if (oxidd_bdd_node_level(f) == (oxidd_level_no_t)-1) // terminal
    return oxidd_bdd_satisfiable(f) ? AIG_TRUE : AIG_FALSE;
  uint32_t cached;
  if (memo_get(&ctx->memo, f, &cached))
    return cached;
  oxidd_var_no_t v = oxidd_bdd_node_var(f);
  uint32_t vlit = ctx->var2lit[v];
  if (vlit ==
      UINT32_MAX) { // a variable that must not appear (e.g. controllable)
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
