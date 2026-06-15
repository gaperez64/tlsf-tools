#ifndef TLSF_OXIDD_COMMON_H
#define TLSF_OXIDD_COMMON_H

/// oxidd_common.h — BDD helpers shared by the in-process OxiDD solvers
/// (`safety_oxidd.c` and `gr1_oxidd.c`): the literal/cube builders, the
/// BDD-equality test, and the memoised BDD->AIG ite-expansion.  The games these
/// solvers consume use the same AIGER conventions (env-first / Mealy; inputs
/// named `controllable_*` are controllable moves; output `bad` is the unsafe
/// predicate; latches are state).
///
/// Only compiled when the OxiDD feature is enabled (`HAVE_OXIDD`).

#include "tlsf/aiger.h"

#include <oxidd/capi.h>

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#define CONTROLLABLE_PREFIX "controllable_"

typedef oxidd_bdd_t Bdd;

/// OxiDD returns an invalid handle (`_p == NULL`) on out-of-memory instead of
/// aborting; callers check this before the FFI calls that would panic on it.
static inline bool bdd_invalid(Bdd f) { return f._p == NULL; }

/// True iff `name` is a controllable input (the `controllable_` prefix).
static inline bool is_controllable(const char *name) {
  return strncmp(name, CONTROLLABLE_PREFIX, strlen(CONTROLLABLE_PREFIX)) == 0;
}

/// BDD for AIG literal `lit` (a new reference): 0/1 are the constants,
/// otherwise the stored var-BDD `var_bdd[lit/2]`, complemented when `lit` is
/// odd.
Bdd lit_to_bdd(oxidd_bdd_manager_t m, const Bdd *var_bdd, uint32_t lit);

/// Conjunction of the variables `vars[0..n)` as a cube BDD (⊤ when n == 0).
Bdd cube_of(oxidd_bdd_manager_t m, const uint32_t *vars, uint32_t n);

/// True iff `a` and `b` are the same Boolean function.
bool bdd_eq(Bdd a, Bdd b);

/// BDD-node -> AIG memo (open-addressing hash on the 16-byte handle identity;
/// equal BDD functions share a node, so the handle bytes are a canonical key).
typedef struct {
  Bdd *keys;
  uint32_t *lits;
  bool *used;
  size_t cap, n;
} Memo;

void memo_free(Memo *t);

/// BDD -> AIG (memoised ite expansion over the strategy AIG).
typedef struct {
  Aig *strat;
  const uint32_t *var2lit; // bdd var index (relative to var_base) -> AIG lit
  uint32_t var_base;        // subtract from oxidd_bdd_node_var() before lookup
  Memo memo;
  bool error;
} Bdd2Aig;

/// Expand BDD `f` into and-gates on `ctx->strat`, returning its literal.  Sets
/// `ctx->error` if a variable with no `var2lit` mapping is reached (e.g. a
/// controllable that should have been substituted away) or on allocation
/// failure; subsequent calls are no-ops returning AIG_FALSE.
uint32_t bdd2aig(Bdd2Aig *ctx, Bdd f);

/// Persistent BDD manager session (one per tlsfcompose invocation).
/// When active, the safety and GR(1) solvers reuse this manager across
/// clusters instead of creating a new one per solve call.  Variables
/// accumulate with a per-cluster base offset; BDD nodes are reclaimed by GC
/// after each cluster.  Call oxidd_session_init() before the first solve and
/// oxidd_session_free() after the last.  If the session is never initialised
/// the solvers fall back to per-cluster managers (same as before).
void oxidd_session_init(uint32_t inner_cap, uint32_t cache_cap);
void oxidd_session_free(void);
oxidd_bdd_manager_t oxidd_session_get(void);
/// Allocate `n` new variables in the session manager; returns the base index
/// for this cluster's variables (add to all local var indices 0..n-1).
uint32_t oxidd_session_alloc_vars(uint32_t n);
/// Run a GC pass on the session manager (call after freeing cluster BDDs).
void oxidd_session_gc(void);

#endif // TLSF_OXIDD_COMMON_H
