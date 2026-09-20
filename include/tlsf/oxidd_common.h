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
#include <stdio.h>

#define CONTROLLABLE_PREFIX "controllable_"

typedef oxidd_bdd_t Bdd;

typedef enum {
  OXIDD_GC_AUTO = 0,
  OXIDD_GC_PRESSURE = 1,
} OxiddGcMode;

typedef enum {
  OXIDD_SAFETY_OBJECTIVE_OUTPUT = 0,
  OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR = 1,
} OxiddSafetyObjective;

typedef enum {
  OXIDD_FAILURE_NONE,
  OXIDD_FAILURE_BDD,
  OXIDD_FAILURE_HOST,
  OXIDD_FAILURE_CONFIGURATION,
  OXIDD_FAILURE_CONVERSION,
  OXIDD_FAILURE_INVALID
} OxiddFailureKind;

typedef struct {
  OxiddFailureKind kind;
  const char *phase, *operation;
  size_t operation_id;
  uint32_t index;
} OxiddFailure;

typedef struct {
  size_t node_cap;  // 0 = legacy heuristic default
  size_t cache_cap; // 0 = legacy heuristic default
  OxiddGcMode gc_mode;
  unsigned gc_threshold_percent;
  unsigned verbosity;
  FILE *trace;
  OxiddSafetyObjective safety_objective;
  uint32_t safety_output_index;
  OxiddFailure *failure; // optional caller-owned output; never a losing verdict
  bool demand_transitions, realizability_only;
} OxiddSolveOptions;

OxiddSolveOptions oxidd_solve_options_default(void);
size_t oxidd_default_capacity(uint32_t local_vars, uint32_t extra_exp);
typedef struct {
  oxidd_bdd_manager_t manager;
  const OxiddSolveOptions *options;
  const char *phase, *failed_operation;
  size_t node_cap, cache_cap, sampled_peak, operations, next_gc;
  size_t retries, recovered, explicit_gc, built_gates, relevant_gates;
  uint32_t index;
  double phase_started;
} OxiddRun;

void oxidd_run_init(OxiddRun *run, oxidd_bdd_manager_t manager,
                    const OxiddSolveOptions *options, size_t nodes,
                    size_t cache);
void oxidd_phase(OxiddRun *run, const char *phase);
bool oxidd_pressure_gc_checkpoint(OxiddRun *run);
void oxidd_run_finish(OxiddRun *run);
void oxidd_record_failure(const OxiddSolveOptions *opts, OxiddFailureKind kind,
                          const char *phase, const char *operation,
                          size_t operation_id, uint32_t index);
Bdd oxidd_run_not(OxiddRun *run, Bdd a);
Bdd oxidd_run_var(OxiddRun *run, uint32_t var);
Bdd oxidd_run_and(OxiddRun *run, Bdd a, Bdd b);
Bdd oxidd_run_or(OxiddRun *run, Bdd a, Bdd b);
Bdd oxidd_run_exists(OxiddRun *run, Bdd a, Bdd b);
Bdd oxidd_run_forall(OxiddRun *run, Bdd a, Bdd b);
Bdd oxidd_run_restrict(OxiddRun *run, Bdd a, Bdd b);
Bdd oxidd_run_substitute(OxiddRun *run, Bdd a,
                         const oxidd_bdd_substitution_t *sub);
Bdd oxidd_run_apply_exists(OxiddRun *run, oxidd_boolean_operator op, Bdd a,
                           Bdd b, Bdd vars);
Bdd oxidd_run_cube(OxiddRun *run, const uint32_t *vars, uint32_t n);

// Consumes map entries as their final consumers finish. On failure, both map
// and roots remain caller-owned and may contain partially constructed results.
bool oxidd_build_roots(OxiddRun *run, const Aig *game, Bdd *map,
                       uint32_t maxvar, const uint32_t *lits, Bdd *roots,
                       size_t count);
bool oxidd_build_game(OxiddRun *run, const Aig *game, Bdd *map, uint32_t maxvar,
                      Bdd *bad, Bdd *next, Bdd *goals, Bdd *fair);
bool oxidd_state_support(Bdd root, uint32_t base, uint32_t count,
                         bool *support);
void oxidd_trace(const OxiddSolveOptions *opts, const char *phase,
                 const char *event, const char *fmt, ...);

/// OxiDD returns an invalid handle (`_p == NULL`) on out-of-memory instead of
/// aborting; callers check this before the FFI calls that would panic on it.
static inline bool bdd_invalid(Bdd f) { return f._p == NULL; }

/// True iff `name` is a controllable input (the `controllable_` prefix).
static inline bool is_controllable(const char *name) {
  if (!name)
    return false;
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
bool bdd_same_identity(Bdd a, Bdd b);

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
  uint32_t var_base;       // subtract from oxidd_bdd_node_var() before lookup
  uint32_t var_count;      // number of valid `var2lit` entries
  Memo memo;
  bool error;
} Bdd2Aig;

/// Expand BDD `f` into and-gates on `ctx->strat`, returning its literal.  Sets
/// `ctx->error` if a variable with no `var2lit` mapping is reached (e.g. a
/// controllable that should have been substituted away) or on allocation
/// failure; subsequent calls are no-ops returning AIG_FALSE.
uint32_t bdd2aig(Bdd2Aig *ctx, Bdd f);
uint32_t bdd2aig_root(Bdd2Aig *ctx, Bdd f);

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
bool oxidd_session_config(const OxiddSolveOptions *opts, size_t *nodes,
                          size_t *cache);
/// Allocate `n` new variables in the session manager; returns the base index
/// for this cluster's variables (add to all local var indices 0..n-1).
uint32_t oxidd_session_alloc_vars(uint32_t n);
/// Run a GC pass on the session manager (call after freeing cluster BDDs).
void oxidd_session_gc(void);

#endif // TLSF_OXIDD_COMMON_H
