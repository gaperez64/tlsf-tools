#ifndef TLSF_NORMALIZE_H
#define TLSF_NORMALIZE_H

/// normalize.h — shared, observable, equivalence-preserving normalization.
///
/// This is the single library all tools call to normalize LTL formulas before
/// exact template recognition (`match`), residual routing (`route`), or
/// user-visible re-emission (`visible`).  High-level (pre-expansion) passes are
/// applied through `tlsf_prenorm_spec` (see below); post-expansion passes are
/// applied through `tlsf_normalize_formula`.
///
/// Design rules (see docs/handoff):
///   - Every rule constructs an *equivalent* AST; recognizers then parse exact
///     shapes.  No fuzzy/similarity matching lives here.
///   - Every rule carries soundness metadata (finite/infinite-word, allowed
///     phases, growth).  Schedules requesting a rule in a disallowed phase or
///     on the wrong word semantics are rejected.
///   - Rewrites that exceed growth/node caps are rejected: the original formula
///     is returned for that step and a rejection counter is incremented.
///   - Everything is observable: per-pass and per-rule attempt/fire/reject
///     counters, node deltas, time, and an optional per-step trace.

#include "tlsf/arena.h"
#include "tlsf/ast.h"

#include <stdint.h>
#include <stdio.h>

// ---------------------------------------------------------------------------
// Phases, passes, rules
// ---------------------------------------------------------------------------

typedef enum {
  TLSF_NORM_PHASE_PRE_EXPAND, ///< high-level TLSF AST, before expand()
  TLSF_NORM_PHASE_MATCH,      ///< post-expansion, for exact recognition
  TLSF_NORM_PHASE_ROUTE,      ///< residual/routing eligibility
  TLSF_NORM_PHASE_VISIBLE,    ///< tlsfnorm user-visible output
  TLSF_NORM_PHASE_BENCH,      ///< structural benchmarking
  TLSF_NORM_PHASE_COUNT,
} TlsfNormPhase;

typedef enum {
  TLSF_NORM_PASS_SPLIT, ///< list-level: decompose top-level && (G/X spine)
  TLSF_NORM_PASS_NNF,
  TLSF_NORM_PASS_WEAK, ///< weak simplification (syfco -s0)
  TLSF_NORM_PASS_BOOL_CANON,
  TLSF_NORM_PASS_OR_TO_IMPL_PATTERN,
  TLSF_NORM_PASS_EQUIV_OUTPUT_SIDE,
  TLSF_NORM_PASS_MUTEX_DEMORGAN,
  TLSF_NORM_PASS_ROUTE_SAFE,
  TLSF_NORM_PASS_SICKERT_STAGE2,
  TLSF_NORM_PASS_SICKERT_STAGE3,
  TLSF_NORM_PASS_PRE_INDEXED_X,
  TLSF_NORM_PASS_PRE_BOUNDED_BOOL,
  TLSF_NORM_PASS_PRE_SPINE_SPLIT,
  TLSF_NORM_PASS_PRE_WEAK,
  TLSF_NORM_PASS_COUNT,
} TlsfNormPass;

typedef enum {
  TLSF_NORM_RULE_WEAK_DOUBLE_NEG,
  TLSF_NORM_RULE_WEAK_CONST_FOLD,
  TLSF_NORM_RULE_WEAK_IDEMPOTENT,
  TLSF_NORM_RULE_BOOL_FLATTEN_AND,
  TLSF_NORM_RULE_BOOL_FLATTEN_OR,
  TLSF_NORM_RULE_BOOL_SORT_AND,
  TLSF_NORM_RULE_BOOL_SORT_OR,
  TLSF_NORM_RULE_OR_TO_RESPONSE_IMPL,
  TLSF_NORM_RULE_OR_TO_GUARDED_NEXT_IMPL,
  TLSF_NORM_RULE_EQUIV_OUTPUT_LEFT,
  TLSF_NORM_RULE_MUTEX_DEMORGAN_PAIR,
  TLSF_NORM_RULE_ROUTE_NNF,
  TLSF_NORM_RULE_ROUTE_PUSH_G_IN,
  TLSF_NORM_RULE_ROUTE_PUSH_X_IN,
  TLSF_NORM_RULE_SICKERT_LIMIT_LIFT,
  TLSF_NORM_RULE_SICKERT_GF_W,
  TLSF_NORM_RULE_SICKERT_FG_U,
  TLSF_NORM_RULE_PRE_X0,
  TLSF_NORM_RULE_PRE_XN_FLATTEN,
  TLSF_NORM_RULE_PRE_XN_BOOL_DISTRIBUTE,
  TLSF_NORM_RULE_PRE_BOUNDED_SINGLETON,
  TLSF_NORM_RULE_PRE_BOUNDED_EMPTY,
  TLSF_NORM_RULE_PRE_BOUNDED_CONST_FOLD,
  TLSF_NORM_RULE_PRE_SPINE_SPLIT,
  TLSF_NORM_RULE_PRE_WEAK,
  TLSF_NORM_RULE_COUNT,
} TlsfNormRule;

typedef enum {
  TLSF_NORM_REJECT_NONE,
  TLSF_NORM_REJECT_GROWTH,
  TLSF_NORM_REJECT_NODES,
  TLSF_NORM_REJECT_FINITE_WORD,
  TLSF_NORM_REJECT_PHASE,
  TLSF_NORM_REJECT_NOT_APPLICABLE,
} TlsfNormRejectReason;

// ---------------------------------------------------------------------------
// Rule soundness metadata
// ---------------------------------------------------------------------------

typedef struct {
  TlsfNormRule rule;
  const char *name;
  bool equivalence_infinite;
  bool equivalence_finite;
  bool allowed_pre_expand;
  bool allowed_match;
  bool allowed_route;
  bool allowed_visible;
  bool may_increase_nodes;
  uint32_t default_growth_cap_percent;
  const char *proof_note;
} TlsfNormRuleInfo;

const TlsfNormRuleInfo *tlsf_norm_rule_info(TlsfNormRule r);

// ---------------------------------------------------------------------------
// Schedules
// ---------------------------------------------------------------------------

typedef struct {
  TlsfNormPass pass;
  uint32_t max_iter; ///< schedule-level iterations (0 -> 1)
} TlsfNormPassSpec;

typedef struct {
  TlsfNormPassSpec *items;
  uint32_t count;
} TlsfNormSchedule;

/// Parse a schedule string ("match-safe:2,route-safe" / "pre-safe" / "off").
/// Profile names expand to pass lists; a trailing ":N" on a profile repeats its
/// block N times.  Allocates `out->items` from `a`.  Returns false (and writes
/// a message to stderr via `tool`) on a syntax error.
bool tlsf_norm_parse_schedule(Arena *a, const char *s, const char *tool,
                              TlsfNormSchedule *out);

/// Canonical, comma-joined string form of a parsed schedule (arena-allocated).
const char *tlsf_norm_schedule_string(Arena *a, const TlsfNormSchedule *sch);

/// True if `sch` contains a pass that only operates before expand().
bool tlsf_norm_schedule_is_pre(const TlsfNormSchedule *sch);
/// True if `sch` contains a post-expansion pass.
bool tlsf_norm_schedule_is_post(const TlsfNormSchedule *sch);

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

typedef struct {
  uint64_t attempts;
  uint64_t fired;
  uint64_t noops;
  uint64_t rejected_growth;
  uint64_t rejected_nodes;
  uint64_t rejected_finite_word;
  uint64_t rejected_not_applicable;
  uint64_t nodes_before_sum;
  uint64_t nodes_after_sum;
  uint64_t time_ns;
} TlsfNormRuleStats;

typedef struct {
  TlsfNormPhase phase;
  const char *schedule; ///< normalized string form (arena/static)
  uint32_t formulas_seen;
  uint32_t formulas_changed;
  uint32_t formulas_rejected;
  uint32_t iterations_total;
  uint64_t nodes_before;
  uint64_t nodes_after;
  uint64_t nodes_max_before;
  uint64_t nodes_max_after;
  uint64_t time_ns;

  // Sickert obstacle counters before/after (PR8).
  uint64_t u_under_w_before, u_under_w_after;
  uint64_t limit_under_temporal_before, limit_under_temporal_after;
  uint64_t w_under_gf_before, w_under_gf_after;
  uint64_t u_under_fg_before, u_under_fg_after;

  // Route classification counters before/after.
  uint64_t safety_before, safety_after;
  uint64_t liveness_before, liveness_after;

  TlsfNormRuleStats rules[TLSF_NORM_RULE_COUNT];
} TlsfNormStats;

void tlsf_norm_stats_init(TlsfNormStats *s, TlsfNormPhase phase,
                          const char *schedule);
void tlsf_norm_stats_print_human(FILE *out, const TlsfNormStats *s);
void tlsf_norm_stats_print_tsv_header(FILE *out);
void tlsf_norm_stats_print_tsv_row(FILE *out, const TlsfNormStats *s);

const char *tlsf_norm_pass_name(TlsfNormPass p);
const char *tlsf_norm_rule_name(TlsfNormRule r);
const char *tlsf_norm_phase_name(TlsfNormPhase p);
const char *tlsf_norm_reject_name(TlsfNormRejectReason r);

// ---------------------------------------------------------------------------
// Sickert-style normalization obstacles (PR8): structural indicators of where
// a Sickert-style rewrite would have to fire.  `GF x` is G(F x); `FG x` is
// F(G x); temporal nodes are X/U/W/R/M/F/G (and GF/FG limit nodes).  Counts
// node occurrences and ADDS to `*out` (caller zero-initializes).
// ---------------------------------------------------------------------------

typedef struct {
  uint64_t u_under_w;            ///< U strictly under a W
  uint64_t limit_under_temporal; ///< GF/FG limit node under a temporal node
  uint64_t w_under_gf;           ///< W inside the body of a GF
  uint64_t u_under_fg;           ///< U inside the body of an FG
} TlsfObstacles;

void tlsf_norm_count_obstacles(const Node *n, TlsfObstacles *out);

// ---------------------------------------------------------------------------
// Options + entry points
// ---------------------------------------------------------------------------

typedef struct {
  TlsfNormSchedule schedule;
  TlsfNormPhase phase;
  uint32_t max_iter_default;   ///< default schedule-level iter cap (default 32)
  uint32_t max_growth_percent; ///< per-step growth cap vs input (default 200)
  uint32_t max_nodes;          ///< absolute node cap (default 20000; 0 = none)
  bool finite_word;            ///< spec uses finite-word semantics
  bool record_stats;
  bool soundness_assert; ///< reject rules not safe for the phase/semantics
  FILE *trace;           ///< NULL means no per-step trace
  const char *trace_file;
  const char *trace_constraint; ///< label for trace rows (may be NULL)
  const char *trace_role;
} TlsfNormOptions;

void tlsf_norm_options_default(TlsfNormOptions *opts, TlsfNormPhase phase);

/// Check that every rule reachable from `opts->schedule` is allowed in
/// `opts->phase` and (when finite_word) finite-safe.  On violation, writes a
/// message to stderr via `tool`, fills `*reason`, and returns false.
bool tlsf_norm_schedule_check(const TlsfNormSchedule *sch,
                              const TlsfNormOptions *opts, const char *tool,
                              TlsfNormRejectReason *reason);

/// Apply `opts->schedule` to a single (post-expansion) formula and return the
/// normalized, equivalent AST (arena-allocated).  List-altering passes (split)
/// are no-ops here.  Never returns NULL for a non-NULL input (falls back to the
/// input on cap rejection).  `stats` may be NULL.
[[nodiscard]] Node *tlsf_normalize_formula(Arena *a, Node *root,
                                           const TlsfNormOptions *opts,
                                           TlsfNormStats *stats);

/// Pre-expansion spine split (high-level analog of rewrite_decompose): splits
/// top-level &&, distributing G / X / X[k] over && along the spine only. Writes
/// an arena array of conjuncts to `*out` and returns the count (>= 1).
[[nodiscard]] uint32_t tlsf_prenorm_spine_split(Arena *a, Node *f, Node ***out);

// Forward declaration; full definition in spec.h (pulled in by .c users).
typedef struct TlsfSpec TlsfSpec;

/// Apply `opts->schedule` (pre-expansion passes) to every section formula of
/// `spec`, before expand().  No-op when the schedule is empty.
bool tlsf_prenorm_spec(TlsfSpec *spec, const TlsfNormOptions *opts,
                       TlsfNormStats *stats);

#endif // TLSF_NORMALIZE_H
