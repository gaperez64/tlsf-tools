#ifndef TLSF_COMPOSE_INTERNAL_H
#define TLSF_COMPOSE_INTERNAL_H

/// compose_internal.h — shared declarations for the tlsfcompose decomposition
/// diagnostics, split across:
///   * compose_analysis.c - pure AST/arena cluster analysis (eligibility gates,
///     x-depth, W/R + GR(1) decomposition, cluster-shape classification);
///   * compose_games.c - `Aig` game builders (direct, W/R, strict-safety,
///     unbounded GR(1)) and structural helpers reused by route stats.
///   * compose_oxidd.c - exact OxiDD residual-cluster pre-solving for
///     output-dir plans.
/// main_tlsfcompose.c keeps CLI parsing and plan emission in `main`.
///
/// Internal to the tlsfcompose executable; not part of libtlsf's public API.
/// Only compiled when the OxiDD feature is enabled (`HAVE_OXIDD`).

#include "tlsf/aiger.h"
#include "tlsf/arena.h"
#include "tlsf/ast.h"
#include "tlsf/cover.h"
#include "tlsf/print_ltlxba.h" // LtlFormat
#include "tlsf/spec.h"

#include <stdbool.h>
#include <stdint.h>

#define AIG_CONTROLLABLE_PREFIX "controllable_"

// ---- GR(1): `G F a` fairness assumptions + recurrence/response justice ----

#define GR1_MAX_JUSTICE 32
#define GR1_MAX_FAIRNESS 32
#define GR1_MAX_WEAK 64

typedef enum {
  GR1_JUSTICE_RECURRENCE,
  GR1_JUSTICE_RESPONSE,
  GR1_JUSTICE_EVENTUAL,
} Gr1JusticeKind;

typedef struct {
  const Node *req;    // nullptr for a recurrence `G F target`
  const Node *target; // recurrence goal `g`, or response grant
  Gr1JusticeKind kind;
} Gr1Justice;

typedef struct {
  const Node *a, *b; // a weak-until guarantee `a W b` (a safety property)
} Gr1WeakUntil;

typedef struct {
  const Node *fairness[GR1_MAX_FAIRNESS]; // the `a`s in the `G F a` assumptions
  uint32_t nfairness;
  const Node *env_init;      // env initial assumption (Boolean, TRUE if none)
  const Node *sys_init;      // sys initial guarantee (Boolean, TRUE if none)
  const Node *safety_assume; // AND of safety assume conjuncts (TRUE if none)
  const Node *safety_gua;    // AND of safety guarantee conjuncts (TRUE if none)
  Gr1Justice justice[GR1_MAX_JUSTICE];
  uint32_t njustice;
  Gr1WeakUntil weak[GR1_MAX_WEAK]; // guarantee-side `a W b` safety monitors
  uint32_t nweak;
} Gr1Parts;

typedef struct {
  int gr_level;
  bool has_liveness;
  bool has_weak_until;
  bool has_release;
  bool has_strong_next;
  bool has_high_level;
} ClusterShape;

// ---- compose_analysis.c ---------------------------------------------------

bool aig_body_ok(const Node *n);
bool aig_initial_ok(const Node *n);
bool aig_initial_x_ok(const Node *n);
uint32_t aig_x_depth(const Node *n);
uint32_t aig_safety_cond_x_depth(const Node *n);
uint32_t aig_global_x_depth(const Node *n);
bool wr_response_parts(const Node *impl, const Node **req, const Node **inner,
                       bool *xdelay);
bool g_body_wr_supported(const Node *n);
bool aig_safety_wr_ok(const Node *n);
uint32_t aig_safety_wr_x_depth(const Node *n);
bool wr_has_initial(const Node *n);
bool wr_has_x_initial(const Node *n);
bool wr_has_delayed_global(const Node *n);
bool wr_has_bare_wr(const Node *n);
bool aig_eligible(const Node *root, bool finite);
bool aig_strict_safety_parts(const Node *root, const Node **sys,
                             const Node **env);
bool aig_response_monitor_parts(Arena *a, const Node *root, Gr1Parts *p);
bool aig_eventual_monitor_parts(TlsfSpec *spec, const Node *root, Gr1Parts *p);
bool aig_until_monitor_parts(TlsfSpec *spec, const Node *root, Gr1Parts *p);
bool aig_gr1_parts(Arena *a, const Node *root, Gr1Parts *p);
Node *bound_liveness(Arena *a, const Node *n, uint32_t k, bool pos);
ClusterShape cluster_shape(TlsfSpec *spec, const Node *root);
const char *cluster_ltlsynt_reason(const ClusterShape *shape, bool finite,
                                   char *buf, size_t buf_sz);

// ---- compose_games.c ------------------------------------------------------

[[nodiscard]] Aig *build_aig_game(ConstraintCover *cov, const bool *seen,
                                  const Node *root);
[[nodiscard]] Aig *build_aig_wr_game(ConstraintCover *cov, const bool *seen,
                                     const Node *root);
[[nodiscard]] Aig *build_aig_strict_safety_game(ConstraintCover *cov,
                                                const bool *seen,
                                                const Node *sys,
                                                const Node *env);
[[nodiscard]] Aig *
build_aig_tlsf_strict_safety_game(ConstraintCover *cov, const bool *seen,
                                  const Node *env_init, const Node *env_require,
                                  const Node *sys_init, const Node *sys_assert);
[[nodiscard]] Aig *build_aig_gr1_game(ConstraintCover *cov, const bool *seen,
                                      const Gr1Parts *parts);
bool wr_structural_supported(const Node *n);

// ---- compose_oxidd.c / oxidd_common.c ------------------------------------

// Persistent BDD manager session: call init before the cluster loop, free
// after.  Both are no-ops when the OxiDD build is not active.
void oxidd_session_init(uint32_t inner_cap, uint32_t cache_cap);
void oxidd_session_free(void);

#endif // TLSF_COMPOSE_INTERNAL_H
