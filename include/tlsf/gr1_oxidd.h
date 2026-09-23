#ifndef TLSF_GR1_OXIDD_H
#define TLSF_GR1_OXIDD_H

#include "tlsf/aiger.h"
#include "tlsf/oxidd_common.h"

/// Optional file export requested by tlsfsolve.  The AAG is a combinational
/// circuit over solver state and game inputs; the JSON file is an optional
/// sidecar describing its predicates and variable mapping.  On an export
/// failure `failed` is set and `error` receives a diagnostic.
typedef struct {
  const char *aag_path;
  const char *json_path;
  /// Optional combinational policy export.  Its inputs are game state,
  /// curr_0..curr_(m-1), and uncontrollable inputs; its outputs are the
  /// controllable game inputs and curr_next_0..curr_next_(m-1).
  const char *policy_aag_path;
  const char *policy_json_path;
  bool failed;
  char error[256];
} Gr1CertificateOptions;

/// Solve a GR(1) game encoded in `game` (the standard AbsSynthe AIGER format:
/// controllable inputs prefixed `controllable_`, `bad` output for safety,
/// justice[] for system Büchi goals, fair[] for environment fairness) using the
/// Piterman-Pnueli-Sa'ar tri-nested fixpoint on OxiDD BDDs.
///
/// Ownership: takes and frees `game`.  On win, returns a strategy `Aig` with
/// uncontrollable inputs, the game's latches plus m one-hot goal-counter
/// latches, and each controllable driven by a `controllable_<sig>` output.
/// On loss sets `*unreal = 1` and returns nullptr.  On internal error returns
/// nullptr without setting `*unreal` (caller should fall back).
[[nodiscard]] Aig *solve_gr1_oxidd(Aig *game, int *unreal);

/// Extended entry point used by tlsfsolve after profile resolution.  Takes the
/// same ownership as `solve_gr1_oxidd()`.
[[nodiscard]] Aig *solve_gr1_oxidd_ex(Aig *game, int *unreal,
                                      const OxiddSolveOptions *opts);

/// As `solve_gr1_oxidd`, additionally exporting the final PPS fixpoint and
/// pre-Skolem strategy relations when `certificate` is non-null.
[[nodiscard]] Aig *
solve_gr1_oxidd_with_certificate(Aig *game, int *unreal,
                                 Gr1CertificateOptions *certificate);

/// Combined extended entry point: retain the resolved OxiDD profile and its
/// failure reporting while exporting a certificate.
[[nodiscard]] Aig *
solve_gr1_oxidd_ex_with_certificate(Aig *game, int *unreal,
                                    const OxiddSolveOptions *opts,
                                    Gr1CertificateOptions *certificate);

#endif // TLSF_GR1_OXIDD_H
