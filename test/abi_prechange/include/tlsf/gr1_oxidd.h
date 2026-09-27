#ifndef TLSF_GR1_OXIDD_H
#define TLSF_GR1_OXIDD_H

#include "tlsf/aiger.h"
#include "tlsf/oxidd_options.h"
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/// Optional file export requested by tlsfsolve.  The AAG is a combinational
/// circuit over solver state and game inputs; the JSON file is an optional
/// sidecar describing its predicates and variable mapping.  On an export
/// failure `failed` is set and `error` receives a diagnostic.
typedef enum {
  GR1_CERTIFICATE_SEMANTICS_EXACT,
  GR1_CERTIFICATE_SEMANTICS_STRICT,
} Gr1CertificateSemantics;

typedef struct {
  const char *aag_path;
  const char *json_path;
  /// Optional combinational policy export. Its inputs are game state,
  /// curr_0..curr_(m-1), and uncontrollable inputs; its outputs are the
  /// controllable game inputs and curr_next_0..curr_next_(m-1).
  const char *policy_aag_path;
  const char *policy_json_path;
  /// Semantics of the reduction that produced the game. Strict reductions
  /// are REAL-sound only, so an environment certificate is never exported for
  /// them.
  Gr1CertificateSemantics semantics;
  bool failed;
  char error[256];
  // Optional in-memory export. Each non-null buffer receives a malloc-owned
  // NUL-terminated byte sequence; the caller frees it. Paths may be null.
  char **aag_bytes, **json_bytes, **policy_aag_bytes, **policy_json_bytes;
  size_t *aag_size, *json_size, *policy_aag_size, *policy_json_size;
  size_t max_artifact_bytes; /* 0 = unlimited export */
} Gr1CertificateOptions;

[[nodiscard]] Aig *solve_gr1_oxidd_ex(Aig *game, int *unreal,
                                      const OxiddSolveOptions *opts);
[[nodiscard]] Aig *
solve_gr1_oxidd_ex_with_certificate(Aig *game, int *unreal,
                                    const OxiddSolveOptions *opts,
                                    Gr1CertificateOptions *certificate);

/* Validate the GR(1) AIGER profile before solving. */
bool tlsf_gr1_validate_game(const Aig *game, char *message, size_t capacity);

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

#ifdef __cplusplus
}
#endif

#endif // TLSF_GR1_OXIDD_H
