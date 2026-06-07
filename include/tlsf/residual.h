#ifndef TLSF_RESIDUAL_H
#define TLSF_RESIDUAL_H

/// residual.h — shared residual-clustering helpers for the decomposed-synthesis
/// tools (`tlsfresidual`, `tlsfcompose`).  Given the per-constraint substituted
/// formulas of a residual, partition them into output-disjoint clusters
/// (`E -> AND_i Gi == AND_i (E -> Gi)`) and assemble each cluster's LTL.

#include "tlsf/cover.h"
#include "tlsf/templates.h"

#include <stdint.h>
#include <stdio.h>

/// Apply every eliminated-output substitution (`comp->elim`, combinational
/// `o := value`) to `n`, to a fixpoint; returns a node over the remaining APs.
[[nodiscard]] const Node *residual_apply_elims(Arena *a, const Node *n,
                                               const CsnfComposition *comp,
                                               ConstraintCover *cov);

/// Mark every AP occurring in `n` in `seen` (length `cov->aps.count`).
void residual_collect_aps(const Node *n, ConstraintCover *cov, bool *seen);

/// Print the signals in `seen` carrying `flag` (AP_FLAG_INPUT/OUTPUT), CSV.
void residual_print_signals(FILE *out, ConstraintCover *cov, const bool *seen,
                            uint8_t flag);

/// True when AP `idx` belongs in a residual interface list for `flag`.
/// Unflagged APs are treated as environment inputs: they can survive expansion
/// from enum/bus syntax or undeclared legacy atoms, and every AP in a cluster
/// formula must be advertised to the backend as either input or output.
bool residual_signal_matches(ConstraintCover *cov, uint32_t idx, uint8_t flag);

/// Rebuild `spec`'s section lists from the substituted residual formulas `rf`
/// (`rf[i] == nullptr` => skip) belonging to cluster `kk` (or all when `all`),
/// always including the global environment (key == UINT32_MAX), and assemble
/// the cluster's LTL formula.  Fills `seen` with the APs it mentions.  nullptr
/// on OOM.
[[nodiscard]] Node *residual_build_cluster(TlsfSpec *spec, ConstraintCover *cov,
                                           const Node **rf, const uint32_t *key,
                                           uint32_t kk, bool all, uint32_t n,
                                           bool *seen);

/// Cluster `rf[0..n)` by shared output (union-find).  Fills `key[i]` (caller
/// array, length `n`): the output-component root, `cov->aps.count` for an
/// input-only system obligation, or UINT32_MAX for global environment /
/// skipped. Returns the distinct non-global keys in `*keys_out` (malloc'd;
/// caller frees) and their count.
[[nodiscard]] uint32_t residual_cluster_keys(ConstraintCover *cov,
                                             const Node **rf, uint32_t n,
                                             uint32_t *key,
                                             uint32_t **keys_out);

#endif // TLSF_RESIDUAL_H
