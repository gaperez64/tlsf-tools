#ifndef TLSF_WL_H
#define TLSF_WL_H

/// wl.h — Weisfeiler-Lehman color refinement over the GSNF graph.
///
/// WL is a structural fingerprint of a spec's synthesis graph: a multiset of
/// "colors" (refined neighbourhood signatures) that can be compared across
/// graphs.  It is a *similarity heuristic, never a proof* — it suggests which
/// specs/templates are alike; it does not certify anything.
///
/// Colors are rendered as stable strings (round-0 = readable initial label,
/// later rounds = a fixed FNV-1a-64 hash hex), so the same structural
/// neighbourhood yields the same color in any graph.  Features are a histogram
/// over rounds 0..N, keyed "<round>:<color>", malloc-backed so many graphs'
/// features can coexist for pairwise comparison.

#include "tlsf/cover.h"
#include <stdio.h>

typedef enum {
  WL_BASIC,     ///< node kind only
  WL_SYNTHESIS, ///< + AP ownership and constraint role/class (default)
  WL_TEMPLATE,  ///< + template-candidate names
} WlLabels;

typedef enum { KERNEL_DOT, KERNEL_COSINE, KERNEL_JACCARD } Kernel;

typedef struct WlFeatures WlFeatures;

/// Compute WL features (depth `rounds`) of the cover's GSNF graph.
/// Returns a malloc-backed object; free with wl_features_free.  nullptr on OOM.
[[nodiscard]] WlFeatures *wl_compute(const ConstraintCover *cov, int rounds,
                                     WlLabels labels);
void wl_features_free(WlFeatures *f);

/// Emit the histogram as `c`/`p wl`/`v <count> <key>` lines.
void wl_features_emit(FILE *out, const WlFeatures *f, const char *source);

/// Similarity of two feature histograms under the chosen kernel (cosine and
/// weighted-Jaccard are in [0,1]; dot is the raw inner product).
double wl_kernel(const WlFeatures *a, const WlFeatures *b, Kernel k);

#endif // TLSF_WL_H
