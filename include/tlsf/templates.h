#ifndef TLSF_TEMPLATES_H
#define TLSF_TEMPLATES_H

/// templates.h — move recognized template *candidates* (GSNF) to *certified* /
/// *solved* blocks (CSNF).  A block is only SOLVED when a sound side condition
/// passes and a controller/decoder + certificate is produced; otherwise it
/// stays CANDIDATE (or, for a standalone mutex, CERTIFIED as a safety
/// invariant).  Nothing is removed from the problem here (residual is M6).
///
/// Side conditions are *syntactic and conservative*: they may decline to
/// certify a solvable block, but never certify an unsound one.

#include "tlsf/cover.h"
#include <stdio.h>

typedef enum {
  CSNF_CANDIDATE, ///< recognized, not certified
  CSNF_CERTIFIED, ///< side condition checked + certificate (e.g. mutex safety)
  CSNF_SOLVED,    ///< certified and a controller/decoder produces its outputs
} CsnfStatus;

typedef struct Csnf Csnf;

/// Certify the cover's templates.  `want` is a bitmask of TPL_* (0 = all).  If
/// `certify` is false every block is left CANDIDATE (the `--candidates` view).
/// Returns a malloc-backed model; free with csnf_free.  nullptr on OOM.
enum {
  TPL_DEFINITION = 1u << 0,
  TPL_ROUND_ROBIN = 1u << 1,
  TPL_GUARDED_NEXT = 1u << 2,
  TPL_MUTEX = 1u << 3,
  TPL_ARBITER = 1u << 4,
  TPL_RESPONSE = 1u << 5,
  TPL_PERSISTENCE = 1u << 6,
  TPL_REACHABILITY = 1u << 7,
  TPL_REACTION = 1u << 8,
  TPL_DELAYED_DEF = 1u << 9,
  TPL_ALL = 0,
};

[[nodiscard]] Csnf *templates_certify(ConstraintCover *cov, unsigned want,
                                      bool certify);
void csnf_free(Csnf *c);

/// Emit the model: `text` is human-readable, `csnf` is the DIMACS-style line
/// format (see README).
void csnf_emit_text(FILE *out, const Csnf *c, bool solve);
void csnf_emit_lines(FILE *out, const Csnf *c, const char *source, bool solve);

/// Tally block statuses and derived counts (any out-pointer may be nullptr).
/// `dependent` counts SOLVED definition decoders; `residual` counts
/// constraints not in any SOLVED block.
void csnf_counts(const Csnf *c, uint32_t *solved, uint32_t *certified,
                 uint32_t *candidate, uint32_t *residual, uint32_t *dependent);

/// The template names recognized so far (for --list-templates).
extern const char *const TEMPLATE_NAMES[];
extern const int TEMPLATE_NAMES_COUNT;

#endif // TLSF_TEMPLATES_H
