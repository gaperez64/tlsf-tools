#ifndef TLSF_GRAPH_H
#define TLSF_GRAPH_H

/// graph.h — emit the Graph Structural Normal Form (GSNF) of a constraint
/// cover in several formats.  The graph is a *view* of the cover (constraints,
/// atomic propositions, template candidates and the edges between them); it is
/// rebuilt on demand by the emitters rather than stored.

#include "tlsf/cover.h"
#include <stdio.h>

typedef enum { GFMT_TEXT, GFMT_JSON, GFMT_DOT, GFMT_TSV } GraphFormat;

typedef enum {
  GK_SYNTHESIS,  ///< constraints + AP ownership + dependency/template edges
  GK_CONSTRAINT, ///< constraints + section/role + shared-output edges (no APs)
  GK_FORMULA,    ///< not yet implemented
  GK_QUOTIENT,   ///< not yet implemented
} GraphKind;

typedef struct {
  GraphKind kind;
  bool templates;            ///< include template-candidate info
  bool candidates_only;      ///< emit only template-candidate blocks
  const char *only_template; ///< restrict to one template name (or nullptr)
  bool pretty;               ///< pretty-print JSON
  const bool *selected;      ///< length cov->count; nullptr ⇒ all constraints
} GraphOpts;

/// Emit `cov` as a GSNF graph.  Returns 0 on success, -1 if the requested
/// graph kind is not implemented (caller should report a clear error).
int graph_emit(FILE *out, ConstraintCover *cov, GraphFormat fmt,
               const GraphOpts *o);

#endif // TLSF_GRAPH_H
