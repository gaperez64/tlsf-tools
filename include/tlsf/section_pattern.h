#ifndef TLSF_SECTION_PATTERN_H
#define TLSF_SECTION_PATTERN_H

/// section_pattern.h - section-preserving formula view used before lowering a
/// TLSF spec or residual cluster to one monolithic LTL formula.

#include "tlsf/classify.h"
#include "tlsf/cover.h"
#include "tlsf/spec.h"

#include <stdbool.h>
#include <stdint.h>

typedef struct {
  Role role;
  Node *formula;
  FormulaClass cls;
} SectionPatternEntry;

typedef struct {
  Arena *arena;
  const TlsfSpec *spec;
  SectionPatternEntry *entries;
  uint32_t count;
  uint32_t cap;
} SectionPatternView;

void section_pattern_init(SectionPatternView *v, Arena *a,
                          const TlsfSpec *spec);
bool section_pattern_add(SectionPatternView *v, Role role, Node *formula,
                         FormulaClass cls);
bool section_pattern_add_classified(SectionPatternView *v, Role role,
                                    Node *formula);
bool section_pattern_from_classified(SectionPatternView *v,
                                     const TlsfSpec *spec,
                                     const ClassifiedSpec *cs);

Node *section_pattern_conj(const SectionPatternView *v, Role role);
Node *section_pattern_guarantees(const SectionPatternView *v, bool safety,
                                 bool liveness);
bool section_pattern_role_empty(const SectionPatternView *v, Role role);
int section_pattern_gr_level(const SectionPatternView *v);
Node *section_pattern_to_ltl(const SectionPatternView *v, bool want_safety,
                             bool want_liveness);

#endif // TLSF_SECTION_PATTERN_H
