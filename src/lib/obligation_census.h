#ifndef TLSF_OBLIGATION_CENSUS_H
#define TLSF_OBLIGATION_CENSUS_H

/// obligation_census.h — response/recurrence obligations and the propositional
/// structure that limits how many can be served at once.
///
/// Derived entirely from the candidates recognize.h already produces; this adds
/// no recognition of its own.  Every field is a count over those candidates,
/// and the co-activation fields are candidate evidence rather than certificates
/// -- see the note in obligation_census.c.

#include "tlsf/cover.h"

#include <stdint.h>
#include <stdio.h>

typedef struct {
  uint32_t schema_version;
  uint32_t obligation_count;         ///< response + pure-recurrence candidates
  uint32_t indexed_obligation_count; ///< discharge proposition carries an index
  uint32_t obligation_types;         ///< families under index renaming
  uint32_t max_family_size;
  uint64_t pairwise_exclusion_edges; ///< pairs excluded by some mutex
  uint32_t largest_exclusion_clique; ///< largest single mutex, a lower bound
  uint32_t service_capacity; ///< 1 when an arbiter block fixes it, else 0
  uint32_t arbiter_blocks;
  uint32_t persistent_trigger_count; ///< triggers that are input propositions
  uint64_t coactivation_candidate_count; ///< pairs with distinct input triggers
} ObligationCensus;

/// Fill `out` from a cover that has already been through recognize_all().
void obligation_census(const ConstraintCover *cov, ObligationCensus *out);

void obligation_census_header(FILE *out);
void obligation_census_row(FILE *out, const char *instance,
                           const ObligationCensus *c);

#endif // TLSF_OBLIGATION_CENSUS_H
