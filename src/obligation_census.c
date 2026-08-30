/// obligation_census.c — export the response/recurrence obligations a spec
/// carries, and the propositional structure that decides how many of them can
/// be served at once.
///
/// This adds no recognition.  recognize.h already matches response
/// `G(r -> F g)`, pure recurrence `G F x`, mutex `G(!(a && b) ...)` and the
/// multi-constraint arbiter block; this walks the resulting candidates and
/// reports them in a stable schema.  The consumer is a solver-side study of
/// when a bounded-rank game's frontier explodes, which needs the specification
/// view because flattening to one LTL implication loses the indexed-family
/// provenance the count depends on.
///
/// Nothing here is a certificate.  A "co-live" obligation pair is a pair whose
/// triggers are distinct input propositions, which is evidence that they *can*
/// be pending together, not proof that they ever are.

#include "tlsf/obligation_census.h"

#include "tlsf/apset.h"
#include "tlsf/cover.h"

#include <stdlib.h>
#include <string.h>

enum { CENSUS_SCHEMA_VERSION = 1 };

/// Split a mangled AP name into its family prefix and index.  Expanded TLSF
/// bus signals arrive as `grant_3` or `grant3`; the family is what remains once
/// a trailing digit run and one optional separator are removed.  Returns the
/// prefix length, and sets *has_index.
static size_t family_prefix(const char *name, bool *has_index) {
  size_t n = strlen(name);
  size_t end = n;
  while (end > 0 && name[end - 1] >= '0' && name[end - 1] <= '9')
    end--;
  *has_index = (end < n);
  if (!*has_index)
    return n;
  if (end > 0 && (name[end - 1] == '_' || name[end - 1] == '.'))
    end--;
  return end;
}

static bool same_family(const ApTable *aps, int32_t a, int32_t b) {
  if (a < 0 || b < 0)
    return false;
  const char *na = ap_table_name(aps, (uint32_t)a);
  const char *nb = ap_table_name(aps, (uint32_t)b);
  bool ia, ib;
  size_t la = family_prefix(na, &ia);
  size_t lb = family_prefix(nb, &ib);
  return la == lb && strncmp(na, nb, la) == 0;
}

typedef struct {
  int32_t trigger; ///< -1 for an unconditional recurrence
  int32_t target;
} Obligation;

void obligation_census(const ConstraintCover *cov, ObligationCensus *out) {
  memset(out, 0, sizeof *out);
  out->schema_version = CENSUS_SCHEMA_VERSION;

  const ApTable *aps = &cov->aps;
  uint32_t cap = cov->template_candidate_count;
  Obligation *obs = cap ? calloc(cap, sizeof *obs) : nullptr;
  if (cap && !obs)
    return;
  uint32_t n = 0;

  for (uint32_t i = 0; i < cov->template_candidate_count; i++) {
    const TemplateCandidate *c = &cov->template_candidates[i];
    switch (c->kind) {
    case CAND_RESPONSE:
      obs[n].trigger = c->u.response.guard;
      obs[n].target = c->u.response.target;
      n++;
      break;
    case CAND_RECURRENCE:
      obs[n].trigger = -1;
      obs[n].target = c->u.recurrence.output;
      n++;
      break;
    case CAND_MUTEX: {
      // A mutex over m propositions excludes every pair, and is itself a
      // clique of that size in the exclusion graph.
      uint32_t m = apset_count(&c->u.mutex.members);
      out->pairwise_exclusion_edges += (uint64_t)m * (m - 1) / 2;
      if (m > out->largest_exclusion_clique)
        out->largest_exclusion_clique = m;
      break;
    }
    default:
      break;
    }
  }

  out->obligation_count = n;

  // Families, under index renaming of the discharge proposition.  An obligation
  // whose target carries no index is its own family.
  for (uint32_t i = 0; i < n; i++) {
    bool indexed = false;
    if (obs[i].target >= 0)
      (void)family_prefix(ap_table_name(aps, (uint32_t)obs[i].target),
                          &indexed);
    if (indexed)
      out->indexed_obligation_count++;

    bool seen = false;
    for (uint32_t j = 0; j < i; j++)
      if (same_family(aps, obs[i].target, obs[j].target)) {
        seen = true;
        break;
      }
    if (!seen) {
      out->obligation_types++;
      uint32_t size = 0;
      for (uint32_t j = 0; j < n; j++)
        if (same_family(aps, obs[i].target, obs[j].target))
          size++;
      if (size > out->max_family_size)
        out->max_family_size = size;
    }

    // Candidate evidence only.  A trigger that is an input proposition is one
    // the environment can hold up while other obligations accumulate; this does
    // not establish that it ever does.
    if (obs[i].trigger >= 0 &&
        (ap_table_flags(aps, (uint32_t)obs[i].trigger) & AP_FLAG_INPUT))
      out->persistent_trigger_count++;
  }

  // Two obligations are co-activation candidates when their triggers are
  // distinct input propositions: nothing in the propositional structure stops
  // the environment asserting both in the same step.
  for (uint32_t i = 0; i < n; i++)
    for (uint32_t j = i + 1; j < n; j++) {
      int32_t a = obs[i].trigger, b = obs[j].trigger;
      if (a < 0 || b < 0 || a == b)
        continue;
      if ((ap_table_flags(aps, (uint32_t)a) & AP_FLAG_INPUT) &&
          (ap_table_flags(aps, (uint32_t)b) & AP_FLAG_INPUT))
        out->coactivation_candidate_count++;
    }

  // Service capacity is reported only when it is structural rather than
  // guessed: an arbiter block is responses plus a grant mutex, so at most one
  // of the mutually exclusive grants is issued per step.
  for (uint32_t i = 0; i < cov->block_count; i++)
    if (cov->blocks[i].template_name &&
        strstr(cov->blocks[i].template_name, "arbiter")) {
      out->arbiter_blocks++;
      out->service_capacity = 1;
    }

  free(obs);
}

void obligation_census_header(FILE *out) {
  fprintf(out,
          "schema_version\tinstance\tobligation_count\tindexed_obligation_count"
          "\tobligation_types\tmax_family_size\tpairwise_exclusion_edges"
          "\tlargest_exclusion_clique\tservice_capacity\tarbiter_blocks"
          "\tpersistent_trigger_count\tcoactivation_candidate_count\n");
}

void obligation_census_row(FILE *out, const char *instance,
                           const ObligationCensus *c) {
  fprintf(out, "%u\t%s\t%u\t%u\t%u\t%u\t%llu\t%u\t%u\t%u\t%u\t%llu\n",
          c->schema_version, instance ? instance : "-", c->obligation_count,
          c->indexed_obligation_count, c->obligation_types, c->max_family_size,
          (unsigned long long)c->pairwise_exclusion_edges,
          c->largest_exclusion_clique, c->service_capacity, c->arbiter_blocks,
          c->persistent_trigger_count,
          (unsigned long long)c->coactivation_candidate_count);
}
