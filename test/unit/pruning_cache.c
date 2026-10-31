#define _GNU_SOURCE
#include "residual_plan.h"
#include "env_witness.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>

static bool answer;
static unsigned calls;

EnvWitnessResult __wrap_env_witness_search(const SectionPatternView *dropped,
                                           uint32_t work_budget);
EnvWitnessResult __wrap_env_witness_search(const SectionPatternView *dropped,
                                           uint32_t work_budget) {
  assert(dropped->count == 1);
  assert(work_budget == ENV_WITNESS_WORK_BUDGET);
  ++calls;
  return answer ? ENV_WITNESS_SATISFIABLE : ENV_WITNESS_UNKNOWN;
}

static void check(bool admitted) {
  const char *source =
      "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { q; r; } "
      "OUTPUTS { p; } ASSUMPTIONS { G F q; } GUARANTEES { G(p <-> X r); } }";
  FILE *input = fmemopen((void *)source, strlen(source), "r");
  assert(input);
  TlsfSpec *spec = spec_parse(input, "pruning-cache");
  fclose(input);
  assert(spec);
  ConstraintCover *cov = cover_build(spec, false);
  assert(cov);
  bool *discharged = calloc(cov->count, sizeof(bool));
  assert(discharged);
  CsnfComposition comp = {.elim_constraint = discharged};
  ResidualPlan *plan =
      residual_plan_build(spec, cov, nullptr, &comp, (ResidualPlanOptions){0});
  assert(plan && plan->nclusters == 1);
  bool *seen = calloc(cov->aps.count, sizeof(bool));
  assert(seen);
  SectionPatternView first, second;
  calls = 0;
  answer = admitted;
  assert(residual_plan_build_cluster_view(spec, cov, plan, plan->keys[0], false,
                                          true, seen, &first));
  assert(calls == 1 && first.count == (admitted ? 1u : 2u));
  // Simulate a later timeout (or a later successful check). Export must use
  // exactly the first view, including the first decision to retain D.
  answer = !admitted;
  assert(residual_plan_build_cluster_view(spec, cov, plan, plan->keys[0], false,
                                          true, seen, &second));
  assert(calls == 1 && second.entries == first.entries);
  assert(residual_plan_build_cluster(spec, cov, plan, plan->keys[0], false,
                                     true, seen));
  assert(calls == 1);
  int32_t q = -1;
  for (uint32_t a = 0; a < cov->aps.count; a++)
    if (strcmp(ap_table_name(&cov->aps, a), "q") == 0)
      q = (int32_t)a;
  assert(q >= 0 && seen[q] == !admitted);
  free(seen);
  residual_plan_free(plan);
  free(discharged);
  spec_free(spec);
}

int main(void) {
  check(true);
  check(false);
  puts("pruning decisions stable across routing, solving and export");
  return 0;
}
