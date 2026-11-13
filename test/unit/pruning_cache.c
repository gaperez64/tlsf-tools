#define _GNU_SOURCE
#include "residual_plan.h"
#include "env_witness.h"

#include "../check.h"
#include <stdlib.h>
#include <string.h>

static bool answer;
static unsigned calls;

EnvWitnessResult __wrap_env_witness_search(const SectionPatternView *dropped,
                                           uint32_t work_budget);
EnvWitnessResult __wrap_env_witness_search(const SectionPatternView *dropped,
                                           uint32_t work_budget) {
  CHECK(dropped->count == 1);
  CHECK(work_budget == ENV_WITNESS_WORK_BUDGET);
  ++calls;
  return answer ? ENV_WITNESS_SATISFIABLE : ENV_WITNESS_UNKNOWN;
}

static void check(bool admitted) {
  const char *source =
      "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { q; r; } "
      "OUTPUTS { p; } ASSUMPTIONS { G F q; } GUARANTEES { G(p <-> X r); } }";
  FILE *input = fmemopen((void *)source, strlen(source), "r");
  CHECK(input);
  TlsfSpec *spec = spec_parse(input, "pruning-cache");
  fclose(input);
  CHECK(spec);
  ConstraintCover *cov = cover_build(spec, false);
  CHECK(cov);
  bool *discharged = calloc(cov->count, sizeof(bool));
  CHECK(discharged);
  CsnfComposition comp = {.elim_constraint = discharged};
  ResidualPlan *plan =
      residual_plan_build(spec, cov, nullptr, &comp, (ResidualPlanOptions){0});
  CHECK(plan && plan->nclusters == 1);
  bool *seen = calloc(cov->aps.count, sizeof(bool));
  CHECK(seen);
  SectionPatternView first, second;
  calls = 0;
  answer = admitted;
  CHECK(residual_plan_build_cluster_view(spec, cov, plan, plan->keys[0], false,
                                         true, seen, &first));
  CHECK(calls == 1 && first.count == (admitted ? 1u : 2u));
  // Simulate a later timeout (or a later successful check). Export must use
  // exactly the first view, including the first decision to retain D.
  answer = !admitted;
  CHECK(residual_plan_build_cluster_view(spec, cov, plan, plan->keys[0], false,
                                         true, seen, &second));
  CHECK(calls == 1 && second.entries == first.entries);
  CHECK(residual_plan_build_cluster(spec, cov, plan, plan->keys[0], false, true,
                                    seen));
  CHECK(calls == 1);
  int32_t q = -1;
  for (uint32_t a = 0; a < cov->aps.count; a++)
    if (strcmp(ap_table_name(&cov->aps, a), "q") == 0)
      q = (int32_t)a;
  CHECK(q >= 0 && seen[q] == !admitted);
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
