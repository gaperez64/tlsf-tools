#define _GNU_SOURCE
#include "templates_internal.h"
#include "recognize.h"
#include "residual_plan.h"
#include "print_ltlxba.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>

// Exercise composition's local-certificate interface independently of the
// stricter certifiers. Otherwise output_is_free masks the Phase B regression.
int main(int argc, char **argv) {
  assert(argc == 2);
  bool chain = strcmp(argv[1], "chain") == 0;
  // In the chain, s precedes p in the AP table: p := s is substituted after
  // s := r, so closing G p's support to r requires another pass.
  const char *source =
      chain
          ? "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { q; } "
            "OUTPUTS { s; p; r; } GUARANTEES { G(p <-> s); G(s <-> r); "
            "G(q -> X !r); G p; } }"
          : "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { q; } "
            "OUTPUTS { p; r; } GUARANTEES { G(p <-> r); G(q -> X !r); G p; } }";
  FILE *input = fmemopen((void *)source, strlen(source), "r");
  assert(input);
  TlsfSpec *spec = spec_parse(input, "phase-b-probe");
  fclose(input);
  assert(spec);
  ConstraintCover *cov = cover_build(spec, false);
  assert(cov);
  recognize_all(cov);
  Csnf *csnf = templates_certify(cov, TPL_DEFINITION | TPL_GUARDED_NEXT, true);
  assert(csnf);
  uint32_t reg = UINT32_MAX;
  for (uint32_t b = 0; b < csnf->nblocks; b++) {
    Block *blk = &csnf->blocks[b];
    if (blk->nsf_output < 0)
      continue;
    assert(blk->status == CSNF_CANDIDATE);
    reg = b;
    // Supply the local controller o' := false. Phase B must reject it after
    // definition substitution exposes r in the otherwise output-p-only use.
    blk->status = CSNF_SOLVED;
    for (uint32_t k = 0; k < blk->ncids; k++)
      csnf->solved[blk->cids[k]] = true;
  }
  assert(reg != UINT32_MAX);
  puts("register before Phase B: solved");
  CsnfComposition *comp = csnf_compose(csnf);
  assert(comp);
  assert(comp->nelim == (chain ? 2u : 1u));
  printf("register after Phase B: %s\n",
         comp->accepted_block[reg] ? "accepted" : "rejected");
  for (uint32_t k = 0; k < comp->nconflicts; k++) {
    Conflict *cf = &comp->conflicts[k];
    assert(cf->kind == CONFLICT_SHARED_OUTPUT && cf->block == reg);
    printf("conflict: shared-output %s\n",
           ap_table_name(&cov->aps, (uint32_t)cf->output));
  }
  ResidualPlan *plan =
      residual_plan_build(spec, cov, csnf, comp, (ResidualPlanOptions){0});
  assert(plan);
  bool *seen = calloc(cov->aps.count, sizeof(bool));
  assert(seen);
  Node *formula =
      residual_plan_build_cluster(spec, cov, plan, 0, true, true, seen);
  assert(formula);
  assert(print_ltl(stdout, formula, LTL_FMT_LTLXBA, false, false, false));
  free(seen);
  residual_plan_free(plan);
  csnf_composition_free(comp);
  csnf_free(csnf);
  spec_free(spec);
  return 0;
}
