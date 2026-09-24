#define _GNU_SOURCE
/* Compiled against the verbatim 8b158d7 public headers in old_abi/include. */
#include "tlsf/pipeline.h"
#include "tlsf/gr1_oxidd.h"

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
  const char source[] =
      "INFO { TITLE: \"small\" DESCRIPTION: \"small\" SEMANTICS: Mealy "
      "TARGET: Mealy }\n"
      "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G b; } }\n";
  FILE *in = fmemopen((void *)source, strlen(source), "r");
  assert(in);
  TlsfPipelineOptions *options = calloc(1, sizeof *options);
  assert(options);
  TlsfPipeline *pipeline = tlsf_pipeline_load(in, options);
  assert(pipeline);
  tlsf_pipeline_free(pipeline);
  fclose(in);
  free(options);

  const char game[] = "aag 3 2 1 1 0 0 0 1 0\n2\n4\n6 6 1\n0\n1\n6\n"
                      "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n";
  in = fmemopen((void *)game, strlen(game), "r");
  assert(in);
  Aig *aig = aig_read_aag(in);
  fclose(in);
  assert(aig);
  OxiddSolveOptions *solve = malloc(sizeof *solve);
  assert(solve);
  *solve = oxidd_solve_options_default();
  solve->node_cap = solve->cache_cap = 1u << 16;
  OxiddFailure failure = {0};
  solve->failure = &failure;
  Gr1CertificateOptions *certificate = calloc(1, sizeof *certificate);
  assert(certificate);
  Aig *strategy =
      solve_gr1_oxidd_ex_with_certificate(aig, &(int){0}, solve, certificate);
  assert(strategy && !certificate->failed &&
         failure.kind == OXIDD_FAILURE_NONE);
  aig_free(strategy);
  free(certificate);
  free(solve);
  return 0;
}
