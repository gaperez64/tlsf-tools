#include "tlsf/spec.h"
#include "spec_internal.h"
#include "diagnostic.h"

#include "tlsf_parse.h"
#include "tlsf_lex.h"

TlsfSpec *spec_parse_budgeted(FILE *in, const char *prog,
                              int (*cancelled)(void *, size_t), void *ctx) {
  if (cancelled && cancelled(ctx, ARENA_DEFAULT_SLAB_SIZE + 4096))
    return nullptr;
  TlsfSpec *spec = spec_new();
  if (!spec) {
    fprintf(tlsf_diagnostic_stream(), "%s: out of memory\n", prog);
    return nullptr;
  }
  arena_set_budget(spec->arena, cancelled, ctx);

  yyscan_t scanner;
  if (yylex_init_extra(spec, &scanner) != 0) {
    spec_free(spec);
    return nullptr;
  }
  yyset_extra(spec, scanner);
  yyset_in(in, scanner);
  int rc = tlsf_parse(scanner, spec);
  yylex_destroy(scanner);

  if (rc != 0 || arena_failed(spec->arena)) {
    spec_free(spec);
    return nullptr;
  }
  return spec;
}

TlsfSpec *spec_parse(FILE *in, const char *prog) {
  return spec_parse_budgeted(in, prog, nullptr, nullptr);
}
