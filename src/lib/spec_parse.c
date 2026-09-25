#include "tlsf/spec.h"
#include "diagnostic.h"

#include "tlsf_parse.h"
#include "tlsf_lex.h"

TlsfSpec *spec_parse(FILE *in, const char *prog) {
  TlsfSpec *spec = spec_new();
  if (!spec) {
    fprintf(tlsf_diagnostic_stream(), "%s: out of memory\n", prog);
    return nullptr;
  }

  yyscan_t scanner;
  yylex_init(&scanner);
  yyset_extra(spec, scanner);
  yyset_in(in, scanner);
  int rc = yyparse(scanner, spec);
  yylex_destroy(scanner);

  if (rc != 0) {
    spec_free(spec);
    return nullptr;
  }
  return spec;
}
