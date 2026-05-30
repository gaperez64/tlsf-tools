#include "tlsf/cli.h"

#include "tlsf_parse.h"
#include "tlsf_lex.h"

FILE *cli_open_input(const char *path, const char *prog) {
  if (!path)
    return stdin;
  FILE *f = fopen(path, "r");
  if (!f) {
    fprintf(stderr, "%s: ", prog);
    perror(path);
  }
  return f;
}

FILE *cli_open_output(const char *path, const char *prog) {
  if (!path)
    return stdout;
  FILE *f = fopen(path, "w");
  if (!f) {
    fprintf(stderr, "%s: ", prog);
    perror(path);
  }
  return f;
}

TlsfSpec *cli_parse(FILE *in, const char *prog) {
  TlsfSpec *spec = spec_new();
  if (!spec) {
    fprintf(stderr, "%s: out of memory\n", prog);
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
