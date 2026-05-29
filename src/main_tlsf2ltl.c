/// tlsf2ltl — parse a TLSF spec and emit LTL in ltlxba format.
///
/// Usage:
///   tlsf2ltl [options] FILE
///
/// Options:
///   --safety    Emit only the safety part of the guarantee formulas.
///   --liveness  Emit only the liveness part of the guarantee formulas.
///   --param NAME=VALUE  Override a TLSF parameter (may be repeated).
///   --help

#include "tlsf/classify.h"
#include "tlsf/expand.h"
#include "tlsf/nnf.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/spec.h"

// Flex/bison interface (parser header first: it defines YYSTYPE/YYLTYPE and
// yyscan_t, which the lexer header references).
#include "tlsf_parse.h" /* yyparse, YYSTYPE, YYLTYPE, yyscan_t */
#include "tlsf_lex.h"   /* yylex_init, yyset_extra, yylex_destroy */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [--safety|--liveness] [--param N=V]... FILE\n",
          prog);
}

// Parse a "NAME=VALUE" override string.
static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsf2ltl: bad --param argument '%s' (expect NAME=VALUE)\n",
            s);
    return false;
  }
  // Temporary copy of the name part (not interned yet).
  size_t nlen = (size_t)(eq - s);
  char *name = malloc(nlen + 1);
  if (!name)
    return false;
  memcpy(name, s, nlen);
  name[nlen] = '\0';
  char *end;
  long long val = strtoll(eq + 1, &end, 10);
  if (*end != '\0') {
    fprintf(stderr, "tlsf2ltl: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name; // caller frees after expand()
  out->value = (int64_t)val;
  return true;
}

// ---------------------------------------------------------------------------
// Apply NNF to all formula lists in the spec.
// ---------------------------------------------------------------------------

static int apply_nnf_all(TlsfSpec *spec) {
#define NNF_LIST(list)                                                         \
  do {                                                                         \
    for (uint32_t _i = 0; _i < (list).count; _i++) {                          \
      Node *_n = to_nnf(spec->arena, (list).formulas[_i], true);              \
      if (!_n) {                                                               \
        fprintf(stderr, "tlsf2ltl: NNF transform failed (OOM)\n");            \
        return -1;                                                             \
      }                                                                        \
      (list).formulas[_i] = _n;                                               \
    }                                                                          \
  } while (0)

  NNF_LIST(spec->initially);
  NNF_LIST(spec->preset);
  NNF_LIST(spec->require);
  NNF_LIST(spec->assert_);
  NNF_LIST(spec->assume);
  NNF_LIST(spec->guarantee);
  return 0;
#undef NNF_LIST
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

int main(int argc, char *argv[]) {
  PrintMode mode = PRINT_ALL;
  const char *input_file = nullptr;

  // Temporary override storage (max 64 overrides).
  ParamOverride overrides[64];
  size_t n_overrides = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--safety") == 0) {
      mode = PRINT_SAFETY;
    } else if (strcmp(argv[i], "--liveness") == 0) {
      mode = PRINT_LIVENESS;
    } else if (strcmp(argv[i], "--param") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2ltl: --param requires an argument\n");
        return 1;
      }
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsf2ltl: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(argv[i], &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(argv[i], "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (argv[i][0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsf2ltl: multiple input files not supported\n");
        return 1;
      }
      input_file = argv[i];
    } else {
      fprintf(stderr, "tlsf2ltl: unknown option '%s'\n", argv[i]);
      usage(argv[0]);
      return 1;
    }
  }

  if (!input_file) {
    fprintf(stderr, "tlsf2ltl: no input file\n");
    usage(argv[0]);
    return 1;
  }

  FILE *fp = fopen(input_file, "r");
  if (!fp) {
    perror(input_file);
    return 1;
  }

  // --- Parse ---
  TlsfSpec *spec = spec_new();
  if (!spec) {
    fprintf(stderr, "tlsf2ltl: out of memory\n");
    fclose(fp);
    return 1;
  }

  yyscan_t scanner;
  yylex_init(&scanner);
  yyset_extra(spec, scanner);
  yyset_in(fp, scanner);

  int parse_result = yyparse(scanner, spec);
  yylex_destroy(scanner);
  fclose(fp);

  if (parse_result != 0) {
    spec_free(spec);
    return 1;
  }

  // --- Expand ---
  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }

  // Free override name copies.
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  // --- NNF ---
  if (apply_nnf_all(spec) != 0) {
    spec_free(spec);
    return 1;
  }

  // --- Classify ---
  ClassifiedSpec *cs = classify_spec(spec);
  if (!cs) {
    fprintf(stderr, "tlsf2ltl: classification failed (OOM)\n");
    spec_free(spec);
    return 1;
  }

  // --- Emit ---
  print_ltlxba_spec(stdout, spec, cs, mode);

  spec_free(spec);
  return 0;
}
