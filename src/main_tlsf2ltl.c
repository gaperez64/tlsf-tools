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
          "Usage: %s [--safety|--liveness] [--parenthesize] [--param N=V]... "
          "FILE\n"
          "  --safety|--liveness  emit only safety / liveness guarantees\n"
          "  --parenthesize       fully parenthesise the output (default:\n"
          "                       minimal parentheses by operator precedence)\n"
          "  --param N=V          override a TLSF parameter (repeatable)\n"
          "  -os, --overwrite-semantics V  replace the spec's SEMANTICS\n"
          "  -ot, --overwrite-target V     replace the spec's TARGET\n"
          "\n"
          "Mealy/Moore and finite/infinite are taken from SEMANTICS; when\n"
          "SEMANTICS and TARGET disagree on Mealy vs Moore the formula is\n"
          "converted to the target.\n",
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
// Mealy/Moore adaptation.
//
// The SEMANTICS field says which timing the spec is written in; the TARGET
// says which machine to produce.  When they disagree the formula is converted
// (TLSF v1.x): Moore->Mealy delays the outputs (o becomes X o), Mealy->Moore
// delays the inputs (i becomes X i).  Applied to the expanded (scalar) spec.
// ---------------------------------------------------------------------------

// True if `name` (interned) is one of the listed signals.
static bool in_signals(const char *name, const SignalDecl *sigs,
                       uint32_t count) {
  for (uint32_t i = 0; i < count; i++)
    if (sigs[i].name == name)
      return true;
  return false;
}

// Wrap every AP whose name is in {sigs} with X.  Compound nodes are rebuilt
// in place (formulas are not shared after expansion); AP nodes are replaced.
static Node *wrap_aps(Arena *a, Node *n, const SignalDecl *sigs,
                      uint32_t count) {
  switch (n->kind) {
  case NODE_AP:
    return in_signals(n->name, sigs, count) ? node_x(a, n) : n;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    n->arg = wrap_aps(a, n->arg, sigs, count);
    return n;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    n->lhs = wrap_aps(a, n->lhs, sigs, count);
    n->rhs = wrap_aps(a, n->rhs, sigs, count);
    return n;
  default: // true / false
    return n;
  }
}

static void adapt_mealy_moore(TlsfSpec *spec) {
  bool sem_moore = semantics_is_moore(spec->info.semantics);
  bool tgt_moore = (spec->info.target == TARGET_MOORE);
  if (sem_moore == tgt_moore)
    return; // frames already agree

  // Moore spec -> Mealy target: delay outputs.  Mealy spec -> Moore: inputs.
  const SignalDecl *sigs = sem_moore ? spec->outputs : spec->inputs;
  uint32_t count = sem_moore ? spec->output_count : spec->input_count;

#define WRAP_LIST(list)                                                        \
  for (uint32_t _i = 0; _i < (list).count; _i++)                               \
  (list).formulas[_i] = wrap_aps(spec->arena, (list).formulas[_i], sigs, count)
  WRAP_LIST(spec->initially);
  WRAP_LIST(spec->require);
  WRAP_LIST(spec->assume);
  WRAP_LIST(spec->preset);
  WRAP_LIST(spec->assert_);
  WRAP_LIST(spec->guarantee);
#undef WRAP_LIST
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
  bool full_parens = false;
  const char *os_arg = nullptr;
  const char *ot_arg = nullptr;
  const char *input_file = nullptr;

  // Temporary override storage (max 64 overrides).
  ParamOverride overrides[64];
  size_t n_overrides = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--safety") == 0) {
      mode = PRINT_SAFETY;
    } else if (strcmp(argv[i], "--liveness") == 0) {
      mode = PRINT_LIVENESS;
    } else if (strcmp(argv[i], "--overwrite-semantics") == 0 ||
               strcmp(argv[i], "-os") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2ltl: %s requires an argument\n", argv[i - 1]);
        return 1;
      }
      os_arg = argv[i];
    } else if (strcmp(argv[i], "--overwrite-target") == 0 ||
               strcmp(argv[i], "-ot") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2ltl: %s requires an argument\n", argv[i - 1]);
        return 1;
      }
      ot_arg = argv[i];
    } else if (strcmp(argv[i], "--parenthesize") == 0 ||
               strcmp(argv[i], "--parens") == 0) {
      full_parens = true;
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

  // --- Apply semantics/target overrides ---
  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsf2ltl: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsf2ltl: invalid target '%s' (expect Mealy or Moore)\n",
            ot_arg);
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

  // --- Mealy/Moore adaptation (after expansion: signals are scalar) ---
  adapt_mealy_moore(spec);

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
  print_ltlxba_spec(stdout, spec, cs, mode, full_parens);

  spec_free(spec);
  return 0;
}
