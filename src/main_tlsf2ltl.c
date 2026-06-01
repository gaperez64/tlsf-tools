/// tlsf2ltl — parse a TLSF spec (file or stdin) and emit LTL in ltlxba format.
/// See --help for the options.

#include "tlsf/classify.h"
#include "tlsf/cli.h"
#include "tlsf/expand.h"
#include "tlsf/nnf.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Reads FILE (or stdin) and writes the spec's LTL formula.\n"
      "  --format VALUE               output dialect: ltlxba (default), ltl,\n"
      "                               or latex\n"
      "  --safety, --liveness         emit only safety / liveness "
      "guarantees\n"
      "  --parenthesize               fully parenthesise (default: minimal\n"
      "                               parentheses by operator precedence)\n"
      "  --param NAME=VALUE           override a parameter (repeatable)\n"
      "  --overwrite-semantics VALUE  replace the spec's SEMANTICS\n"
      "  --overwrite-target VALUE     replace the spec's TARGET\n"
      "  --output FILE                write to FILE (default: stdout)\n"
      "  --version, --help\n"
      "\n"
      "Formula transformations (equivalence-preserving, off by default):\n"
      "  --weak-simplify              constant folding / redundancy (syfco "
      "-s0)\n"
      "  --strong-simplify            -s0 + NNF + replace/pull set (syfco "
      "-s1)\n"
      "  --nnf                        convert to negation normal form\n"
      "  --no-weak-until              a W b => (a U b) || G a\n"
      "  --no-release                 a R b => b W (a && b)\n"
      "  --no-finally                 F a => true U a\n"
      "  --no-globally                G a => false R a\n"
      "  --no-derived                 --no-weak-until --no-finally "
      "--no-globally\n"
      "  --push-globally-in           G(a && b) => G a && G b\n"
      "  --push-finally-in            F(a || b) => F a || F b\n"
      "  --push-next-in               X(a && b) => X a && X b (and ||)\n"
      "  --pull-globally-out          G a && G b => G(a && b)\n"
      "  --pull-finally-out           F a || F b => F(a || b)\n"
      "  --pull-next-out              X a && X b => X(a && b) (and ||)\n"
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
    for (uint32_t _i = 0; _i < (list).count; _i++) {                           \
      Node *_n = to_nnf(spec->arena, (list).formulas[_i], true);               \
      if (!_n) {                                                               \
        fprintf(stderr, "tlsf2ltl: NNF transform failed (OOM)\n");             \
        return -1;                                                             \
      }                                                                        \
      (list).formulas[_i] = _n;                                                \
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
  LtlFormat fmt = LTL_FMT_LTLXBA;
  unsigned rw_flags = RW_NONE;
  const char *os_arg = nullptr;
  const char *ot_arg = nullptr;
  const char *input_file = nullptr;
  const char *output_file = nullptr;

  // Temporary override storage (max 64 overrides).
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc                                                                 \
       ? (fprintf(stderr, "tlsf2ltl: %s requires an argument\n", argv[i - 1]), \
          exit(1), nullptr)                                                    \
       : argv[i])

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--safety") == 0) {
      mode = PRINT_SAFETY;
    } else if (strcmp(argv[i], "--liveness") == 0) {
      mode = PRINT_LIVENESS;
    } else if (strcmp(argv[i], "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(argv[i], "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(argv[i], "--parenthesize") == 0) {
      full_parens = true;
    } else if (strcmp(argv[i], "--format") == 0) {
      const char *v = NEED_ARG();
      if (strcmp(v, "ltlxba") == 0)
        fmt = LTL_FMT_LTLXBA;
      else if (strcmp(v, "ltl") == 0)
        fmt = LTL_FMT_LTL;
      else if (strcmp(v, "latex") == 0)
        fmt = LTL_FMT_LATEX;
      else {
        fprintf(stderr,
                "tlsf2ltl: unknown format '%s' (ltlxba, ltl, or latex)\n", v);
        return 1;
      }
    } else if (strcmp(argv[i], "--weak-simplify") == 0) {
      rw_flags |= RW_SIMPLIFY_WEAK;
    } else if (strcmp(argv[i], "--strong-simplify") == 0) {
      rw_flags |= RW_STRONG_SIMPLIFY;
    } else if (strcmp(argv[i], "--nnf") == 0) {
      rw_flags |= RW_NNF;
    } else if (strcmp(argv[i], "--no-weak-until") == 0) {
      rw_flags |= RW_NO_WEAK_UNTIL;
    } else if (strcmp(argv[i], "--no-release") == 0) {
      rw_flags |= RW_NO_RELEASE;
    } else if (strcmp(argv[i], "--no-finally") == 0) {
      rw_flags |= RW_NO_FINALLY;
    } else if (strcmp(argv[i], "--no-globally") == 0) {
      rw_flags |= RW_NO_GLOBALLY;
    } else if (strcmp(argv[i], "--no-derived") == 0) {
      rw_flags |= RW_NO_DERIVED;
    } else if (strcmp(argv[i], "--push-globally-in") == 0) {
      rw_flags |= RW_PUSH_G_IN;
    } else if (strcmp(argv[i], "--push-finally-in") == 0) {
      rw_flags |= RW_PUSH_F_IN;
    } else if (strcmp(argv[i], "--push-next-in") == 0) {
      rw_flags |= RW_PUSH_X_IN;
    } else if (strcmp(argv[i], "--pull-globally-out") == 0) {
      rw_flags |= RW_PULL_G_OUT;
    } else if (strcmp(argv[i], "--pull-finally-out") == 0) {
      rw_flags |= RW_PULL_F_OUT;
    } else if (strcmp(argv[i], "--pull-next-out") == 0) {
      rw_flags |= RW_PULL_X_OUT;
    } else if (strcmp(argv[i], "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(argv[i], "--param") == 0) {
      const char *a = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsf2ltl: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(a, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(argv[i], "--version") == 0) {
      printf("tlsf2ltl %s\n", TLSF_VERSION);
      return 0;
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
#undef NEED_ARG

  // --- Parse (FILE or stdin) ---
  FILE *fp = cli_open_input(input_file, "tlsf2ltl");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsf2ltl");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

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
  // NNF is only needed to classify formulas correctly for the --safety /
  // --liveness split (the syntactic F/U/M test must see negations pushed to
  // the leaves, so that e.g. !(G p) is recognised as the liveness F !p).  The
  // default full-formula output emits every guarantee regardless of class, so
  // we skip NNF there and print the formula as written.
  if (mode != PRINT_ALL && apply_nnf_all(spec) != 0) {
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

  // --- Build the single spec formula, then apply any requested transforms ---
  Node *root = build_spec_formula(spec, cs, mode);
  root = apply_rewrites(spec->arena, root, rw_flags);
  if (!root) {
    fprintf(stderr, "tlsf2ltl: transform failed (OOM)\n");
    spec_free(spec);
    return 1;
  }

  // --- Emit ---
  FILE *out = cli_open_output(output_file, "tlsf2ltl");
  if (!out) {
    spec_free(spec);
    return 1;
  }
  print_ltl(out, root, fmt, full_parens,
            semantics_is_finite(spec->info.semantics));
  if (output_file)
    fclose(out);

  spec_free(spec);
  return 0;
}
