/// tlsfnorm — local, equivalence-preserving normalization of a TLSF spec,
/// re-emitted as TLSF.  Each section is the conjunction of its formulas, so the
/// passes operate per-section without changing the spec's meaning:
///   split   — decompose each formula into its top-level && conjuncts
///   nnf     — push negations to the leaves
///   boolean — constant folding / redundancy removal (syfco -s0)

#include "tlsf/cli.h"
#include "tlsf/expand.h"
#include "tlsf/nnf.h"
#include "tlsf/print_tlsf.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE]\n"
          "Local normalization of a TLSF spec, re-emitted as TLSF.\n"
          "  --passes LIST                comma list of: split, nnf, boolean\n"
          "                               (default: split), applied in order\n"
          "  --format tlsf|trace          output (default tlsf)\n"
          "  --overwrite-semantics VALUE  replace SEMANTICS\n"
          "  --overwrite-target VALUE     replace TARGET\n"
          "  --param NAME=VALUE           override a parameter (repeatable)\n"
          "  --output FILE                write to FILE (default stdout)\n"
          "  --version, --help\n",
          prog);
}

static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsfnorm: bad --param '%s'\n", s);
    return false;
  }
  size_t nlen = (size_t)(eq - s);
  char *name = malloc(nlen + 1);
  if (!name)
    return false;
  memcpy(name, s, nlen);
  name[nlen] = '\0';
  char *end;
  long long val = strtoll(eq + 1, &end, 10);
  if (*end != '\0') {
    fprintf(stderr, "tlsfnorm: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

typedef enum { PASS_SPLIT, PASS_NNF, PASS_BOOLEAN } Pass;

static const char *RESERVED_PASSES[] = {"response", "expose-gf", "expose-fg",
                                        "offending"};

// Apply one pass to one section list (in spec->arena).  Returns the new count.
static void apply_pass(TlsfSpec *spec, FormulaList *L, Pass pass) {
  if (pass == PASS_SPLIT) {
    FormulaList nl = {0};
    for (uint32_t i = 0; i < L->count; i++) {
      Node **parts;
      uint32_t np = rewrite_decompose(spec->arena, L->formulas[i], &parts);
      for (uint32_t p = 0; p < np; p++)
        (void)formula_list_push(spec, &nl, parts[p]);
    }
    *L = nl;
  } else {
    for (uint32_t i = 0; i < L->count; i++)
      L->formulas[i] =
          pass == PASS_NNF
              ? to_nnf(spec->arena, L->formulas[i], true)
              : apply_rewrites(spec->arena, L->formulas[i], RW_SIMPLIFY_WEAK);
  }
}

int main(int argc, char *argv[]) {
  Pass passes[8];
  int npasses = 0;
  bool have_passes = false, trace = false;
  const char *input_file = nullptr, *output_file = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc                                                                 \
       ? (fprintf(stderr, "tlsfnorm: %s requires an argument\n", argv[i - 1]), \
          exit(1), nullptr)                                                    \
       : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--passes") == 0) {
      have_passes = true;
      char *list = strdup(NEED_ARG());
      for (char *tok = strtok(list, ","); tok; tok = strtok(nullptr, ",")) {
        for (size_t r = 0; r < sizeof RESERVED_PASSES / sizeof *RESERVED_PASSES;
             r++)
          if (strcmp(tok, RESERVED_PASSES[r]) == 0) {
            fprintf(stderr, "tlsfnorm: pass '%s' is not implemented yet\n",
                    tok);
            free(list);
            return 2;
          }
        if (npasses >= 8) {
          fprintf(stderr, "tlsfnorm: too many passes\n");
          free(list);
          return 1;
        }
        if (!strcmp(tok, "split"))
          passes[npasses++] = PASS_SPLIT;
        else if (!strcmp(tok, "nnf"))
          passes[npasses++] = PASS_NNF;
        else if (!strcmp(tok, "boolean"))
          passes[npasses++] = PASS_BOOLEAN;
        else {
          fprintf(stderr, "tlsfnorm: unknown pass '%s'\n", tok);
          free(list);
          return 1;
        }
      }
      free(list);
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "tlsf"))
        trace = false;
      else if (!strcmp(v, "trace"))
        trace = true;
      else {
        fprintf(stderr, "tlsfnorm: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfnorm: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfnorm %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (!strcmp(a, "--global") || !strcmp(a, "--all-depths") ||
               !strcmp(a, "--pass-schedule") ||
               !strcmp(a, "--stop-on-stable") || !strcmp(a, "--output-dir") ||
               !strcmp(a, "--max-size") || !strcmp(a, "--max-nodes")) {
      fprintf(stderr, "tlsfnorm: %s is not implemented yet\n", a);
      return 2;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfnorm: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfnorm: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  if (!have_passes)
    passes[npasses++] = PASS_SPLIT; // default

  FILE *fp = cli_open_input(input_file, "tlsfnorm");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfnorm");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfnorm: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfnorm: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (!spec_validate_semantics(spec, "tlsfnorm")) {
    spec_free(spec);
    return 1;
  }
  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  FormulaList *lists[] = {&spec->initially, &spec->require, &spec->assume,
                          &spec->preset,    &spec->assert_, &spec->guarantee};
  static const char *names[] = {"INITIALLY", "REQUIRE", "ASSUME",
                                "PRESET",    "ASSERT",  "GUARANTEE"};
  static const char *pass_names[] = {"split", "nnf", "boolean"};

  FILE *out = cli_open_output(output_file, "tlsfnorm");
  if (!out) {
    spec_free(spec);
    return 1;
  }

  for (int p = 0; p < npasses; p++) {
    for (int s = 0; s < 6; s++) {
      uint32_t before = lists[s]->count;
      apply_pass(spec, lists[s], passes[p]);
      if (trace && lists[s]->count != before)
        fprintf(out, "c pass %s: %s %u -> %u\n", pass_names[passes[p]],
                names[s], before, lists[s]->count);
    }
  }

  if (!trace)
    print_tlsf(out, spec, /*include_global=*/false);

  if (output_file)
    fclose(out);
  spec_free(spec);
  return 0;
}
