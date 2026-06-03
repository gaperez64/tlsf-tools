/// tlsfresidual — what is left of a spec after template certification.
///
/// Runs the cover -> recognize -> certify -> compose pipeline, keeps the
/// maximal sound set of SOLVED blocks (csnf_compose), and re-emits the
/// remaining (residual) obligations as a single LTL formula, ready to hand to
/// an external synthesizer (e.g. `ltlsynt --ins=.. --outs=..`).  The certified
/// controllers plus a controller for this residual realise the whole spec.

#include "tlsf/cli.h"
#include "tlsf/classify.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/recognize.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE]\n"
          "Emit the residual LTL of a spec after template certification.\n"
          "  --split                      decompose constraints first\n"
          "  --format ltlxba|ltl          output dialect (default ltlxba)\n"
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
    fprintf(stderr, "tlsfresidual: bad --param '%s'\n", s);
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
    fprintf(stderr, "tlsfresidual: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

// Map a constraint Role to its destination section list in the spec.
static FormulaList *role_list(TlsfSpec *spec, Role role) {
  switch (role) {
  case TLSF_ROLE_INITIALLY:
    return &spec->initially;
  case TLSF_ROLE_PRESET:
    return &spec->preset;
  case TLSF_ROLE_REQUIRE:
    return &spec->require;
  case TLSF_ROLE_ASSERT:
    return &spec->assert_;
  case TLSF_ROLE_ASSUME:
    return &spec->assume;
  case TLSF_ROLE_GUARANTEE:
  default:
    return &spec->guarantee;
  }
}

// Print a comma-separated list of residual signal names with the given flag.
static void print_signals(FILE *out, ConstraintCover *cov, const bool *residual,
                          uint32_t n, uint8_t flag) {
  bool *seen = calloc(cov->aps.count ? cov->aps.count : 1, sizeof(bool));
  bool first = true;
  for (uint32_t i = 0; i < n; i++) {
    if (!residual[i])
      continue;
    const ApSet *s =
        flag == AP_FLAG_INPUT ? &cov->items[i].inputs : &cov->items[i].outputs;
    for (uint32_t a = 0; a < cov->aps.count; a++) {
      if (seen[a] || !apset_test(s, a))
        continue;
      seen[a] = true;
      fprintf(out, "%s%s", first ? "" : ",", ap_table_name(&cov->aps, a));
      first = false;
    }
  }
  free(seen);
}

int main(int argc, char *argv[]) {
  bool split = false;
  LtlFormat fmt = LTL_FMT_LTLXBA;
  const char *input_file = nullptr, *output_file = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfresidual: %s requires an argument\n",   \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "ltlxba"))
        fmt = LTL_FMT_LTLXBA;
      else if (!strcmp(v, "ltl"))
        fmt = LTL_FMT_LTL;
      else {
        fprintf(stderr, "tlsfresidual: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfresidual: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfresidual %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfresidual: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfresidual: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsfresidual");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfresidual");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfresidual: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfresidual: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  // Cover -> recognize -> certify -> compose.
  ConstraintCover *cov = cover_build(spec, split);
  if (!cov) {
    fprintf(stderr, "tlsfresidual: out of memory\n");
    spec_free(spec);
    return 1;
  }
  recognize_all(cov);
  Csnf *csnf = templates_certify(cov, TPL_ALL, true);
  CsnfComposition *comp = csnf ? csnf_compose(csnf) : nullptr;
  if (!csnf || !comp) {
    fprintf(stderr, "tlsfresidual: out of memory\n");
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  FILE *out = cli_open_output(output_file, "tlsfresidual");
  if (!out) {
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  // Rebuild the spec's section lists from the residual constraints only (the
  // accepted blocks' outputs are globally free, so the residual never refers to
  // them -- it is self-contained).
  spec->initially.count = spec->require.count = spec->assume.count = 0;
  spec->preset.count = spec->assert_.count = spec->guarantee.count = 0;
  for (uint32_t i = 0; i < cov->count; i++)
    if (comp->residual_constraint[i])
      (void)formula_list_push(spec, role_list(spec, cov->items[i].role),
                              cov->items[i].formula);

  if (comp->fully_solved)
    fprintf(out, "c composition: fully-solved\n");
  else
    fprintf(out, "c composition: residual=%u conflicts=%u\n", comp->nresidual,
            comp->nconflicts);
  fprintf(out, "c ins=");
  print_signals(out, cov, comp->residual_constraint, cov->count, AP_FLAG_INPUT);
  fprintf(out, "\nc outs=");
  print_signals(out, cov, comp->residual_constraint, cov->count,
                AP_FLAG_OUTPUT);
  fprintf(out, "\n");

  ClassifiedSpec *cs = classify_spec(spec);
  if (!cs) {
    fprintf(stderr, "tlsfresidual: classification failed (OOM)\n");
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  bool finite = semantics_is_finite(spec->info.semantics);
  if (finite)
    root = apply_rewrites(spec->arena, root,
                          RW_NO_WEAK_UNTIL | RW_NO_STRONG_RELEASE);
  print_ltl(out, root, fmt, /*full_parens=*/false, finite);

  if (output_file)
    fclose(out);
  csnf_composition_free(comp);
  csnf_free(csnf);
  spec_free(spec);
  return 0;
}
