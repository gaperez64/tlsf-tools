/// tlsftemplates — find and (optionally) certify template-solvable blocks of a
/// TLSF spec, emitting CSNF.  Soundness rule (candidate -> checked -> certified
/// -> solved): a block is SOLVED only after a side condition passes and a
/// controller/decoder + certificate is produced.  Nothing is removed here.

#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/recognize.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE]\n"
          "Find/certify template-solvable blocks of a TLSF spec (CSNF).\n"
          "  --candidates                 list candidate blocks (default)\n"
          "  --certify                    check side conditions, certify "
          "blocks\n"
          "  --solve                      include controller/decoder "
          "artifacts\n"
          "  --split                      split constraints at top-level &&\n"
          "  --check                      report whole-spec composition "
          "soundness\n"
          "  --template NAME              restrict to one certifiable "
          "template\n"
          "  --templates LIST             comma-separated certifiable "
          "templates\n"
          "  --list-templates             print recognized templates and "
          "exit\n"
          "  --format text|csnf           output format (default text)\n"
          "  --side-conditions syntactic  side-condition mode (sat/bdd "
          "reserved)\n"
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
    fprintf(stderr, "tlsftemplates: bad --param '%s'\n", s);
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
    fprintf(stderr, "tlsftemplates: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

// Map a certifiable template name to its TPL_* bit (0 = unknown).
static unsigned tpl_bit(const char *s) {
  if (!strcmp(s, "definition"))
    return TPL_DEFINITION;
  if (!strcmp(s, "round-robin"))
    return TPL_ROUND_ROBIN;
  if (!strcmp(s, "guarded-next-assignment"))
    return TPL_GUARDED_NEXT;
  if (!strcmp(s, "mutex"))
    return TPL_MUTEX;
  if (!strcmp(s, "arbiter"))
    return TPL_ARBITER;
  if (!strcmp(s, "response"))
    return TPL_RESPONSE;
  if (!strcmp(s, "persistence"))
    return TPL_PERSISTENCE;
  if (!strcmp(s, "reachability"))
    return TPL_REACHABILITY;
  if (!strcmp(s, "reaction"))
    return TPL_REACTION;
  if (!strcmp(s, "delayed-definition"))
    return TPL_DELAYED_DEF;
  if (!strcmp(s, "safety-invariant"))
    return TPL_INVARIANT;
  return 0;
}

static const char *conflict_kind(ConflictKind k) {
  switch (k) {
  case CONFLICT_DUP_OUTPUT:
    return "dup-output";
  case CONFLICT_SHARED_OUTPUT:
    return "shared-output";
  case CONFLICT_DECODER_CYCLE:
  default:
    return "decoder-cycle";
  }
}

// Print the whole-spec composition verdict: whether the locally-SOLVED blocks
// compose into a sound decomposition, and which were ejected.
static void print_composition(FILE *out, ConstraintCover *cov,
                              const CsnfComposition *comp) {
  if (comp->fully_solved) {
    fprintf(out, "composition: fully-solved\n");
    return;
  }
  fprintf(out, "composition: residual=%u conflicts=%u accepted=%u\n",
          comp->nresidual, comp->nconflicts, comp->naccepted);
  for (uint32_t i = 0; i < comp->nconflicts; i++) {
    const Conflict *c = &comp->conflicts[i];
    fprintf(out, "x %s %s block %u\n", conflict_kind(c->kind),
            c->output >= 0 ? ap_table_name(&cov->aps, (uint32_t)c->output)
                           : "?",
            c->block);
  }
}

int main(int argc, char *argv[]) {
  bool certify = false, solve = false, csnf = false, split = false,
       check = false;
  unsigned want = TPL_ALL;
  const char *input_file = nullptr, *output_file = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsftemplates: %s requires an argument\n",  \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--candidates") == 0) {
      certify = false;
    } else if (strcmp(a, "--certify") == 0) {
      certify = true;
    } else if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--check") == 0) {
      check = true;
      certify = true;
    } else if (strcmp(a, "--solve") == 0) {
      solve = true;
      certify = true;
    } else if (strcmp(a, "--list-templates") == 0) {
      for (int t = 0; t < TEMPLATE_NAMES_COUNT; t++)
        printf("%s\n", TEMPLATE_NAMES[t]);
      return 0;
    } else if (strcmp(a, "--template") == 0) {
      unsigned bit = tpl_bit(NEED_ARG());
      if (!bit) {
        fprintf(stderr,
                "tlsftemplates: '%s' is not a certifiable template "
                "this milestone\n",
                argv[i]);
        return 1;
      }
      want |= bit;
    } else if (strcmp(a, "--templates") == 0) {
      char *list = strdup(NEED_ARG());
      for (char *tok = strtok(list, ","); tok; tok = strtok(nullptr, ",")) {
        unsigned bit = tpl_bit(tok);
        if (!bit) {
          fprintf(stderr, "tlsftemplates: '%s' is not certifiable\n", tok);
          free(list);
          return 1;
        }
        want |= bit;
      }
      free(list);
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "text"))
        csnf = false;
      else if (!strcmp(v, "csnf"))
        csnf = true;
      else {
        fprintf(stderr, "tlsftemplates: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--side-conditions") == 0) {
      const char *v = NEED_ARG();
      if (strcmp(v, "syntactic") != 0) {
        fprintf(stderr,
                "tlsftemplates: --side-conditions %s not implemented "
                "(only 'syntactic')\n",
                v);
        return 2;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsftemplates: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsftemplates %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (!strcmp(a, "--from-gsnf") || !strcmp(a, "--template-library") ||
               !strcmp(a, "--disable")) {
      fprintf(stderr,
              "tlsftemplates: %s is not implemented yet (GSNF line reader is "
              "milestone 6)\n",
              a);
      return 2;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsftemplates: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsftemplates: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsftemplates");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsftemplates");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsftemplates: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsftemplates: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  ConstraintCover *cov = cover_build(spec, split);
  if (!cov) {
    fprintf(stderr, "tlsftemplates: out of memory\n");
    spec_free(spec);
    return 1;
  }
  recognize_all(cov);
  Csnf *model = templates_certify(cov, want, certify);
  if (!model) {
    fprintf(stderr, "tlsftemplates: out of memory\n");
    spec_free(spec);
    return 1;
  }

  FILE *out = cli_open_output(output_file, "tlsftemplates");
  if (!out) {
    csnf_free(model);
    spec_free(spec);
    return 1;
  }
  if (csnf)
    csnf_emit_lines(out, model, input_file ? input_file : "<stdin>", solve);
  else
    csnf_emit_text(out, model, solve);

  int rc = 0;
  if (check) {
    CsnfComposition *comp = csnf_compose(model);
    if (!comp) {
      fprintf(stderr, "tlsftemplates: out of memory\n");
      rc = 1;
    } else {
      print_composition(out, cov, comp);
      csnf_composition_free(comp);
    }
  }
  if (output_file)
    fclose(out);

  csnf_free(model);
  spec_free(spec);
  return rc;
}
