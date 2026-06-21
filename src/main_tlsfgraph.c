/// tlsfgraph — build and inspect the TLSF synthesis graph (GSNF) of a spec.
/// Operates on the expanded constraint cover, before LTL flattening.  Output is
/// candidate-only: it exposes structure and template candidates but does not
/// solve, certify, or remove anything.  See --help.

#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/graph.h"
#include "tlsf/recognize.h"
#include "tlsf/spec.h"
#include "tlsf/wl.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Builds the synthesis graph (GSNF) of a TLSF spec (FILE or stdin).\n"
      "  --format text|gsnf|dot|tsv   output format (default text); gsnf is\n"
      "                               the DIMACS-style line format\n"
      "  --graph synthesis|constraint complete graph kind (default "
      "synthesis)\n"
      "  --wl N                       append WL features of depth N\n"
      "  --wl-labels basic|synthesis|template   WL label scheme (default "
      "synthesis)\n"
      "  --split                      split constraints at top-level &&\n"
      "  --templates                  include template-candidate info\n"
      "  --template NAME              restrict to one template\n"
      "  --template-candidates-only   emit only candidate blocks\n"
      "  --roles LIST                 comma-separated TLSF roles to keep\n"
      "  --assumptions / --guarantees keep only that side\n"
      "  --safety / --liveness        keep only that syntactic class\n"
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
    fprintf(stderr, "tlsfgraph: bad --param '%s' (expect NAME=VALUE)\n", s);
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
    fprintf(stderr, "tlsfgraph: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

// Map a role keyword to its bit; returns false on unknown.
static bool role_bit(const char *s, unsigned *bit) {
  static const char *names[] = {"INITIALLY", "PRESET", "REQUIRE",
                                "ASSERT",    "ASSUME", "GUARANTEE"};
  for (unsigned i = 0; i < 6; i++)
    if (strcmp(s, names[i]) == 0) {
      *bit = 1u << i;
      return true;
    }
  return false;
}

int main(int argc, char *argv[]) {
  GraphFormat fmt = GFMT_TEXT;
  GraphOpts o = {.kind = GK_SYNTHESIS};
  const char *input_file = nullptr, *output_file = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  unsigned role_mask = 0; // 0 = all roles
  bool want_assume = false, want_guar = false;
  bool want_safety = false, want_live = false;
  int wl_rounds = -1; // < 0 = no WL
  WlLabels wl_labels = WL_SYNTHESIS;
  bool split = false;

  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfgraph: %s requires an argument\n",      \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "text"))
        fmt = GFMT_TEXT;
      else if (!strcmp(v, "gsnf"))
        fmt = GFMT_GSNF;
      else if (!strcmp(v, "dot"))
        fmt = GFMT_DOT;
      else if (!strcmp(v, "tsv"))
        fmt = GFMT_TSV;
      else {
        fprintf(stderr, "tlsfgraph: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--graph") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "synthesis"))
        o.kind = GK_SYNTHESIS;
      else if (!strcmp(v, "constraint"))
        o.kind = GK_CONSTRAINT;
      else {
        fprintf(stderr, "tlsfgraph: unknown graph kind '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--wl") == 0) {
      wl_rounds = (int)strtol(NEED_ARG(), nullptr, 10);
      if (wl_rounds < 0) {
        fprintf(stderr, "tlsfgraph: --wl N must be >= 0\n");
        return 1;
      }
    } else if (strcmp(a, "--wl-labels") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "basic"))
        wl_labels = WL_BASIC;
      else if (!strcmp(v, "synthesis"))
        wl_labels = WL_SYNTHESIS;
      else if (!strcmp(v, "template"))
        wl_labels = WL_TEMPLATE;
      else {
        fprintf(stderr, "tlsfgraph: unknown --wl-labels '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--templates") == 0) {
      o.templates = true;
    } else if (strcmp(a, "--template") == 0) {
      o.only_template = NEED_ARG();
      o.templates = true;
    } else if (strcmp(a, "--template-candidates-only") == 0) {
      o.candidates_only = true;
      o.templates = true;
    } else if (strcmp(a, "--roles") == 0) {
      char *list = strdup(NEED_ARG());
      for (char *tok = strtok(list, ","); tok; tok = strtok(nullptr, ",")) {
        unsigned bit;
        if (!role_bit(tok, &bit)) {
          fprintf(stderr, "tlsfgraph: unknown role '%s'\n", tok);
          free(list);
          return 1;
        }
        role_mask |= bit;
      }
      free(list);
    } else if (strcmp(a, "--assumptions") == 0) {
      want_assume = true;
    } else if (strcmp(a, "--guarantees") == 0) {
      want_guar = true;
    } else if (strcmp(a, "--safety") == 0) {
      want_safety = true;
    } else if (strcmp(a, "--liveness") == 0) {
      want_live = true;
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfgraph: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfgraph %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfgraph: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfgraph: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsfgraph");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfgraph");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfgraph: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfgraph: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (!spec_validate_semantics(spec, "tlsfgraph")) {
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
    fprintf(stderr, "tlsfgraph: out of memory building constraint cover\n");
    spec_free(spec);
    return 1;
  }
  recognize_all(cov);

  // Constraint selection from the filter flags (AND across active categories).
  bool *selected = nullptr;
  bool any_filter =
      role_mask || want_assume || want_guar || want_safety || want_live;
  if (any_filter) {
    selected = malloc(cov->count * sizeof(bool));
    for (uint32_t i = 0; i < cov->count; i++) {
      Constraint *c = &cov->items[i];
      bool ok = true;
      if (role_mask && !(role_mask & (1u << (unsigned)c->role)))
        ok = false;
      if ((want_assume || want_guar) && !((want_assume && c->assumption_side) ||
                                          (want_guar && c->guarantee_side)))
        ok = false;
      if ((want_safety || want_live) &&
          !((want_safety && c->is_safety) || (want_live && !c->is_safety)))
        ok = false;
      selected[i] = ok;
    }
    o.selected = selected;
  }

  FILE *out = cli_open_output(output_file, "tlsfgraph");
  if (!out) {
    free(selected);
    spec_free(spec);
    return 1;
  }
  int rc = graph_emit(out, cov, fmt, &o);
  if (rc != 0)
    fprintf(stderr, "tlsfgraph: --graph kind not implemented yet\n");

  // WL features, appended after the graph (or emitted standalone for text).
  if (rc == 0 && wl_rounds >= 0) {
    WlFeatures *wf = wl_compute(cov, wl_rounds, wl_labels);
    if (!wf) {
      fprintf(stderr, "tlsfgraph: out of memory computing WL features\n");
      rc = 1;
    } else {
      wl_features_emit(out, wf, input_file ? input_file : "<stdin>");
      wl_features_free(wf);
    }
  }

  if (output_file)
    fclose(out);
  free(selected);
  spec_free(spec);
  return rc == 0 ? 0 : 2;
}
