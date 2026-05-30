/// tlsfinfo — print metadata from a TLSF specification.
///
/// Mirrors the information-printing options of syfco.  With no selection flag
/// it prints the full INFO section followed by the signal and parameter lists.
///
/// Usage:
///   tlsfinfo [SELECTION] FILE
///
/// Selection flags (combine freely; default prints everything):
///   -t,    --title             the title
///   -d,    --description       the description
///   -s,    --semantics         the semantics
///   -g,    --target            the target
///   -a,    --tags              the tags (comma-separated)
///   -p,    --parameters        the parameter names (one per line)
///   -i,    --info              the full INFO section
///   -ins,  --input-signals     the input signals (comma-separated)
///   -outs, --output-signals    the output signals (comma-separated)
///   -v,    --version           version information

#include "tlsf/expand.h"
#include "tlsf/gr.h"
#include "tlsf/spec.h"

#include "tlsf_parse.h"
#include "tlsf_lex.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSFINFO_VERSION "0.1.0"

// ---------------------------------------------------------------------------
// Enum → string helpers (kept in sync with print_tlsf.c)
// ---------------------------------------------------------------------------

static const char *semantics_str(Semantics s) {
  switch (s) {
  case SEM_MEALY:
    return "Mealy";
  case SEM_MOORE:
    return "Moore";
  case SEM_MEALY_STRICT:
    return "Strict,Mealy";
  case SEM_MOORE_STRICT:
    return "Strict,Moore";
  case SEM_MEALY_FINITE:
    return "Finite,Mealy";
  case SEM_MOORE_FINITE:
    return "Finite,Moore";
  }
  return "Mealy";
}

static const char *target_str(Target t) {
  return t == TARGET_MOORE ? "Moore" : "Mealy";
}

// ---------------------------------------------------------------------------
// Selected-output printers
// ---------------------------------------------------------------------------

static void print_signals(FILE *out, const SignalDecl *sigs, uint32_t count) {
  for (uint32_t i = 0; i < count; i++) {
    if (i > 0)
      fprintf(out, ", ");
    if (sigs[i].is_bus)
      fprintf(out, "%s[%u..%u]", sigs[i].name, sigs[i].bus_lo, sigs[i].bus_hi);
    else
      fprintf(out, "%s", sigs[i].name);
  }
  fprintf(out, "\n");
}

static void print_tags(FILE *out, const TlsfSpec *s) {
  for (uint16_t i = 0; i < s->info.tag_count; i++) {
    if (i > 0)
      fprintf(out, ", ");
    fprintf(out, "%s", s->info.tags[i]);
  }
  fprintf(out, "\n");
}

static void print_parameters(FILE *out, const TlsfSpec *s) {
  for (uint16_t i = 0; i < s->param_count; i++)
    fprintf(out, "%s\n", s->params[i].name);
}

static void print_info_block(FILE *out, const TlsfSpec *s) {
  fprintf(out, "Title:         \"%s\"\n", s->info.title ? s->info.title : "");
  fprintf(out, "Description:   \"%s\"\n",
          s->info.description ? s->info.description : "");
  fprintf(out, "Semantics:     %s\n", semantics_str(s->info.semantics));
  fprintf(out, "Target:        %s\n", target_str(s->info.target));
  if (s->info.tag_count > 0) {
    fprintf(out, "Tags:          ");
    print_tags(out, s);
  }
}

// Default view: full info, then signals and parameters.
static void print_all(FILE *out, const TlsfSpec *s) {
  print_info_block(out, s);
  fprintf(out, "Inputs:        ");
  print_signals(out, s->inputs, s->input_count);
  fprintf(out, "Outputs:       ");
  print_signals(out, s->outputs, s->output_count);
  if (s->param_count > 0) {
    fprintf(out, "Parameters:    ");
    for (uint16_t i = 0; i < s->param_count; i++) {
      if (i > 0)
        fprintf(out, ", ");
      fprintf(out, "%s", s->params[i].name);
    }
    fprintf(out, "\n");
  }
}

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

typedef enum {
  SEL_NONE = 0,
  SEL_TITLE,
  SEL_DESCRIPTION,
  SEL_SEMANTICS,
  SEL_TARGET,
  SEL_TAGS,
  SEL_PARAMETERS,
  SEL_INFO,
  SEL_INPUTS,
  SEL_OUTPUTS,
  SEL_GR,
} Selection;

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [SELECTION] FILE\n"
          "  -t,   --title            the title\n"
          "  -d,   --description      the description\n"
          "  -s,   --semantics        the semantics\n"
          "  -g,   --target           the target\n"
          "  -a,   --tags             the tags\n"
          "  -p,   --parameters       the parameter names\n"
          "  -i,   --info             the full INFO section\n"
          "  -ins, --input-signals    the input signals\n"
          "  -outs,--output-signals   the output signals\n"
          "  -gr,  --generalized-reactivity  whether the spec is in GR(1)\n"
          "  -v,   --version          version information\n"
          "With no selection flag, prints everything.\n",
          prog);
}

static Selection parse_selection(const char *arg) {
  struct {
    const char *s, *l;
    Selection sel;
  } opts[] = {
      {"-t", "--title", SEL_TITLE},
      {"-d", "--description", SEL_DESCRIPTION},
      {"-s", "--semantics", SEL_SEMANTICS},
      {"-g", "--target", SEL_TARGET},
      {"-a", "--tags", SEL_TAGS},
      {"-p", "--parameters", SEL_PARAMETERS},
      {"-i", "--info", SEL_INFO},
      {"-ins", "--input-signals", SEL_INPUTS},
      {"-outs", "--output-signals", SEL_OUTPUTS},
      {"-gr", "--generalized-reactivity", SEL_GR},
  };
  for (size_t i = 0; i < sizeof(opts) / sizeof(opts[0]); i++)
    if (strcmp(arg, opts[i].s) == 0 || strcmp(arg, opts[i].l) == 0)
      return opts[i].sel;
  return SEL_NONE;
}

int main(int argc, char *argv[]) {
  Selection sel = SEL_NONE;
  const char *input_file = nullptr;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
      usage(argv[0]);
      return 0;
    }
    if (strcmp(argv[i], "--version") == 0 || strcmp(argv[i], "-v") == 0) {
      printf("tlsfinfo %s\n", TLSFINFO_VERSION);
      return 0;
    }
    if (argv[i][0] == '-') {
      Selection s = parse_selection(argv[i]);
      if (s == SEL_NONE) {
        fprintf(stderr, "tlsfinfo: unknown option '%s'\n", argv[i]);
        usage(argv[0]);
        return 1;
      }
      if (sel != SEL_NONE) {
        fprintf(stderr, "tlsfinfo: only one selection flag is supported\n");
        return 1;
      }
      sel = s;
    } else {
      if (input_file) {
        fprintf(stderr, "tlsfinfo: multiple input files not supported\n");
        return 1;
      }
      input_file = argv[i];
    }
  }

  if (!input_file) {
    fprintf(stderr, "tlsfinfo: no input file\n");
    usage(argv[0]);
    return 1;
  }

  FILE *fp = fopen(input_file, "r");
  if (!fp) {
    perror(input_file);
    return 1;
  }

  TlsfSpec *spec = spec_new();
  if (!spec) {
    fprintf(stderr, "tlsfinfo: out of memory\n");
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

  // No expansion: tlsfinfo reports the raw specification metadata.
  switch (sel) {
  case SEL_TITLE:
    printf("%s\n", spec->info.title ? spec->info.title : "");
    break;
  case SEL_DESCRIPTION:
    printf("%s\n", spec->info.description ? spec->info.description : "");
    break;
  case SEL_SEMANTICS:
    printf("%s\n", semantics_str(spec->info.semantics));
    break;
  case SEL_TARGET:
    printf("%s\n", target_str(spec->info.target));
    break;
  case SEL_TAGS:
    print_tags(stdout, spec);
    break;
  case SEL_PARAMETERS:
    print_parameters(stdout, spec);
    break;
  case SEL_INFO:
    print_info_block(stdout, spec);
    break;
  case SEL_INPUTS:
    print_signals(stdout, spec->inputs, spec->input_count);
    break;
  case SEL_OUTPUTS:
    print_signals(stdout, spec->outputs, spec->output_count);
    break;
  case SEL_GR: {
    // GR(1) recognition needs the ground spec: expand with default parameters.
    if (expand(spec, nullptr, 0) != 0) {
      fprintf(stderr, "tlsfinfo: cannot expand spec for GR(1) check\n");
      spec_free(spec);
      return 1;
    }
    // GR(k) over the full Boolean-combination-of-GF/FG liveness fragment.
    int level = gr_level(spec);
    if (level < 0)
      printf("NOT in GR\n");
    else
      printf("IN GR(%d)\n", level);
    break;
  }
  case SEL_NONE:
    print_all(stdout, spec);
    break;
  }

  spec_free(spec);
  return 0;
}
