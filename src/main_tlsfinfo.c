/// tlsfinfo — print metadata from a TLSF specification (file or stdin).
///
/// Mirrors the information-printing options of syfco (long names only).  With
/// no selection flag it prints the full INFO section followed by the signal
/// and parameter lists.  See --help for the options.

#include "tlsf/cli.h"
#include "tlsf/expand.h"
#include "tlsf/gr.h"
#include "tlsf/spec.h"

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
  SEL_CHECK,
} Selection;

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [SELECTION] [--output FILE] [FILE]\n"
          "Reads FILE (or stdin) and prints the requested metadata.\n"
          "  --title, --description, --semantics, --target, --tags\n"
          "  --parameters, --info, --input-signals, --output-signals\n"
          "  --generalized-reactivity   the GR(k) level (or NOT in GR)\n"
          "  --check                    verify the spec parses (conforms)\n"
          "  --output FILE              write to FILE (default: stdout)\n"
          "  --version, --help\n"
          "With no selection flag, prints everything.\n",
          prog);
}

static Selection parse_selection(const char *arg) {
  struct {
    const char *l;
    Selection sel;
  } opts[] = {
      {"--title", SEL_TITLE},
      {"--description", SEL_DESCRIPTION},
      {"--semantics", SEL_SEMANTICS},
      {"--target", SEL_TARGET},
      {"--tags", SEL_TAGS},
      {"--parameters", SEL_PARAMETERS},
      {"--info", SEL_INFO},
      {"--input-signals", SEL_INPUTS},
      {"--output-signals", SEL_OUTPUTS},
      {"--generalized-reactivity", SEL_GR},
      {"--check", SEL_CHECK},
  };
  for (size_t i = 0; i < sizeof(opts) / sizeof(opts[0]); i++)
    if (strcmp(arg, opts[i].l) == 0)
      return opts[i].sel;
  return SEL_NONE;
}

int main(int argc, char *argv[]) {
  Selection sel = SEL_NONE;
  const char *input_file = nullptr;
  const char *output_file = nullptr;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (strcmp(argv[i], "--version") == 0) {
      printf("tlsfinfo %s\n", TLSFINFO_VERSION);
      return 0;
    } else if (strcmp(argv[i], "--output") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsfinfo: --output requires an argument\n");
        return 1;
      }
      output_file = argv[i];
    } else if (argv[i][0] == '-') {
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

  FILE *fp = cli_open_input(input_file, "tlsfinfo");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfinfo");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  FILE *out = cli_open_output(output_file, "tlsfinfo");
  if (!out) {
    spec_free(spec);
    return 1;
  }

  // No expansion: tlsfinfo reports the raw specification metadata.
  int rc = 0;
  switch (sel) {
  case SEL_TITLE:
    fprintf(out, "%s\n", spec->info.title ? spec->info.title : "");
    break;
  case SEL_DESCRIPTION:
    fprintf(out, "%s\n", spec->info.description ? spec->info.description : "");
    break;
  case SEL_SEMANTICS:
    fprintf(out, "%s\n", semantics_str(spec->info.semantics));
    break;
  case SEL_TARGET:
    fprintf(out, "%s\n", target_str(spec->info.target));
    break;
  case SEL_TAGS:
    print_tags(out, spec);
    break;
  case SEL_PARAMETERS:
    print_parameters(out, spec);
    break;
  case SEL_INFO:
    print_info_block(out, spec);
    break;
  case SEL_INPUTS:
    print_signals(out, spec->inputs, spec->input_count);
    break;
  case SEL_OUTPUTS:
    print_signals(out, spec->outputs, spec->output_count);
    break;
  case SEL_CHECK:
    // Parsing succeeded, so the spec conforms to the TLSF grammar.
    fprintf(out, "valid\n");
    break;
  case SEL_GR: {
    // GR(k) recognition needs the ground spec: expand with default parameters.
    if (expand(spec, nullptr, 0) != 0) {
      fprintf(stderr, "tlsfinfo: cannot expand spec for the GR(k) check\n");
      rc = 1;
      break;
    }
    // GR(k) over the full Boolean-combination-of-GF/FG liveness fragment.
    int level = gr_level(spec);
    if (level < 0)
      fprintf(out, "NOT in GR\n");
    else
      fprintf(out, "IN GR(%d)\n", level);
    break;
  }
  case SEL_NONE:
    print_all(out, spec);
    break;
  }

  if (output_file)
    fclose(out);
  spec_free(spec);
  return rc;
}
