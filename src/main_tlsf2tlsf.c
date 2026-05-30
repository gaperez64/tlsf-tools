/// tlsf2tlsf — parse a TLSF spec, expand it to the basic fragment, re-emit.
///
/// Usage:
///   tlsf2tlsf [--param NAME=VALUE]... [--output FILE] FILE
///
/// Options:
///   --param NAME=VALUE  Override a TLSF parameter (may be repeated).
///   --output FILE       Write output to FILE (default: stdout).
///   --help

#include "tlsf/expand.h"
#include "tlsf/print_tlsf.h"
#include "tlsf/spec.h"

#include "tlsf_parse.h"
#include "tlsf_lex.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [--basic] [--param N=V]... [--output FILE] FILE\n"
          "  --basic        fully expand to the basic TLSF fragment (no\n"
          "                 GLOBAL section). Default: substitute parameter\n"
          "                 values and re-emit the spec unchanged otherwise.\n"
          "  --param N=V    override parameter N with value V (repeatable)\n"
          "  -os, --overwrite-semantics V  replace the spec's SEMANTICS\n"
          "  -ot, --overwrite-target V     replace the spec's TARGET\n"
          "  --output FILE  write to FILE instead of stdout\n",
          prog);
}

static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsf2tlsf: bad --param '%s'\n", s);
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
    fprintf(stderr, "tlsf2tlsf: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

int main(int argc, char *argv[]) {
  const char *input_file = nullptr;
  const char *output_file = nullptr;
  bool to_basic = false;
  const char *os_arg = nullptr;
  const char *ot_arg = nullptr;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--basic") == 0) {
      to_basic = true;
    } else if (strcmp(argv[i], "--overwrite-semantics") == 0 ||
               strcmp(argv[i], "-os") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2tlsf: %s requires an argument\n", argv[i - 1]);
        return 1;
      }
      os_arg = argv[i];
    } else if (strcmp(argv[i], "--overwrite-target") == 0 ||
               strcmp(argv[i], "-ot") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2tlsf: %s requires an argument\n", argv[i - 1]);
        return 1;
      }
      ot_arg = argv[i];
    } else if (strcmp(argv[i], "--param") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2tlsf: --param requires an argument\n");
        return 1;
      }
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsf2tlsf: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(argv[i], &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(argv[i], "--output") == 0) {
      if (++i >= argc) {
        fprintf(stderr, "tlsf2tlsf: --output requires an argument\n");
        return 1;
      }
      output_file = argv[i];
    } else if (strcmp(argv[i], "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (argv[i][0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsf2tlsf: multiple input files not supported\n");
        return 1;
      }
      input_file = argv[i];
    } else {
      fprintf(stderr, "tlsf2tlsf: unknown option '%s'\n", argv[i]);
      usage(argv[0]);
      return 1;
    }
  }

  if (!input_file) {
    fprintf(stderr, "tlsf2tlsf: no input file\n");
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
    fprintf(stderr, "tlsf2tlsf: out of memory\n");
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
    fprintf(stderr, "tlsf2tlsf: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsf2tlsf: invalid target '%s' (expect Mealy or Moore)\n",
            ot_arg);
    spec_free(spec);
    return 1;
  }

  if (to_basic) {
    // Full expansion to the basic fragment (drops the GLOBAL section).
    if (expand(spec, overrides, n_overrides) != 0) {
      spec_free(spec);
      return 1;
    }
  } else {
    // Plain parameter substitution: apply overrides to the PARAMETERS values
    // and re-emit the spec (GLOBAL section preserved), without expanding.
    for (size_t i = 0; i < n_overrides; i++) {
      const char *iname = intern(spec->intern, overrides[i].name);
      bool found = false;
      for (uint16_t j = 0; j < spec->param_count; j++) {
        if (spec->params[j].name == iname) {
          spec->params[j].value = overrides[i].value;
          spec->params[j].has_default = true;
          found = true;
          break;
        }
      }
      if (!found) {
        fprintf(stderr, "tlsf2tlsf: unknown parameter '%s'\n",
                overrides[i].name);
        spec_free(spec);
        return 1;
      }
    }
  }

  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  FILE *out = stdout;
  if (output_file) {
    out = fopen(output_file, "w");
    if (!out) {
      perror(output_file);
      spec_free(spec);
      return 1;
    }
  }

  print_tlsf(out, spec, /*include_global=*/!to_basic);

  if (output_file)
    fclose(out);

  spec_free(spec);
  return 0;
}
