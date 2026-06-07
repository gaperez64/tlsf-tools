/// tlsf2tlsf — parse a TLSF spec, expand it to the basic fragment, re-emit.
///
/// Usage:
///   tlsf2tlsf [--param NAME=VALUE]... [--output FILE] FILE
///
/// Options:
///   --param NAME=VALUE  Override a TLSF parameter (may be repeated).
///   --output FILE       Write output to FILE (default: stdout).
///   --help

#include "tlsf/cli.h"
#include "tlsf/expand.h"
#include "tlsf/print_tlsf.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE]\n"
          "Reads FILE (or stdin) and writes expanded TLSF.\n"
          "  --basic                      fully expand to the basic fragment\n"
          "                               (no GLOBAL section). Default:\n"
          "                               substitute --param values and "
          "re-emit.\n"
          "  --param NAME=VALUE           override a parameter (repeatable)\n"
          "  --overwrite-semantics VALUE  replace the spec's SEMANTICS\n"
          "  --overwrite-target VALUE     replace the spec's TARGET\n"
          "  --output FILE                write to FILE (default: stdout)\n"
          "  --version, --help\n",
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

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsf2tlsf: %s requires an argument\n",      \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--basic") == 0) {
      to_basic = true;
    } else if (strcmp(argv[i], "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(argv[i], "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(argv[i], "--param") == 0) {
      const char *a = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsf2tlsf: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(a, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(argv[i], "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(argv[i], "--version") == 0) {
      printf("tlsf2tlsf %s\n", TLSF_VERSION);
      return 0;
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
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsf2tlsf");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsf2tlsf");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

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
  if (!spec_validate_semantics(spec, "tlsf2tlsf")) {
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

  FILE *out = cli_open_output(output_file, "tlsf2tlsf");
  if (!out) {
    spec_free(spec);
    return 1;
  }
  print_tlsf(out, spec, /*include_global=*/!to_basic);
  if (output_file)
    fclose(out);

  spec_free(spec);
  return 0;
}
