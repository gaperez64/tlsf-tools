/// tlsf2tlsf — parse a TLSF spec, expand it to the basic fragment, re-emit.
///
/// Usage:
///   tlsf2tlsf [--param NAME=VALUE]... [--output FILE] FILE
///
/// Options:
///   --param NAME=VALUE  Override a TLSF parameter (may be repeated).
///   --output FILE       Write output to FILE (default: stdout).
///   --help

#define _GNU_SOURCE
#include "build_info.h"
#include "cli.h"
#include "tlsf/expand.h"
#include "tlsf/print_tlsf.h"
#include "tlsf/pipeline.h"
#include "tlsf/spec.h"

#include "spec_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *read_source(FILE *in, size_t *size) {
  size_t cap = 16384;
  char *bytes = malloc(cap);
  if (!bytes)
    return nullptr;
  *size = 0;
  for (;;) {
    if (*size == cap) {
      size_t next = cap * 2;
      char *grown = realloc(bytes, next);
      if (!grown) {
        free(bytes);
        return nullptr;
      }
      bytes = grown;
      cap = next;
    }
    size_t got = fread(bytes + *size, 1, cap - *size, in);
    *size += got;
    if (got == 0) {
      if (ferror(in)) {
        free(bytes);
        return nullptr;
      }
      break;
    }
  }
  return bytes;
}

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Reads FILE (or stdin) and writes expanded TLSF.\n"
      "  --basic                      fully expand to the basic fragment\n"
      "                               (no GLOBAL section). Default:\n"
      "                               substitute --param values and "
      "re-emit.\n"
      "  --fair-environment           require every Boolean input to visit\n"
      "                               both values infinitely often\n"
      "  --param NAME=VALUE           override a parameter (repeatable)\n"
      "  --overwrite-semantics VALUE  replace the spec's SEMANTICS\n"
      "  --overwrite-target VALUE     replace the spec's TARGET\n"
      "  --output FILE                write to FILE (default: stdout)\n"
      "  --provenance-out FILE        write source-origin expansion JSON\n"
      "  --version, --help\n",
      prog);
}

int main(int argc, char *argv[]) {
  const char *input_file = nullptr;
  const char *output_file = nullptr;
  const char *provenance_file = nullptr;
  bool to_basic = false;
  bool fair_environment = false;
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
    } else if (strcmp(argv[i], "--fair-environment") == 0) {
      fair_environment = true;
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
      if (!cli_parse_param(a, "tlsf2tlsf", &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(argv[i], "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(argv[i], "--provenance-out") == 0) {
      provenance_file = NEED_ARG();
      to_basic = true;
    } else if (strcmp(argv[i], "--version") == 0) {
      printf("tlsf2tlsf %s\n", TLSF_PROJECT_VERSION);
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

  if (provenance_file && output_file &&
      strcmp(provenance_file, output_file) == 0) {
    fprintf(stderr,
            "tlsf2tlsf: --output and --provenance-out need different files\n");
    return 1;
  }

  FILE *fp = cli_open_input(input_file, "tlsf2tlsf");
  if (!fp)
    return 1;
  char *source = nullptr;
  size_t source_size = 0;
  char source_sha256[65] = {0};
  if (provenance_file) {
    source = read_source(fp, &source_size);
    if (input_file)
      fclose(fp);
    if (source &&
        !tlsf_pipeline_source_sha256(source, source_size, source_sha256)) {
      free(source);
      source = nullptr;
    }
    if (!source || !(fp = fmemopen(source, source_size, "r"))) {
      fprintf(stderr, "tlsf2tlsf: cannot read or hash source\n");
      free(source);
      return 1;
    }
  }
  TlsfSpec *spec = spec_parse(fp, "tlsf2tlsf");
  if (input_file || provenance_file)
    fclose(fp);
  free(source);
  if (!spec)
    return 1;
  char *provenance_bytes = nullptr;
  size_t provenance_size = 0;
  FILE *provenance_stream = nullptr;

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
  if (fair_environment && semantics_is_finite(spec->info.semantics)) {
    fprintf(stderr,
            "tlsf2tlsf: --fair-environment is only available for infinite "
            "semantics\n");
    spec_free(spec);
    return 1;
  }
  if (fair_environment && !spec_add_fair_environment(spec)) {
    fprintf(stderr, "tlsf2tlsf: fair-environment transform failed (OOM)\n");
    spec_free(spec);
    return 1;
  }
  if (provenance_file) {
    provenance_stream = open_memstream(&provenance_bytes, &provenance_size);
    if (!provenance_stream) {
      spec_free(spec);
      return 1;
    }
  }

  if (to_basic) {
    // Full expansion to the basic fragment (drops the GLOBAL section).
    // The historical CLI accepts repeated names, with the last value winning.
    // The library entry point deliberately rejects duplicates for new callers.
    ParamOverride effective[64];
    size_t n_effective = 0;
    for (size_t i = 0; i < n_overrides; i++) {
      bool found = false;
      for (uint16_t j = 0; j < spec->param_count; j++)
        found |= strcmp(overrides[i].name, spec->params[j].name) == 0;
      if (!found) {
        fprintf(stderr, "expand: unknown parameter '%s'\n", overrides[i].name);
        if (provenance_stream)
          fclose(provenance_stream);
        free(provenance_bytes);
        spec_free(spec);
        return 1;
      }
      size_t j = 0;
      while (j < n_effective &&
             strcmp(effective[j].name, overrides[i].name) != 0)
        j++;
      if (j == n_effective)
        n_effective++;
      effective[j] = overrides[i];
    }
    TlsfPipelineError expand_error = {0};
    int expanded = tlsf_pipeline_expand_spec(
        spec, effective, n_effective, provenance_stream,
        provenance_file ? source_sha256 : nullptr, false, &expand_error);
    if (provenance_stream && fclose(provenance_stream) != 0)
      expanded = -1;
    provenance_stream = nullptr;
    if (expanded != 0) {
      if (strncmp(expand_error.message, "expand:", 7) == 0)
        fprintf(stderr, "%s\n", expand_error.message);
      free(provenance_bytes);
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

  if (provenance_file) {
    FILE *provenance_out = fopen(provenance_file, "wb");
    int write_status =
        provenance_out && fwrite(provenance_bytes, 1, provenance_size,
                                 provenance_out) == provenance_size
            ? 0
            : -1;
    int close_status = provenance_out ? fclose(provenance_out) : -1;
    free(provenance_bytes);
    if (write_status != 0 || close_status != 0) {
      fprintf(stderr, "tlsf2tlsf: cannot write provenance\n");
      spec_free(spec);
      return 1;
    }
  }

  spec_free(spec);
  return 0;
}
