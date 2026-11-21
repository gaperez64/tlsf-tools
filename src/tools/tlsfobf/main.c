/// tlsfobf — write a semantically equivalent TLSF spec without name-like or
/// order-like cues, for benchmarking solvers' independence of them.
///
/// Usage:
///   tlsfobf [--mode rename|reorder|all] [--seed N] [--map FILE]
///           [--param NAME=VALUE]... [--output FILE] [FILE]
///
/// The output is verified against the input (see tlsf/obfuscate.h); when the
/// check fails nothing is written and the exit status is 1.

#include "build_info.h"
#include "cli.h"
#include "tlsf/obfuscate.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Reads FILE (or stdin) and writes an equivalent TLSF spec with neutral\n"
      "names and/or permuted order, after checking that its expansion equals\n"
      "the input's.\n"
      "  --mode rename|reorder|all  what to change (default: all)\n"
      "      rename   neutral identifiers; INFO text neutral, TAGS dropped\n"
      "      reorder  permute declarations, section formulas, definitions,\n"
      "               and && / || operands\n"
      "  --seed N                   seed for names and permutations (default "
      "0)\n"
      "  --map FILE                 write the renaming as TSV\n"
      "  --param NAME=VALUE         override a parameter (repeatable)\n"
      "  --output FILE              write to FILE (default: stdout)\n"
      "  --version, --help\n",
      prog);
}

static char *read_all(FILE *in, size_t *size) {
  size_t cap = 16384;
  char *bytes = malloc(cap);
  if (!bytes)
    return nullptr;
  *size = 0;
  for (;;) {
    if (*size == cap) {
      char *grown = realloc(bytes, cap * 2);
      if (!grown) {
        free(bytes);
        return nullptr;
      }
      bytes = grown;
      cap *= 2;
    }
    size_t got = fread(bytes + *size, 1, cap - *size, in);
    *size += got;
    if (got == 0) {
      if (ferror(in)) {
        free(bytes);
        return nullptr;
      }
      return bytes;
    }
  }
}

static bool parse_seed(const char *text, uint64_t *out) {
  char *end = nullptr;
  errno = 0;
  unsigned long long value = strtoull(text, &end, 10);
  if (errno || end == text || *end || text[0] == '-')
    return false;
  *out = value;
  return true;
}

int main(int argc, char *argv[]) {
  const char *input_file = nullptr;
  const char *output_file = nullptr;
  const char *map_file = nullptr;
  TlsfObfuscateOptions options = {.mode = TLSF_OBFUSCATE_ALL};
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc                                                                 \
       ? (fprintf(stderr, "tlsfobf: %s requires an argument\n", argv[i - 1]),  \
          exit(1), nullptr)                                                    \
       : argv[i])

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--mode") == 0) {
      const char *mode = NEED_ARG();
      if (strcmp(mode, "rename") == 0)
        options.mode = TLSF_OBFUSCATE_RENAME;
      else if (strcmp(mode, "reorder") == 0)
        options.mode = TLSF_OBFUSCATE_REORDER;
      else if (strcmp(mode, "all") == 0)
        options.mode = TLSF_OBFUSCATE_ALL;
      else {
        fprintf(stderr,
                "tlsfobf: invalid mode '%s' (expect rename, reorder or all)\n",
                mode);
        return 1;
      }
    } else if (strcmp(argv[i], "--seed") == 0) {
      const char *seed = NEED_ARG();
      if (!parse_seed(seed, &options.seed)) {
        fprintf(stderr, "tlsfobf: invalid seed '%s'\n", seed);
        return 1;
      }
    } else if (strcmp(argv[i], "--map") == 0) {
      map_file = NEED_ARG();
    } else if (strcmp(argv[i], "--param") == 0) {
      char *a = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfobf: too many --param overrides\n");
        return 1;
      }
      if (!cli_parse_param(a, "tlsfobf", &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(argv[i], "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(argv[i], "--test-fault") == 0) {
      // Testing only: corrupt the transform so the self-check must fail.
      options.test_fault = (unsigned)atoi(NEED_ARG());
    } else if (strcmp(argv[i], "--version") == 0) {
      printf("tlsfobf %s\n", TLSF_PROJECT_VERSION);
      return 0;
    } else if (strcmp(argv[i], "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (argv[i][0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfobf: multiple input files not supported\n");
        return 1;
      }
      input_file = argv[i];
    } else {
      fprintf(stderr, "tlsfobf: unknown option '%s'\n", argv[i]);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG
  if (map_file && output_file && strcmp(map_file, output_file) == 0) {
    fprintf(stderr, "tlsfobf: --output and --map need different files\n");
    return 1;
  }

  FILE *in = cli_open_input(input_file, "tlsfobf");
  if (!in)
    return 1;
  size_t size = 0;
  char *source = read_all(in, &size);
  if (input_file)
    fclose(in);
  if (!source) {
    fprintf(stderr, "tlsfobf: cannot read input\n");
    return 1;
  }
  options.overrides = overrides;
  options.n_overrides = n_overrides;
  TlsfObfuscateResult result;
  TlsfObfuscateStatus status = tlsf_obfuscate(source, size, &options, &result);
  free(source);
  if (status != TLSF_OBFUSCATE_OK) {
    fprintf(stderr, "tlsfobf: %s\n", result.message);
    tlsf_obfuscate_result_clear(&result);
    return 1;
  }

  // Write the map first: a consumer that sees the spec can rely on the map.
  if (map_file) {
    FILE *map = fopen(map_file, "w");
    bool ok = map && tlsf_obfuscate_write_map(map, &result);
    if (map && fclose(map) != 0)
      ok = false;
    if (!ok) {
      fprintf(stderr, "tlsfobf: cannot write map '%s'\n", map_file);
      tlsf_obfuscate_result_clear(&result);
      return 1;
    }
  }
  FILE *out = cli_open_output(output_file, "tlsfobf");
  if (!out) {
    tlsf_obfuscate_result_clear(&result);
    return 1;
  }
  bool written = fwrite(result.text, 1, result.size, out) == result.size;
  if (output_file ? fclose(out) != 0 : fflush(out) != 0)
    written = false;
  tlsf_obfuscate_result_clear(&result);
  if (!written) {
    fprintf(stderr, "tlsfobf: cannot write output\n");
    return 1;
  }
  return 0;
}
