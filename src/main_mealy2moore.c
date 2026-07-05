/// mealy2moore - delay AIGER controller outputs by one step.
///
/// Reads an ASCII AIGER strategy that may implement a Mealy controller
/// (outputs depend on current inputs) and emits a Moore-style controller where
/// each output is driven by a latch.  The initial output valuation is obtained
/// by evaluating the original output cone at the original latch resets and an
/// arbitrary first-step input valuation, currently all inputs false.

#include "tlsf/aiger.h"
#include "tlsf/build_info.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [FILE]\n"
          "Convert an ASCII AIGER Mealy strategy to a Moore-style strategy by "
          "delaying outputs one step.\n"
          "  FILE   aag strategy file (default: stdin; use '-' for stdin)\n"
          "First-step inputs are fixed to false when choosing output latch "
          "resets.\n"
          "  --version, --help\n",
          prog);
}

static uint32_t remap_lit(uint32_t lit, const uint32_t *litmap) {
  if (lit < 2)
    return lit;
  uint32_t mapped = litmap[lit / 2];
  return (lit & 1u) ? aig_not(mapped) : mapped;
}

static bool eval_lit(uint32_t lit, const bool *value) {
  if (lit == AIG_FALSE)
    return false;
  if (lit == AIG_TRUE)
    return true;
  bool v = value[lit / 2];
  return (lit & 1u) ? !v : v;
}

static bool input_value_for_reset(const char *name) {
  (void)name;
  return false;
}

static Aig *mealy_to_moore(const Aig *src) {
  uint32_t nin = aig_num_inputs(src);
  uint32_t nlat = aig_num_latches(src);
  uint32_t nand = aig_num_ands(src);
  uint32_t nout = aig_num_outputs(src);
  uint32_t maxvar = 0;

  for (uint32_t i = 0; i < nin; i++) {
    uint32_t lit;
    (void)aig_input_name(src, i, &lit);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < nlat; i++) {
    uint32_t cur;
    aig_latch_at(src, i, &cur, nullptr, nullptr);
    if (cur / 2 > maxvar)
      maxvar = cur / 2;
  }
  for (uint32_t i = 0; i < nand; i++) {
    uint32_t lhs;
    aig_and_at(src, i, &lhs, nullptr, nullptr);
    if (lhs / 2 > maxvar)
      maxvar = lhs / 2;
  }

  uint32_t *litmap = calloc((size_t)maxvar + 1u, sizeof *litmap);
  bool *reset_value = calloc((size_t)maxvar + 1u, sizeof *reset_value);
  if (!litmap || !reset_value) {
    free(litmap);
    free(reset_value);
    return nullptr;
  }

  Aig *dst = aig_new();
  if (!dst) {
    free(litmap);
    free(reset_value);
    return nullptr;
  }

  for (uint32_t i = 0; i < nin; i++) {
    uint32_t lit;
    const char *name = aig_input_name(src, i, &lit);
    char fallback[64];
    if (!name || !*name) {
      snprintf(fallback, sizeof fallback, "mealy2moore_input_%u", i);
      name = fallback;
    }
    uint32_t dlit = aig_input(dst, name);
    litmap[lit / 2] = dlit;
    reset_value[lit / 2] = input_value_for_reset(name);
  }
  for (uint32_t i = 0; i < nlat; i++) {
    uint32_t cur, reset;
    aig_latch_at(src, i, &cur, nullptr, &reset);
    uint32_t dlit = aig_latch(dst, AIG_FALSE, reset);
    litmap[cur / 2] = dlit;
    reset_value[cur / 2] = reset != 0;
  }
  for (uint32_t i = 0; i < nand; i++) {
    uint32_t lhs, r0, r1;
    aig_and_at(src, i, &lhs, &r0, &r1);
    uint32_t dlit = aig_and(dst, remap_lit(r0, litmap), remap_lit(r1, litmap));
    litmap[lhs / 2] = dlit;
    reset_value[lhs / 2] =
        eval_lit(r0, reset_value) && eval_lit(r1, reset_value);
  }
  for (uint32_t i = 0; i < nlat; i++) {
    uint32_t cur, next;
    aig_latch_at(src, i, &cur, &next, nullptr);
    if (!aig_set_latch_next(dst, remap_lit(cur, litmap),
                            remap_lit(next, litmap))) {
      aig_free(dst);
      free(litmap);
      free(reset_value);
      return nullptr;
    }
  }
  for (uint32_t i = 0; i < nout; i++) {
    uint32_t lit;
    const char *name = aig_output_at(src, i, &lit);
    uint32_t delayed = aig_latch(dst, remap_lit(lit, litmap),
                                 eval_lit(lit, reset_value) ? 1u : 0u);
    aig_set_output(dst, name, delayed);
  }

  free(litmap);
  free(reset_value);
  return dst;
}

int main(int argc, char **argv) {
  const char *path = nullptr;
  bool have_input = false;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
      usage(argv[0]);
      return 0;
    }
    if (!strcmp(argv[i], "--version")) {
      printf("mealy2moore %s\n", TLSF_PROJECT_VERSION);
      return 0;
    }
    if (!strcmp(argv[i], "-")) {
      if (have_input) {
        fprintf(stderr, "%s: multiple input files not supported\n", argv[0]);
        return 2;
      }
      path = nullptr;
      have_input = true;
    } else if (argv[i][0] != '-') {
      if (have_input) {
        fprintf(stderr, "%s: multiple input files not supported\n", argv[0]);
        return 2;
      }
      path = argv[i];
      have_input = true;
    } else {
      fprintf(stderr, "%s: unknown option '%s'\n", argv[0], argv[i]);
      usage(argv[0]);
      return 2;
    }
  }

  FILE *in = path ? fopen(path, "r") : stdin;
  if (!in) {
    perror(path);
    return 2;
  }

  Aig *src = aig_read_aag(in);
  if (path)
    fclose(in);
  if (!src) {
    fprintf(stderr, "%s: failed to parse aag strategy\n", argv[0]);
    return 2;
  }

  Aig *dst = mealy_to_moore(src);
  aig_free(src);
  if (!dst) {
    fprintf(stderr, "%s: failed to convert strategy\n", argv[0]);
    return 2;
  }

  aig_write_aag(stdout, dst);
  aig_free(dst);
  return 0;
}
