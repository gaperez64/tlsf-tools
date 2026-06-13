/// tlsfsolve — in-process AIGER game solver (OxiDD BDD backend).
///
/// Reads an AIGER game (aag format, stdin or FILE) and emits the winning
/// strategy as an aag on stdout, or exits 1 with "UNREALIZABLE" on stderr if
/// the controller player loses.  The game format is the same as AbsSynthe's:
/// controllable inputs prefixed "controllable_", latches with reset values,
/// "bad" output for the unsafe predicate.  GR(1) games additionally carry
/// justice[] and fair[] records (AIGER 1.9); these are auto-detected and routed
/// to the GR(1) tri-nested-fixpoint solver.
///
/// Usage:
///   tlsfsolve [FILE]     (FILE = aag game; omit or use "-" for stdin)
///   tlsfsolve --help

#include "tlsf/aiger.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"

#include <stdio.h>
#include <string.h>

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [FILE]\n"
          "Solve an AIGER safety or GR(1) game with the in-process OxiDD BDD "
          "solver.\n"
          "  FILE   aag game file (default: stdin; use '-' for stdin)\n"
          "Exit 0: realizable — writes strategy aag to stdout.\n"
          "Exit 1: UNREALIZABLE — writes message to stderr.\n"
          "  --help\n",
          prog);
}

int main(int argc, char **argv) {
  const char *path = nullptr;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
      usage(argv[0]);
      return 0;
    }
    if (!strcmp(argv[i], "-")) {
      path = nullptr;
    } else if (argv[i][0] != '-') {
      path = argv[i];
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

  Aig *game = aig_read_aag(in);
  if (path)
    fclose(in);
  if (!game) {
    fprintf(stderr, "%s: failed to parse aag game\n", argv[0]);
    return 2;
  }

  int unreal = 0;
  bool is_gr1 = aig_num_justice(game) > 0 || aig_num_fairness(game) > 0;
  Aig *strat =
      is_gr1 ? solve_gr1_oxidd(game, &unreal) : solve_safety_oxidd(game, &unreal);

  if (!strat) {
    fprintf(stderr, "UNREALIZABLE\n");
    return 1;
  }

  aig_write_aag(stdout, strat);
  aig_free(strat);
  return 0;
}
