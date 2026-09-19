/// tlsfsolve — in-process AIGER game solver (OxiDD BDD backend).
///
/// Reads an AIGER game (aag format, stdin or FILE) and emits the winning
/// strategy as an aag on stdout, exits 1 with "UNREALIZABLE" on stderr if the
/// controller player loses, or exits 2 if OxiDD/profile resolution fails.
/// Profile resolution determines whether the objective is legacy ordinary
/// output 0, typed AIGER 1.9 bad properties, or the local GR(1) dialect.
///
/// Usage:
///   tlsfsolve [FILE]     (FILE = aag game; omit or use "-" for stdin)
///   tlsfsolve --help

#include "tlsf/aiger.h"
#include "tlsf/build_info.h"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/safety_oxidd.h"

#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  PROFILE_AUTO = 0,
  PROFILE_LEGACY_SAFETY,
  PROFILE_GR1,
  PROFILE_MULTI_SAFETY,
} GameProfile;

static const char *profile_name(GameProfile p) {
  switch (p) {
  case PROFILE_AUTO:
    return "auto";
  case PROFILE_LEGACY_SAFETY:
    return "legacy-safety";
  case PROFILE_GR1:
    return "gr1";
  case PROFILE_MULTI_SAFETY:
    return "multi-safety";
  }
  return "unknown";
}

static bool parse_profile(const char *s, GameProfile *out) {
  if (!strcmp(s, "auto"))
    *out = PROFILE_AUTO;
  else if (!strcmp(s, "legacy-safety"))
    *out = PROFILE_LEGACY_SAFETY;
  else if (!strcmp(s, "gr1"))
    *out = PROFILE_GR1;
  else if (!strcmp(s, "multi-safety"))
    *out = PROFILE_MULTI_SAFETY;
  else
    return false;
  return true;
}

static bool parse_size_value(const char *s, size_t *out) {
  if (!s || *s == '-' || *s == '\0')
    return false;
  errno = 0;
  char *end = nullptr;
  unsigned long long v = strtoull(s, &end, 10);
  if (errno || end == s || *end != '\0' || v == 0 || v > SIZE_MAX)
    return false;
  *out = (size_t)v;
  return true;
}

static const char *option_value(int *i, int argc, char **argv, const char *arg,
                                const char *name) {
  size_t n = strlen(name);
  if (strncmp(arg, name, n) == 0 && arg[n] == '=')
    return arg + n + 1;
  if (strcmp(arg, name) == 0 && *i + 1 < argc)
    return argv[++*i];
  return nullptr;
}

static bool has_controllable_input(const Aig *game) {
  for (uint32_t i = 0; i < aig_num_inputs(game); i++) {
    if (is_controllable(aig_input_name(game, i, nullptr)))
      return true;
  }
  return false;
}

static bool justice_records_are_singleton(const Aig *game) {
  for (uint32_t j = 0; j < aig_num_justice(game); j++) {
    uint32_t n = 0;
    aig_justice_at(game, j, nullptr, &n);
    if (n != 1)
      return false;
  }
  return true;
}

static bool validate_supported_resets(const Aig *game, const char *prog) {
  for (uint32_t j = 0; j < aig_num_latches(game); j++) {
    uint32_t cur, reset;
    aig_latch_at(game, j, &cur, nullptr, &reset);
    if (reset == 0 || reset == 1)
      continue;
    if (reset == cur) {
      fprintf(stderr,
              "%s: unsupported uninitialized latch reset at latch %u "
              "(literal %u)\n",
              prog, j, reset);
    } else {
      fprintf(stderr,
              "%s: unsupported nonconstant latch reset at latch %u "
              "(literal %u)\n",
              prog, j, reset);
    }
    return false;
  }
  return true;
}

static void print_counts(FILE *out, const Aig *game) {
  fprintf(out, "I=%u,L=%u,O=%u,A=%u,B=%u,C=%u,J=%u,F=%u", aig_num_inputs(game),
          aig_num_latches(game), aig_num_outputs(game), aig_num_ands(game),
          aig_num_bad(game), aig_num_constraints(game), aig_num_justice(game),
          aig_num_fairness(game));
}

static bool validate_explicit_profile(const Aig *game, GameProfile p,
                                      const char *prog) {
  uint32_t O = aig_num_outputs(game), B = aig_num_bad(game);
  uint32_t C = aig_num_constraints(game), J = aig_num_justice(game);
  uint32_t F = aig_num_fairness(game);
  bool ok = false;
  switch (p) {
  case PROFILE_LEGACY_SAFETY:
    ok = O == 1 && B == 0 && C == 0 && J == 0 && F == 0;
    break;
  case PROFILE_GR1:
    ok = O == 1 && B == 0 && C == 0 && J > 0 &&
         justice_records_are_singleton(game);
    break;
  case PROFILE_MULTI_SAFETY:
    ok = B > 0 && C == 0 && J == 0 && F == 0;
    break;
  case PROFILE_AUTO:
    ok = false;
    break;
  }
  if (!ok) {
    fprintf(stderr, "%s: --game-profile=%s is incompatible with raw counts ",
            prog, profile_name(p));
    print_counts(stderr, game);
    if (p == PROFILE_GR1 && J > 0 && !justice_records_are_singleton(game))
      fprintf(stderr, " (non-singleton justice records are preserved but not "
                      "supported by this GR(1) solver)");
    fputc('\n', stderr);
  }
  return ok;
}

static bool resolve_profile(const Aig *game, GameProfile requested,
                            GameProfile *resolved, const char *prog) {
  if (requested != PROFILE_AUTO) {
    if (!validate_explicit_profile(game, requested, prog))
      return false;
    *resolved = requested;
    return true;
  }

  uint32_t O = aig_num_outputs(game), B = aig_num_bad(game);
  uint32_t C = aig_num_constraints(game), J = aig_num_justice(game);
  uint32_t F = aig_num_fairness(game);
  if (O == 1 && B == 0 && C == 0 && J == 0 && F == 0) {
    *resolved = PROFILE_LEGACY_SAFETY;
    return true;
  }
  if (O == 1 && B == 0 && C == 0 && J > 0 && has_controllable_input(game) &&
      justice_records_are_singleton(game)) {
    *resolved = PROFILE_GR1;
    return true;
  }

  fprintf(stderr, "%s: cannot infer synthesis game profile from raw counts ",
          prog);
  print_counts(stderr, game);
  if (C > 0) {
    fprintf(stderr, "; typed constraints are parsed but unsupported as "
                    "synthesis assumptions");
  } else if (B > 0) {
    fprintf(stderr, "; typed bad properties require explicit "
                    "--game-profile=multi-safety");
  } else if (J > 0 || F > 0) {
    fprintf(stderr, "; AIGER 1.9 liveness/fairness needs explicit "
                    "--game-profile=gr1 when tlsf-tools game semantics are "
                    "intended");
  } else {
    fprintf(stderr, "; legacy safety requires exactly one ordinary output");
  }
  fputc('\n', stderr);
  return false;
}

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE]\n"
          "Solve an AIGER safety or GR(1) game with the in-process OxiDD BDD "
          "solver.\n"
          "  FILE   aag game file (default: stdin; use '-' for stdin)\n"
          "  --game-profile=auto|legacy-safety|gr1|multi-safety\n"
          "  --oxidd-nodes N        BDD node arena capacity\n"
          "  --oxidd-cache N        BDD apply-cache capacity\n"
          "  --oxidd-gc auto|pressure\n"
          "  --oxidd-gc-threshold PERCENT\n"
          "  -v, --verbose          diagnostic trace (requires non-NDEBUG)\n"
          "Exit 0: realizable — writes strategy aag to stdout.\n"
          "Exit 1: UNREALIZABLE — writes message to stderr.\n"
          "Exit 2: input, usage, or OxiDD solver failure.\n"
          "  --version, --help\n",
          prog);
}

int main(int argc, char **argv) {
  const char *path = nullptr;
  GameProfile requested_profile = PROFILE_AUTO, resolved_profile = PROFILE_AUTO;
  OxiddSolveOptions opts = oxidd_solve_options_default();
  for (int i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "--help") || !strcmp(arg, "-h")) {
      usage(argv[0]);
      return 0;
    }
#ifndef NDEBUG
    if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose")) {
      opts.verbosity++;
      continue;
    }
    if (!strcmp(arg, "-vv")) {
      opts.verbosity += 2;
      continue;
    }
#else
    if (!strcmp(arg, "-v") || !strcmp(arg, "-vv") ||
        !strcmp(arg, "--verbose")) {
      fprintf(stderr,
              "%s: verbose diagnostics compiled out; rebuild with "
              "-Db_ndebug=false\n",
              argv[0]);
      return 2;
    }
#endif
    if (!strcmp(arg, "--version")) {
      printf("tlsfsolve %s oxidd=%s research=%s simd=%s diagnostics=%s\n",
             TLSF_PROJECT_VERSION, tlsf_build_oxidd(), tlsf_build_research(),
             tlsf_build_simd(),
#ifndef NDEBUG
             "yes"
#else
             "no"
#endif
      );
      return 0;
    }
    const char *val = option_value(&i, argc, argv, arg, "--game-profile");
    if (val) {
      if (!parse_profile(val, &requested_profile)) {
        fprintf(stderr, "%s: bad --game-profile '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-nodes");
    if (val) {
      if (!parse_size_value(val, &opts.node_cap)) {
        fprintf(stderr, "%s: bad --oxidd-nodes '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-cache");
    if (val) {
      if (!parse_size_value(val, &opts.cache_cap)) {
        fprintf(stderr, "%s: bad --oxidd-cache '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-gc");
    if (val) {
      if (!strcmp(val, "auto")) {
        opts.gc_mode = OXIDD_GC_AUTO;
      } else if (!strcmp(val, "pressure")) {
        opts.gc_mode = OXIDD_GC_PRESSURE;
      } else {
        fprintf(stderr, "%s: bad --oxidd-gc '%s'\n", argv[0], val);
        return 2;
      }
      continue;
    }
    val = option_value(&i, argc, argv, arg, "--oxidd-gc-threshold");
    if (val) {
      size_t parsed = 0;
      if (!parse_size_value(val, &parsed) || parsed > 100) {
        fprintf(stderr, "%s: bad --oxidd-gc-threshold '%s'\n", argv[0], val);
        return 2;
      }
      opts.gc_threshold_percent = (unsigned)parsed;
      continue;
    }
    if (!strcmp(arg, "-")) {
      path = nullptr;
    } else if (arg[0] != '-') {
      if (path) {
        fprintf(stderr, "%s: more than one input file\n", argv[0]);
        return 2;
      }
      path = arg;
    } else {
      fprintf(stderr, "%s: unknown option '%s'\n", argv[0], arg);
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

  if (!resolve_profile(game, requested_profile, &resolved_profile, argv[0]) ||
      !validate_supported_resets(game, argv[0])) {
    aig_free(game);
    return 2;
  }

  oxidd_trace(&opts, "resolve_profile", "game",
              ",\"profile_requested\":\"%s\",\"profile\":\"%s\","
              "\"outputs\":%u,\"bad\":%u,\"constraints\":%u,"
              "\"justice\":%u,\"fairness\":%u,\"controllable_input\":%s",
              profile_name(requested_profile), profile_name(resolved_profile),
              aig_num_outputs(game), aig_num_bad(game),
              aig_num_constraints(game), aig_num_justice(game),
              aig_num_fairness(game),
              has_controllable_input(game) ? "true" : "false");

  if (resolved_profile == PROFILE_MULTI_SAFETY) {
    opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR;
  } else {
    opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT;
    opts.safety_output_index = 0;
  }

  int unreal = 0;
  Aig *strat = resolved_profile == PROFILE_GR1
                   ? solve_gr1_oxidd_ex(game, &unreal, &opts)
                   : solve_safety_oxidd_ex(game, &unreal, &opts);

  if (!strat) {
    if (unreal) {
      fprintf(stderr, "UNREALIZABLE\n");
      return 1;
    }
    fprintf(stderr, "tlsfsolve: OxiDD solver failed\n");
    return 2;
  }

  aig_write_aag(stdout, strat);
  aig_free(strat);
  return 0;
}
