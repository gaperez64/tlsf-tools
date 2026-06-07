/// tlsfcompose — a self-contained decomposed-synthesis plan.
///
/// Runs cover -> recognize -> certify -> compose, then emits everything needed
/// to synthesize the whole spec by decomposition: the exact *combinational*
/// controllers it already certified (`o := value`), and the rest of the spec as
/// independent residual clusters (output-disjoint, so `E -> AND Gi == AND
/// (E -> Gi)`), one LTL job each.  With --output-dir it also writes a
/// compose.sh that runs `ltlsynt` per cluster.  The spec is realizable iff
/// every cluster is; a full controller is the emitted controllers plus one per
/// cluster.
///
/// Text plans do not spawn processes: backend calls live in compose.sh.
/// `--aiger` runs the selected synthesis backend immediately for each cluster.

// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/aiger.h"
#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/recognize.h"
#include "tlsf/residual.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include <fcntl.h>
#include <spawn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

#define TLSF_VERSION "0.1.0"
#define ABSSYNTHE_CONTROLLABLE_PREFIX "controllable_"

// Render a (Boolean/LTL) node to a heap string in the ltlxba/ltl dialect, with
// any trailing newline stripped (for ltlsynt --formula=).
static char *ltl_string(const Node *n, LtlFormat fmt, bool finite) {
  char *buf = nullptr;
  size_t sz = 0;
  FILE *ms = open_memstream(&buf, &sz);
  if (!ms)
    return nullptr;
  print_ltl(ms, n, fmt, /*full_parens=*/false, finite);
  fclose(ms);
  if (sz && buf[sz - 1] == '\n')
    buf[sz - 1] = '\0';
  return buf;
}

// Synthesize one cluster with ltlsynt --aiger; returns its strategy AIG (caller
// frees), nullptr on failure (and sets *unreal=1 if ltlsynt said UNREALIZABLE).
static Aig *run_ltlsynt(const char *prog, const char *ins, const char *outs,
                        const char *ltl, int *unreal) {
  *unreal = 0;
  FILE *cap = tmpfile();
  if (!cap)
    return nullptr;
  char *ai = malloc(strlen(ins) + 8), *ao = malloc(strlen(outs) + 9),
       *af = malloc(strlen(ltl) + 12);
  if (!ai || !ao || !af) {
    free(ai);
    free(ao);
    free(af);
    fclose(cap);
    return nullptr;
  }
  sprintf(ai, "--ins=%s", ins);
  sprintf(ao, "--outs=%s", outs);
  sprintf(af, "--formula=%s", ltl);
  char *argv[] = {(char *)prog, ai, ao, af, (char *)"--aiger", nullptr};
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  posix_spawn_file_actions_adddup2(&fa, fileno(cap), 1);
  pid_t pid;
  int rc = posix_spawnp(&pid, prog, &fa, nullptr, argv, environ);
  posix_spawn_file_actions_destroy(&fa);
  free(ai);
  free(ao);
  free(af);
  if (rc != 0) {
    fclose(cap);
    return nullptr; // ltlsynt not found / not executable
  }
  int status;
  waitpid(pid, &status, 0);
  char line[64];
  fseek(cap, 0, SEEK_SET);
  if (fgets(line, sizeof line, cap) && strncmp(line, "UNREALIZABLE", 12) == 0) {
    *unreal = 1;
    fclose(cap);
    return nullptr;
  }
  fseek(cap, 0, SEEK_SET); // aig_read_aag skips a leading REALIZABLE line
  Aig *g = aig_read_aag(cap);
  fclose(cap);
  return g;
}

static char *controllable_name(const char *name) {
  size_t p = strlen(ABSSYNTHE_CONTROLLABLE_PREFIX), n = strlen(name);
  char *out = malloc(p + n + 1);
  if (!out)
    return nullptr;
  int written =
      snprintf(out, p + n + 1, "%s%s", ABSSYNTHE_CONTROLLABLE_PREFIX, name);
  if (written < 0 || (size_t)written != p + n) {
    free(out);
    return nullptr;
  }
  return out;
}

static bool abssynthe_body_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
    return abssynthe_body_supported(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  default:
    return false;
  }
}

static bool abssynthe_global_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return abssynthe_body_supported(n->arg);
  case NODE_AND:
    return abssynthe_global_supported(n->lhs) &&
           abssynthe_global_supported(n->rhs);
  default:
    return false;
  }
}

static uint32_t abssynthe_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_X:
  case NODE_X_STRONG:
    return 1 + abssynthe_x_depth(n->arg);
  case NODE_NOT:
    return abssynthe_x_depth(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    uint32_t a = abssynthe_x_depth(n->lhs), b = abssynthe_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return 0;
  }
}

static uint32_t abssynthe_global_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_G:
    return abssynthe_x_depth(n->arg);
  case NODE_AND: {
    uint32_t a = abssynthe_global_x_depth(n->lhs);
    uint32_t b = abssynthe_global_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return UINT32_MAX;
  }
}

static bool abssynthe_eligible(const Node *root, bool finite) {
  if (finite)
    return false;
  if (root->kind == NODE_IMPL)
    return abssynthe_global_supported(root->lhs) &&
           abssynthe_global_x_depth(root->lhs) == 0 &&
           abssynthe_global_supported(root->rhs);
  return abssynthe_global_supported(root);
}

typedef struct {
  Aig *g;
  ConstraintCover *cov;
  uint32_t *hist; // (max_lag + 1) x AP table; UINT32_MAX = unavailable
  uint32_t ap_count;
} AbssyntheCompile;

static uint32_t hist_lit(const AbssyntheCompile *ctx, uint32_t lag,
                         uint32_t ap) {
  return ctx->hist[(lag * ctx->ap_count) + ap];
}

static void hist_set(AbssyntheCompile *ctx, uint32_t lag, uint32_t ap,
                     uint32_t lit) {
  ctx->hist[(lag * ctx->ap_count) + ap] = lit;
}

static uint32_t abssynthe_compile_at_lag(AbssyntheCompile *ctx, const Node *n,
                                         uint32_t lag) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_FALSE:
    return AIG_FALSE;
  case NODE_AP: {
    int32_t idx = ap_table_find(&ctx->cov->aps, n->name);
    if (idx < 0)
      return UINT32_MAX;
    return hist_lit(ctx, lag, (uint32_t)idx);
  }
  case NODE_NOT: {
    uint32_t a = abssynthe_compile_at_lag(ctx, n->arg, lag);
    return a == UINT32_MAX ? a : aig_not(a);
  }
  case NODE_X:
  case NODE_X_STRONG:
    if (lag == 0)
      return UINT32_MAX;
    return abssynthe_compile_at_lag(ctx, n->arg, lag - 1);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    uint32_t a = abssynthe_compile_at_lag(ctx, n->lhs, lag);
    uint32_t b = abssynthe_compile_at_lag(ctx, n->rhs, lag);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    switch (n->kind) {
    case NODE_AND:
      return aig_and(ctx->g, a, b);
    case NODE_OR:
      return aig_or(ctx->g, a, b);
    case NODE_IMPL:
      return aig_or(ctx->g, aig_not(a), b);
    default:
      return aig_and(ctx->g, aig_or(ctx->g, aig_not(a), b),
                     aig_or(ctx->g, a, aig_not(b)));
    }
  }
  default:
    return UINT32_MAX;
  }
}

static uint32_t abssynthe_compile_global_at_lag(AbssyntheCompile *ctx,
                                                const Node *n, uint32_t lag) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_G:
    return abssynthe_compile_at_lag(ctx, n->arg, lag);
  case NODE_AND: {
    uint32_t a = abssynthe_compile_global_at_lag(ctx, n->lhs, lag);
    uint32_t b = abssynthe_compile_global_at_lag(ctx, n->rhs, lag);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return aig_and(ctx->g, a, b);
  }
  default:
    return UINT32_MAX;
  }
}

static uint32_t abssynthe_compile_assumption_window(AbssyntheCompile *ctx,
                                                    const Node *assume,
                                                    uint32_t depth) {
  uint32_t ok = AIG_TRUE;
  for (uint32_t lag = 0; lag <= depth; lag++) {
    uint32_t at_lag = abssynthe_compile_global_at_lag(ctx, assume, lag);
    if (at_lag == UINT32_MAX)
      return UINT32_MAX;
    ok = aig_and(ctx->g, ok, at_lag);
  }
  return ok;
}

static Aig *build_abssynthe_game(ConstraintCover *cov, const bool *seen,
                                 const Node *root) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;
  const Node *assume = nullptr, *guarantee = root;
  if (root->kind == NODE_IMPL) {
    assume = root->lhs;
    guarantee = root->rhs;
  }
  uint32_t ass_depth = assume ? abssynthe_global_x_depth(assume) : 0;
  uint32_t gua_depth = abssynthe_global_x_depth(guarantee);
  if (ass_depth == UINT32_MAX || gua_depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t depth = ass_depth > gua_depth ? ass_depth : gua_depth;
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AbssyntheCompile ctx = {g, cov, hist, A ? A : 1};

  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !residual_signal_matches(cov, a, AP_FLAG_INPUT))
      continue;
    hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
  }
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    char *cname = controllable_name(ap_table_name(&cov->aps, a));
    if (!cname) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    hist_set(&ctx, 0, a, aig_input(g, cname));
    free(cname);
  }
  for (uint32_t d = 1; d <= depth; d++) {
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  }
  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);

  uint32_t gua_ok = abssynthe_compile_global_at_lag(&ctx, guarantee, depth);
  if (gua_ok == UINT32_MAX) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  uint32_t bad = aig_and(g, valid, aig_not(gua_ok));
  if (assume) {
    uint32_t ass_ok = abssynthe_compile_global_at_lag(&ctx, assume, depth);
    if (ass_ok == UINT32_MAX) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    uint32_t ass_window_ok =
        abssynthe_compile_assumption_window(&ctx, assume, depth);
    if (ass_window_ok == UINT32_MAX) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    uint32_t violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
    uint32_t violated_next =
        aig_or(g, violated, aig_and(g, valid, aig_not(ass_ok)));
    if (!aig_set_latch_next(g, violated, violated_next)) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    bad = aig_and(g, bad, aig_and(g, aig_not(violated), ass_window_ok));
  }
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}

static bool abssynthe_strategy_has_outputs(Aig *g, ConstraintCover *cov,
                                           const bool *seen) {
  aig_remove_output(g, "bad");
  aig_strip_output_prefix(g, ABSSYNTHE_CONTROLLABLE_PREFIX);
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    if (!aig_has_output(g, ap_table_name(&cov->aps, a)))
      return false;
  }
  return true;
}

static void cleanup_abssynthe_tmp(const char *dir, const char *game,
                                  const char *strat) {
  if (game)
    unlink(game);
  if (strat)
    unlink(strat);
  if (dir)
    rmdir(dir);
}

// Synthesize one safety cluster with AbsSynthe.  The first backend slice
// accepts strategy AAGs that expose each controllable as an output named either
// `<name>` or `controllable_<name>`.
static Aig *run_abssynthe(const char *prog, ConstraintCover *cov,
                          const bool *seen, const Node *root, int *unreal) {
  *unreal = 0;
  Aig *game = build_abssynthe_game(cov, seen, root);
  if (!game)
    return nullptr;

  char dir[] = "/tmp/tlsfcompose-abssynthe-XXXXXX";
  if (!mkdtemp(dir)) {
    aig_free(game);
    return nullptr;
  }
  char game_path[4096], strat_path[4096];
  if (snprintf(game_path, sizeof game_path, "%s/game.aag", dir) >=
          (int)sizeof game_path ||
      snprintf(strat_path, sizeof strat_path, "%s/strategy.aag", dir) >=
          (int)sizeof strat_path) {
    cleanup_abssynthe_tmp(dir, nullptr, nullptr);
    aig_free(game);
    return nullptr;
  }
  FILE *gf = fopen(game_path, "w");
  if (!gf) {
    cleanup_abssynthe_tmp(dir, nullptr, nullptr);
    aig_free(game);
    return nullptr;
  }
  aig_write_aag(gf, game);
  fclose(gf);
  aig_free(game);

  char *argv[] = {(char *)prog, (char *)"-o", strat_path, game_path, nullptr};
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  posix_spawn_file_actions_addopen(&fa, 1, "/dev/null", O_WRONLY, 0);
  posix_spawn_file_actions_addopen(&fa, 2, "/dev/null", O_WRONLY, 0);
  pid_t pid;
  int rc = posix_spawnp(&pid, prog, &fa, nullptr, argv, environ);
  posix_spawn_file_actions_destroy(&fa);
  if (rc != 0) {
    cleanup_abssynthe_tmp(dir, game_path, strat_path);
    return nullptr;
  }

  int status;
  waitpid(pid, &status, 0);
  if (!WIFEXITED(status)) {
    cleanup_abssynthe_tmp(dir, game_path, strat_path);
    return nullptr;
  }
  int code = WEXITSTATUS(status);
  if (code == 20) {
    *unreal = 1;
    cleanup_abssynthe_tmp(dir, game_path, strat_path);
    return nullptr;
  }
  if (code != 0 && code != 10) {
    cleanup_abssynthe_tmp(dir, game_path, strat_path);
    return nullptr;
  }

  FILE *sf = fopen(strat_path, "r");
  if (!sf) {
    cleanup_abssynthe_tmp(dir, game_path, strat_path);
    return nullptr;
  }
  Aig *strategy = aig_read_aag(sf);
  fclose(sf);
  if (strategy && !abssynthe_strategy_has_outputs(strategy, cov, seen)) {
    aig_free(strategy);
    strategy = nullptr;
  }
  cleanup_abssynthe_tmp(dir, game_path, strat_path);
  return strategy;
}

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Decomposed-synthesis plan: certified controllers + residual "
      "clusters.\n"
      "  --split                      decompose constraints first\n"
      "  --aiger                      emit one merged controller (AIGER aag)"
      " via synthesis backends\n"
      "  --ltlsynt PATH               ltlsynt to use for --aiger (default: "
      "$LTLSYNT or PATH)\n"
      "  --abssynthe PATH             AbsSynthe to use for eligible safety "
      "--aiger clusters\n"
      "  --format ltlxba|ltl          output dialect (default ltlxba)\n"
      "  --output-dir DIR             write controllers.txt, cluster.<k>"
      ".ltl, compose.sh\n"
      "  --overwrite-semantics VALUE  replace SEMANTICS\n"
      "  --overwrite-target VALUE     replace TARGET\n"
      "  --param NAME=VALUE           override a parameter (repeatable)\n"
      "  --output FILE                write the plan to FILE (default "
      "stdout)\n"
      "  --version, --help\n",
      prog);
}

static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsfcompose: bad --param '%s'\n", s);
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
    fprintf(stderr, "tlsfcompose: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

static void compose_sh_header(FILE *sh) {
  fprintf(sh,
          "#!/bin/sh\n"
          "# Generated by tlsfcompose: synthesize each residual cluster with\n"
          "# ltlsynt.  controllers.txt holds the combinational part (already\n"
          "# solved, exact).  The spec is realizable iff every cluster is.\n"
          "dir=$(CDPATH= cd -- \"$(dirname -- \"$0\")\" && pwd)\n"
          "ok=1\n"
          "run() {\n"
          "  ltl=$(grep -v '^c ' \"$dir/$1\")\n"
          "  if ltlsynt --ins=\"$2\" --outs=\"$3\" --formula=\"$ltl\" "
          "--realizability >/dev/null 2>&1; then\n"
          "    echo \"$1: REALIZABLE\"\n"
          "  else\n"
          "    echo \"$1: UNREALIZABLE\"; ok=0\n"
          "  fi\n"
          "}\n");
}

int main(int argc, char *argv[]) {
  bool split = false, aiger = false;
  LtlFormat fmt = LTL_FMT_LTLXBA;
  const char *input_file = nullptr, *output_file = nullptr, *out_dir = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr, *ltlsynt_path = nullptr;
  const char *abssynthe_path = nullptr;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfcompose: %s requires an argument\n",    \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--aiger") == 0) {
      aiger = true;
    } else if (strcmp(a, "--ltlsynt") == 0) {
      ltlsynt_path = NEED_ARG();
    } else if (strcmp(a, "--abssynthe") == 0 || strcmp(a, "--absynthe") == 0) {
      abssynthe_path = NEED_ARG();
    } else if (strcmp(a, "--output-dir") == 0) {
      out_dir = NEED_ARG();
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "ltlxba"))
        fmt = LTL_FMT_LTLXBA;
      else if (!strcmp(v, "ltl"))
        fmt = LTL_FMT_LTL;
      else {
        fprintf(stderr, "tlsfcompose: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfcompose: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfcompose %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfcompose: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfcompose: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsfcompose");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfcompose");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfcompose: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfcompose: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (!spec_validate_semantics(spec, "tlsfcompose")) {
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
    fprintf(stderr, "tlsfcompose: out of memory\n");
    spec_free(spec);
    return 1;
  }
  recognize_all(cov);
  Csnf *csnf = templates_certify(cov, TPL_ALL, true);
  CsnfComposition *comp = csnf ? csnf_compose(csnf) : nullptr;
  if (!csnf || !comp) {
    fprintf(stderr, "tlsfcompose: out of memory\n");
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  FILE *out = cli_open_output(output_file, "tlsfcompose");
  if (!out) {
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  uint32_t A = cov->aps.count, N = cov->count;
  bool finite = semantics_is_finite(spec->info.semantics);
  int rc = 0;

  // Synthesis residual = every constraint NOT discharged by a combinational
  // controller (those liveness templates / registers / genuine leftovers go to
  // ltlsynt), with the combinational controllers substituted in.
  const Node **rf = calloc(N ? N : 1, sizeof(Node *));
  for (uint32_t i = 0; i < N; i++) {
    if (comp->elim_constraint[i])
      continue; // discharged by a combinational controller
    const Node *f =
        residual_apply_elims(spec->arena, cov->items[i].formula, comp, cov);
    f = apply_rewrites(spec->arena, (Node *)f, RW_SIMPLIFY_WEAK);
    if (f->kind != NODE_TRUE)
      rf[i] = f;
  }

  uint32_t *key = malloc((N ? N : 1) * sizeof(uint32_t));
  uint32_t *keys = nullptr;
  uint32_t K = residual_cluster_keys(cov, rf, N, key, &keys);
  bool *seen = calloc(A ? A : 1, sizeof(bool));

  // --aiger: synthesize each cluster with ltlsynt and merge with the
  // combinational controllers into one AIGER controller over the full
  // interface.
  if (aiger) {
    const char *env = getenv("LTLSYNT");
    const char *prog = ltlsynt_path    ? ltlsynt_path
                       : (env && *env) ? env
                                       : "ltlsynt";
    const char *abs_env = getenv("ABSSYNTHE");
    const char *abs_prog = abssynthe_path          ? abssynthe_path
                           : (abs_env && *abs_env) ? abs_env
                                                   : nullptr;
    Aig *g = aig_new();
    for (uint32_t o = 0; o < A; o++) // all declared and residual env inputs
      if (residual_signal_matches(cov, o, AP_FLAG_INPUT))
        (void)aig_input(g, ap_table_name(&cov->aps, o));

    // Clusters first (so a decoder reading a synthesized output resolves).
    for (uint32_t k = 0; k < K && rc == 0; k++) {
      Node *root =
          residual_build_cluster(spec, cov, rf, key, keys[k], false, N, seen);
      if (!root) {
        rc = 1;
        break;
      }
      int unreal = 0;
      Aig *sub = nullptr;
      if (abs_prog && abssynthe_eligible(root, finite)) {
        sub = run_abssynthe(abs_prog, cov, seen, root, &unreal);
      } else {
        char *ltl = ltl_string(root, fmt, finite);
        // Build ins/outs CSV via memstreams.
        char *ins = nullptr, *outs = nullptr;
        size_t isz = 0, osz = 0;
        FILE *fi = open_memstream(&ins, &isz),
             *fo = open_memstream(&outs, &osz);
        residual_print_signals(fi, cov, seen, AP_FLAG_INPUT);
        residual_print_signals(fo, cov, seen, AP_FLAG_OUTPUT);
        fclose(fi);
        fclose(fo);
        sub = ltl ? run_ltlsynt(prog, ins, outs, ltl, &unreal) : nullptr;
        free(ltl);
        free(ins);
        free(outs);
      }
      if (unreal) {
        fprintf(stderr, "tlsfcompose: cluster %u is UNREALIZABLE\n", k);
        rc = 1;
      } else if (!sub) {
        fprintf(stderr,
                "tlsfcompose: synthesis backend failed for cluster %u\n", k);
        rc = 1;
      } else if (!aig_merge(g, sub)) {
        fprintf(stderr, "tlsfcompose: AIGER merge failed for cluster %u\n", k);
        rc = 1;
      }
      aig_free(sub);
    }
    // Combinational controllers: ground their values, compile, drive outputs.
    for (uint32_t k = 0; k < comp->nelim && rc == 0; k++) {
      const Node *v =
          residual_apply_elims(spec->arena, comp->elim[k].value, comp, cov);
      uint32_t lit = aig_compile(g, v);
      if (lit == UINT32_MAX) {
        fprintf(stderr, "tlsfcompose: cannot encode controller for %s\n",
                ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output));
        rc = 1;
        break;
      }
      aig_set_output(
          g, ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output), lit);
    }
    // Any unconstrained output: drive to false.
    for (uint32_t o = 0; o < A && rc == 0; o++)
      if ((ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT) &&
          aig_lookup(g, ap_table_name(&cov->aps, o)) == UINT32_MAX)
        aig_set_output(g, ap_table_name(&cov->aps, o), AIG_FALSE);

    if (rc == 0)
      aig_write_aag(out, g);
    aig_free(g);
    free(seen);
    free(rf);
    free(key);
    free(keys);
    if (output_file)
      fclose(out);
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return rc;
  }

  fprintf(out, "c compose: controllers=%u clusters=%u\n", comp->nelim, K);

  // Combinational controllers (exact): o := value.
  FILE *ctlf = nullptr;
  if (out_dir) {
    char path[4096];
    snprintf(path, sizeof path, "%s/controllers.txt", out_dir);
    ctlf = fopen(path, "w");
    if (!ctlf) {
      fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
      rc = 1;
    }
  }
  for (uint32_t k = 0; k < comp->nelim && rc == 0; k++) {
    const char *oname =
        ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output);
    FILE *dst = ctlf ? ctlf : out;
    fprintf(dst, "ctl %s := ", oname);
    print_ltl(dst, comp->elim[k].value, fmt, /*full_parens=*/false, finite);
  }
  if (ctlf)
    fclose(ctlf);

  // compose.sh driver (only with --output-dir).
  FILE *shf = nullptr;
  if (out_dir && rc == 0) {
    char path[4096];
    snprintf(path, sizeof path, "%s/compose.sh", out_dir);
    shf = fopen(path, "w");
    if (!shf) {
      fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
      rc = 1;
    } else {
      compose_sh_header(shf);
    }
  }

  for (uint32_t k = 0; k < K && rc == 0; k++) {
    Node *root =
        residual_build_cluster(spec, cov, rf, key, keys[k], false, N, seen);
    if (!root) {
      rc = 1;
      break;
    }
    if (out_dir) {
      char path[4096];
      snprintf(path, sizeof path, "%s/cluster.%u.ltl", out_dir, k);
      FILE *cf = fopen(path, "w");
      if (!cf) {
        fprintf(stderr, "tlsfcompose: cannot write %s\n", path);
        rc = 1;
        break;
      }
      fprintf(cf, "c outs=");
      residual_print_signals(cf, cov, seen, AP_FLAG_OUTPUT);
      fprintf(cf, "\nc ins=");
      residual_print_signals(cf, cov, seen, AP_FLAG_INPUT);
      fprintf(cf, "\n");
      print_ltl(cf, root, fmt, false, finite);
      fclose(cf);
      fprintf(shf, "run cluster.%u.ltl \"", k);
      residual_print_signals(shf, cov, seen, AP_FLAG_INPUT);
      fprintf(shf, "\" \"");
      residual_print_signals(shf, cov, seen, AP_FLAG_OUTPUT);
      fprintf(shf, "\"\n");
      fprintf(out, "c cluster %u file=cluster.%u.ltl outs=", k, k);
      residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, " ins=");
      residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
    } else {
      fprintf(out, "c cluster %u outs=", k);
      residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, " ins=");
      residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
      print_ltl(out, root, fmt, false, finite);
    }
  }
  if (shf) {
    fprintf(shf, "[ \"$ok\" = 1 ] && echo \"SPEC REALIZABLE\" || echo \"SPEC "
                 "UNREALIZABLE\"\n");
    fclose(shf);
  }
  fprintf(out, "c realizable iff every cluster is realizable (controllers are "
               "exact)\n");

  free(seen);
  free(rf);
  free(key);
  free(keys);
  if (rc)
    fprintf(stderr, "tlsfcompose: failed (OOM or I/O)\n");
  if (output_file)
    fclose(out);
  csnf_composition_free(comp);
  csnf_free(csnf);
  spec_free(spec);
  return rc;
}
