// compose_solve.c — ltlsynt fallback + OxiDD solver dispatch for tlsfcompose.
//
// The ltlsynt subprocess path (formula rendering, --ins/--outs derivation,
// AIGER read-back) used when an OxiDD solve declines or errors; the safety and
// GR(1) dispatchers that wrap the in-process solvers and map controllable
// outputs back to cluster names; and the best-effort self-verification gate.
// See compose_internal.h.

// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/compose_internal.h"

#include "tlsf/gr1_oxidd.h"
#include "tlsf/residual.h"
#include "tlsf/safety_oxidd.h"

#include <ctype.h>
#include <fcntl.h>
#include <signal.h>
#include <spawn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

// Render a (Boolean/LTL) node to a heap string in the ltlxba/ltl dialect, with
// any trailing newline stripped (for ltlsynt --formula=).
static char *ltl_string(const Node *n, LtlFormat fmt, bool finite, bool lower) {
  char *buf = nullptr;
  size_t sz = 0;
  FILE *ms = open_memstream(&buf, &sz);
  if (!ms)
    return nullptr;
  print_ltl(ms, n, fmt, /*full_parens=*/true, finite, lower);
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

static char *str_dup_lower(const char *s) {
  size_t n = strlen(s);
  char *o = malloc(n + 1);
  if (!o)
    return nullptr;
  for (size_t i = 0; i < n; i++)
    o[i] = (char)tolower((unsigned char)s[i]);
  o[n] = '\0';
  return o;
}

// ltlsynt's ltlxba parser mishandles atoms containing uppercase letters (syfco
// lowercases for the same reason).  When a cluster has such names we send a
// lowercased formula/interface to ltlsynt and rename the controller back.
static bool seen_has_uppercase(ConstraintCover *cov, const bool *seen) {
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a])
      continue;
    for (const char *p = ap_table_name(&cov->aps, a); *p; p++)
      if (*p >= 'A' && *p <= 'Z')
        return true;
  }
  return false;
}

// Lowercasing is usable only if it stays injective over the seen names, so the
// rename-back of the controller is unambiguous.
static bool seen_lower_safe(ConstraintCover *cov, const bool *seen) {
  bool ok = true;
  uint32_t cap = 0;
  char **lc = nullptr;
  for (uint32_t a = 0; a < cov->aps.count && ok; a++) {
    if (!seen[a])
      continue;
    const char *na = ap_table_name(&cov->aps, a);
    char *l = str_dup_lower(na);
    if (!l) {
      ok = false;
      break;
    }
    for (uint32_t i = 0; i < cap; i++)
      if (strcmp(lc[i], l) == 0) {
        ok = false; // two names collide once lowercased
        break;
      }
    char **grown = ok ? realloc(lc, (cap + 1) * sizeof *lc) : nullptr;
    if (ok && grown) {
      lc = grown;
      lc[cap++] = l;
    } else {
      free(l);
      ok = false;
    }
  }
  for (uint32_t i = 0; i < cap; i++)
    free(lc[i]);
  free(lc);
  return ok;
}

// Synthesize one cluster with ltlsynt: render `root` to LTL and pass the
// cluster's input/output interface.  Caller frees the returned strategy AIG.
// When the cluster has uppercase atom names (which ltlsynt's parser mishandles)
// the formula and interface are lowercased and the controller is renamed back.
Aig *run_ltlsynt_cluster(const char *prog, ConstraintCover *cov,
                         const bool *seen, const Node *root, LtlFormat fmt,
                         bool finite, int *unreal) {
  bool lower = seen_has_uppercase(cov, seen) && seen_lower_safe(cov, seen);
  char *ltl = ltl_string(root, fmt, finite, lower);
  char *ins = nullptr, *outs = nullptr;
  size_t isz = 0, osz = 0;
  FILE *fi = open_memstream(&ins, &isz), *fo = open_memstream(&outs, &osz);
  residual_print_signals(fi, cov, seen, AP_FLAG_INPUT);
  residual_print_signals(fo, cov, seen, AP_FLAG_OUTPUT);
  fclose(fi);
  fclose(fo);
  if (lower && ins && outs) { // match the lowercased formula's atoms
    char *il = str_dup_lower(ins), *ol = str_dup_lower(outs);
    if (il && ol) {
      free(ins);
      ins = il;
      free(outs);
      outs = ol;
    } else {
      free(il);
      free(ol); // OOM: fall through; the mismatch makes ltlsynt return nothing
    }
  }

  Aig *sub = ltl ? run_ltlsynt(prog, ins, outs, ltl, unreal) : nullptr;
  if (sub && lower) // map the lowercased controller back to the spec's names
    for (uint32_t a = 0; a < cov->aps.count; a++) {
      if (!seen[a])
        continue;
      const char *orig = ap_table_name(&cov->aps, a);
      char *lc = str_dup_lower(orig);
      if (lc) {
        aig_rename_signal(sub, lc, orig);
        free(lc);
      }
    }
  free(ltl);
  free(ins);
  free(outs);
  return sub;
}

static bool strategy_has_outputs(Aig *g, ConstraintCover *cov,
                                 const bool *seen) {
  aig_remove_output(g, "bad");
  aig_strip_output_prefix(g, AIG_CONTROLLABLE_PREFIX);
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    if (!aig_has_output(g, ap_table_name(&cov->aps, a)))
      return false;
  }
  return true;
}

// Solve one safety game using OxiDD in-process BDD solver.  Takes ownership
// of `game` and returns a strategy whose controllable outputs have been mapped
// back to the cluster's output names (or nullptr, with *unreal set on a
// trusted UNREALIZABLE verdict).
Aig *solve_safety_game(ConstraintCover *cov, const bool *seen, Aig *game,
                       int *unreal) {
  Aig *strat = solve_safety_oxidd(game, unreal);
  if (strat && !strategy_has_outputs(strat, cov, seen)) {
    aig_free(strat);
    strat = nullptr;
  }
  return strat;
}

// Self-verification: run the external verifier (PROG --aiger FILE --formula
// LTL) on a synthesized controller against the original cluster spec.  Returns
// true ONLY when the verifier reports a definite violation (exit 1).  On
// "verified" (0), an AP mismatch, a verifier error/timeout/OOM, or any other
// code it returns false (keep the controller) -- an inconclusive check never
// turns a sound solve into a fallback.  `controller` has cluster-named
// inputs/outputs (the controllable_ prefix was stripped on read-back), matching
// the formula.
bool controller_violates_spec(const char *verifier, Aig *controller,
                              const Node *root, LtlFormat fmt, bool finite) {
  // The controller AIGER keeps the spec's original signal names, so the spec
  // formula handed to the verifier must too (no lowering).
  char *ltl = ltl_string(root, fmt, finite, /*lower=*/false);
  if (!ltl)
    return false;
  char tmp[] = "/tmp/tlsfcompose-verify-XXXXXX";
  int fd = mkstemp(tmp);
  if (fd < 0) {
    free(ltl);
    return false;
  }
  FILE *f = fdopen(fd, "w");
  if (!f) {
    close(fd);
    unlink(tmp);
    free(ltl);
    return false;
  }
  aig_write_aag(f, controller);
  fclose(f);

  char *argv[] = {
      (char *)verifier, (char *)"--aiger", tmp, (char *)"--formula", ltl,
      nullptr};
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  posix_spawn_file_actions_addopen(&fa, 1, "/dev/null", O_WRONLY, 0);
  posix_spawn_file_actions_addopen(&fa, 2, "/dev/null", O_WRONLY, 0);
  pid_t pid;
  int spawned = posix_spawnp(&pid, verifier, &fa, nullptr, argv, environ);
  posix_spawn_file_actions_destroy(&fa);
  bool violates = false;
  if (spawned == 0) {
    // The gate is best-effort: cap the verifier ($TLSFCOMPOSE_VERIFY_TIMEOUT
    // seconds, default 30).  A timeout (e.g. Spot blowing up on a big formula)
    // is inconclusive -- keep the controller -- rather than hanging the tool.
    const char *to_env = getenv("TLSFCOMPOSE_VERIFY_TIMEOUT");
    long timeout_s = (to_env && *to_env) ? strtol(to_env, nullptr, 10) : 30;
    int status;
    if (timeout_s > 0) {
      struct timespec slice = {0, 20L * 1000 * 1000}; // 20 ms
      long ticks = timeout_s * 50;                    // 50 polls per second
      pid_t r = 0;
      for (long i = 0; i < ticks; i++) {
        r = waitpid(pid, &status, WNOHANG);
        if (r != 0)
          break;
        nanosleep(&slice, nullptr);
      }
      if (r == 0) { // verifier did not finish in time: inconclusive
        kill(pid, SIGKILL);
        waitpid(pid, &status, 0);
        status = -1;
      }
    } else {
      waitpid(pid, &status, 0);
    }
    violates = status != -1 && WIFEXITED(status) && WEXITSTATUS(status) == 1;
  }
  unlink(tmp);
  free(ltl);
  return violates;
}

// Solve one GR(1) game using OxiDD in-process PPS fixpoint solver.
Aig *solve_gr1_game(ConstraintCover *cov, const bool *seen, Aig *game,
                    int *unreal) {
  Aig *strat = solve_gr1_oxidd(game, unreal);
  if (strat && !strategy_has_outputs(strat, cov, seen)) {
    aig_free(strat);
    strat = nullptr;
  }
  return strat;
}
