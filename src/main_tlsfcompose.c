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
#include "tlsf/gr.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/recognize.h"
#include "tlsf/residual.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include <ctype.h>
#include <fcntl.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

#define TLSF_VERSION "0.1.0"
#define ABSSYNTHE_CONTROLLABLE_PREFIX "controllable_"

// Render a (Boolean/LTL) node to a heap string in the ltlxba/ltl dialect, with
// any trailing newline stripped (for ltlsynt --formula=).
static char *ltl_string(const Node *n, LtlFormat fmt, bool finite, bool lower) {
  char *buf = nullptr;
  size_t sz = 0;
  FILE *ms = open_memstream(&buf, &sz);
  if (!ms)
    return nullptr;
  print_ltl(ms, n, fmt, /*full_parens=*/false, finite, lower);
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
static Aig *run_ltlsynt_cluster(const char *prog, ConstraintCover *cov,
                                const bool *seen, const Node *root,
                                LtlFormat fmt, bool finite, int *unreal) {
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

static bool abssynthe_initial_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return abssynthe_initial_supported(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return abssynthe_initial_supported(n->lhs) &&
           abssynthe_initial_supported(n->rhs);
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

static bool abssynthe_safety_condition_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_AND:
    return abssynthe_safety_condition_supported(n->lhs) &&
           abssynthe_safety_condition_supported(n->rhs);
  case NODE_G:
    return abssynthe_body_supported(n->arg);
  default:
    return abssynthe_initial_supported(n);
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

static uint32_t abssynthe_safety_condition_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_AND: {
    uint32_t a = abssynthe_safety_condition_x_depth(n->lhs);
    uint32_t b = abssynthe_safety_condition_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_G:
    return abssynthe_x_depth(n->arg);
  default:
    return abssynthe_initial_supported(n) ? 0 : UINT32_MAX;
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

// Recognize a re-armed safety response `G(req -> [X](a W b))` or
// `G(req -> [X](a R b))` with Boolean operands.  On success sets *req to the
// antecedent, *inner to the weak-until/release node, and *xdelay to whether the
// consequent is X-delayed.  These are genuine safety obligations that a monitor
// latch tracks (re-armed each time req fires).
static bool wr_response_parts(const Node *impl, const Node **req,
                              const Node **inner, bool *xdelay) {
  if (impl->kind != NODE_IMPL)
    return false;
  const Node *rhs = impl->rhs;
  bool x = false;
  if (rhs->kind == NODE_X || rhs->kind == NODE_X_STRONG) {
    x = true;
    rhs = rhs->arg;
  }
  if (rhs->kind != NODE_W && rhs->kind != NODE_R)
    return false;
  if (!abssynthe_body_supported(impl->lhs) ||
      !abssynthe_body_supported(rhs->lhs) ||
      !abssynthe_body_supported(rhs->rhs))
    return false;
  *req = impl->lhs;
  *inner = rhs;
  *xdelay = x;
  return true;
}

// A conjunct of a `G(...)` body: Boolean, a bare weak-until / release, or a
// re-armed response.  Under the outer G a bare W/R collapses to an invariant --
// `G(a W b) == G(a|b)`, `G(a R b) == G(b)` -- so no monitor is needed; a
// response `G(req -> [X](a W/R b))` re-arms a monitor each time req fires.
static bool g_body_wr_supported(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return g_body_wr_supported(n->lhs) && g_body_wr_supported(n->rhs);
  case NODE_W:
  case NODE_R:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  case NODE_IMPL: {
    const Node *req, *inner;
    bool xdelay;
    if (wr_response_parts(n, &req, &inner, &xdelay))
      return true;
    // Distributable: G(outer_req -> body) === AND over G(outer_req ->
    // conjunct). Supported when outer_req is propositional; each conjunct in
    // body is then checked by recursing (and resolving to bool, W/R-collapse,
    // or response).
    if (abssynthe_body_supported(n->lhs))
      return g_body_wr_supported(n->rhs);
    return false;
  }
  default:
    return abssynthe_body_supported(n);
  }
}

// Pure-safety guarantee that may also carry weak-until `a W b` or release
// `a R b` (Boolean operands): genuine safety properties.  A top-level `a W b`
// gets a "released" monitor latch; a `W`/`R` *inside* a `G` body collapses to a
// plain invariant.  Both are exactly encodable alongside `G(...)` invariants.
static bool abssynthe_safety_wr_supported(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_G:
    return g_body_wr_supported(n->arg);
  case NODE_AND:
    return abssynthe_safety_wr_supported(n->lhs) &&
           abssynthe_safety_wr_supported(n->rhs);
  case NODE_W:
  case NODE_R:
    return abssynthe_body_supported(n->lhs) && abssynthe_body_supported(n->rhs);
  default:
    // A bare Boolean conjunct is an initial-state constraint (step 0 only).
    return abssynthe_initial_supported(n);
  }
}

static uint32_t abssynthe_safety_wr_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return 0;
  case NODE_G:
    return abssynthe_x_depth(n->arg);
  case NODE_AND: {
    uint32_t a = abssynthe_safety_wr_x_depth(n->lhs);
    uint32_t b = abssynthe_safety_wr_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_W:
  case NODE_R: {
    uint32_t a = abssynthe_x_depth(n->lhs), b = abssynthe_x_depth(n->rhs);
    return a > b ? a : b;
  }
  default:
    return abssynthe_initial_supported(n) ? 0 : UINT32_MAX;
  }
}

// Does this safety condition carry a bare-Boolean (initial-state) conjunct?
// Mirrors wr_emit_guarantee's structure: only the default (bare-Boolean) leaf
// is an initial constraint, so a game needs the `first` marker only when this
// holds.
static bool wr_has_initial(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_G:
  case NODE_W:
  case NODE_R:
    return false;
  case NODE_AND:
    return wr_has_initial(n->lhs) || wr_has_initial(n->rhs);
  default:
    return true;
  }
}

static bool abssynthe_eligible(const Node *root, bool finite) {
  if (finite)
    return false;
  if (root->kind == NODE_IMPL)
    return abssynthe_global_supported(root->lhs) &&
           abssynthe_global_x_depth(root->lhs) == 0 &&
           abssynthe_safety_wr_supported(root->rhs);
  return abssynthe_safety_wr_supported(root);
}

static bool abssynthe_strict_safety_parts(const Node *root, const Node **sys,
                                          const Node **env) {
  if (root->kind != NODE_W || root->rhs->kind != NODE_NOT)
    return false;
  if (!abssynthe_safety_condition_supported(root->lhs) ||
      !abssynthe_safety_condition_supported(root->rhs->arg))
    return false;
  *sys = root->lhs;
  *env = root->rhs->arg;
  return true;
}

// ---- GR(1): `G F a` fairness assumptions + recurrence/response justice ----

#define GR1_MAX_JUSTICE 32
#define GR1_MAX_FAIRNESS 32
#define GR1_MAX_WEAK 64

typedef struct {
  const Node *req;    // nullptr for a recurrence `G F target`
  const Node *target; // recurrence goal `g`, or response grant
} Gr1Justice;

typedef struct {
  const Node *a, *b; // a weak-until guarantee `a W b` (a safety property)
} Gr1WeakUntil;

typedef struct {
  const Node *fairness[GR1_MAX_FAIRNESS]; // the `a`s in the `G F a` assumptions
  uint32_t nfairness;
  const Node *env_init;      // env initial assumption (Boolean, TRUE if none)
  const Node *sys_init;      // sys initial guarantee (Boolean, TRUE if none)
  const Node *safety_assume; // AND of safety assume conjuncts (TRUE if none)
  const Node *safety_gua;    // AND of safety guarantee conjuncts (TRUE if none)
  Gr1Justice justice[GR1_MAX_JUSTICE];
  uint32_t njustice;
  Gr1WeakUntil weak[GR1_MAX_WEAK]; // guarantee-side `a W b` safety monitors
  uint32_t nweak;
} Gr1Parts;

// `G F x` with `x` AbsSynthe-Boolean -> x, else nullptr.
static const Node *match_gf(const Node *n) {
  if (n->kind == NODE_G && n->arg->kind == NODE_F &&
      abssynthe_body_supported(n->arg->arg))
    return n->arg->arg;
  return nullptr;
}

// `G(req -> F grant)` with req, grant AbsSynthe-Boolean.
static bool match_response(const Node *n, const Node **req,
                           const Node **grant) {
  if (n->kind != NODE_G || n->arg->kind != NODE_IMPL)
    return false;
  const Node *body = n->arg;
  if (body->rhs->kind != NODE_F || !abssynthe_body_supported(body->lhs) ||
      !abssynthe_body_supported(body->rhs->arg))
    return false;
  *req = body->lhs;
  *grant = body->rhs->arg;
  return true;
}

// Classify each top-level conjunct of an assume/guarantee side into the
// fairness / justice / safety buckets of `p`.  Returns false on any conjunct
// that is neither a recognized liveness goal nor an encodable safety formula.
static bool gr1_collect(Arena *a, const Node *n, bool assume, Gr1Parts *p) {
  if (n->kind == NODE_AND)
    return gr1_collect(a, n->lhs, assume, p) &&
           gr1_collect(a, n->rhs, assume, p);
  // An initial Boolean conjunct (env-init on the assume side, sys-init on the
  // guarantee side): part of the GR(1) implication's antecedent/consequent.
  if (abssynthe_initial_supported(n)) {
    const Node **init = assume ? &p->env_init : &p->sys_init;
    *init =
        (*init)->kind == NODE_TRUE ? n : node_and(a, (Node *)*init, (Node *)n);
    return true;
  }
  const Node *gf = match_gf(n);
  if (assume) {
    if (gf) {
      if (p->nfairness >= GR1_MAX_FAIRNESS)
        return false;
      p->fairness[p->nfairness++] = gf;
      return true;
    }
  } else if (gf) {
    if (p->njustice >= GR1_MAX_JUSTICE)
      return false;
    p->justice[p->njustice++] = (Gr1Justice){nullptr, gf};
    return true;
  } else {
    const Node *req = nullptr, *grant = nullptr;
    if (match_response(n, &req, &grant)) {
      if (p->njustice >= GR1_MAX_JUSTICE)
        return false;
      p->justice[p->njustice++] = (Gr1Justice){req, grant};
      return true;
    }
    // A weak-until `a W b` (Boolean a, b) is a pure-safety guarantee: a holds
    // until b, or forever.  Encoded with a "released" monitor in the emitter.
    if (n->kind == NODE_W && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs)) {
      if (p->nweak >= GR1_MAX_WEAK)
        return false;
      p->weak[p->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
      return true;
    }
  }
  if (!abssynthe_global_supported(n))
    return false; // otherwise must be an encodable `G(safety)` conjunct
  const Node **safety = assume ? &p->safety_assume : &p->safety_gua;
  *safety = (*safety)->kind == NODE_TRUE
                ? n
                : node_and(a, (Node *)*safety, (Node *)n);
  return true;
}

// Bucket the system-safety side `S_safety` of a strict `S_safety W ¬A_safety`
// conjunct (a conjunction of `G(...)` invariants and initial Booleans) into the
// guarantee-safety / sys-init buckets.  The strict conditioning itself is
// realized by the `violated` latch (driven by the env safety A_safety, which
// reappears in the liveness antecedent E), so the `¬A_safety` release is
// redundant here and ignored.
static bool gr1_collect_strict_safety(Arena *a, const Node *n, Gr1Parts *p) {
  if (n->kind == NODE_AND)
    return gr1_collect_strict_safety(a, n->lhs, p) &&
           gr1_collect_strict_safety(a, n->rhs, p);
  if (abssynthe_initial_supported(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (!abssynthe_global_supported(n))
    return false;
  p->safety_gua = p->safety_gua->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->safety_gua, (Node *)n);
  return true;
}

// Bucket a GR(1) consequent conjunct.  A GR(1) cluster has exactly ONE
// `assume -> guarantee` implication carrying all fairness/justice; outside it
// only sys-init Booleans and unconditional safety (`G(...)`, weak-until, or a
// strict `S W ¬A` safety) are allowed.  A bare `G F`/response or a second
// implication is rejected: it would be unconditional or independent liveness,
// which is not a single GR(1) condition (it is Streett-like).
static bool gr1_collect_consequent(Arena *a, const Node *n, Gr1Parts *p,
                                   bool *found_impl) {
  if (n->kind == NODE_AND)
    return gr1_collect_consequent(a, n->lhs, p, found_impl) &&
           gr1_collect_consequent(a, n->rhs, p, found_impl);
  if (abssynthe_initial_supported(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (n->kind == NODE_IMPL) { // the single flat GR(1) implication
    if (*found_impl)
      return false; // a second independent implication is not GR(1)
    *found_impl = true;
    return gr1_collect(a, n->lhs, true, p) && gr1_collect(a, n->rhs, false, p);
  }
  if (match_gf(n))
    return false; // unconditional `G F` justice (not gated by the assume)
  if (n->kind == NODE_W && abssynthe_body_supported(n->lhs) &&
      abssynthe_body_supported(n->rhs)) {
    if (p->nweak >= GR1_MAX_WEAK)
      return false;
    p->weak[p->nweak++] = (Gr1WeakUntil){n->lhs, n->rhs};
    return true;
  }
  // Strict GR(1) safety `S_safety W ¬A_safety` (the operands carry `G(...)`, so
  // the pure weak-until above did not match).  Bucket S_safety; A_safety is
  // captured from the liveness antecedent E and drives the `violated` latch.
  if (n->kind == NODE_W && n->rhs->kind == NODE_NOT)
    return gr1_collect_strict_safety(a, n->lhs, p);
  if (!abssynthe_global_supported(n))
    return false; // bare response / anything that is not unconditional safety
  p->safety_gua = p->safety_gua->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->safety_gua, (Node *)n);
  return true;
}

// Recognize a GR(1) cluster `(EnvInit & SafetyAssume & AND G F a) ->
// (SysInit & SafetyGua & AND justice)`: >= 1 fairness, >= 1 justice, safety
// parts encodable with x-depth-0 assumptions.  TLSF renders initial conditions
// as a nested `EnvInit -> (SysInit & (assume -> guarantee))`, so peel the
// initial Boolean antecedents/conjuncts first.
static bool abssynthe_gr1_parts(Arena *a, const Node *root, Gr1Parts *p) {
  *p = (Gr1Parts){.nfairness = 0,
                  .env_init = node_true(a),
                  .sys_init = node_true(a),
                  .safety_assume = node_true(a),
                  .safety_gua = node_true(a),
                  .njustice = 0};
  // Peel env-init: `EnvInit -> rest` where the antecedent is purely initial
  // (a `G`/`G F` antecedent is the real assume side, so it is not peeled).
  while (root->kind == NODE_IMPL && abssynthe_initial_supported(root->lhs)) {
    p->env_init = p->env_init->kind == NODE_TRUE
                      ? root->lhs
                      : node_and(a, (Node *)p->env_init, (Node *)root->lhs);
    root = root->rhs;
  }
  // The remainder is the guarantee side: sys-init conjuncts, unconditional
  // safety, and the single `(AND G F a) -> (AND justice)` implication (anywhere
  // in the AND tree).  gr1_collect_consequent buckets them and rejects
  // non-GR(1) shapes; the fairness/justice counts below are the final gate.
  bool found_impl = false;
  if (!gr1_collect_consequent(a, root, p, &found_impl))
    return false;
  // The emitter encodes X-depth assumptions via the assumption window, so the
  // safety assume need only be encodable (finite X-depth), not x-depth 0.
  return p->nfairness > 0 && p->njustice > 0 &&
         abssynthe_global_x_depth(p->safety_assume) != UINT32_MAX;
}

// Bounded eventually: `x | Xx | ... | X^k x` ("x within the next k steps").
static Node *bounded_eventually(Arena *a, Node *x, uint32_t k) {
  Node *r = x, *xi = x;
  for (uint32_t i = 1; i <= k; i++) {
    xi = node_x(a, xi);
    r = node_or(a, r, xi);
  }
  return r;
}

// Bounded until: `⋁_{i=0}^{k} ( (⋀_{j<i} X^j p) ∧ X^i q )` ("q within the next
// k steps, with p holding until then").  Sound under-approximation of `p U q`.
static Node *bounded_until(Arena *a, Node *p, Node *q, uint32_t k) {
  Node *acc = q;            // i = 0: q
  Node *pre = node_true(a); // ⋀_{j<i} X^j p
  Node *xp = p, *xq = q;    // X^{i-1} p (next loop) / X^i q
  for (uint32_t i = 1; i <= k; i++) {
    pre = node_and(a, pre, xp); // now ⋀_{j=0}^{i-1} X^j p
    xp = node_x(a, xp);
    xq = node_x(a, xq);
    acc = node_or(a, acc, node_and(a, pre, xq));
  }
  return acc;
}

// Bound the *guarantee* liveness of a cluster: rewrite `F x` (with `x` an
// AbsSynthe-Boolean body) to `x | Xx | ... | X^k x` at *positive* polarity
// only. Bounding a guarantee is sound — forcing `x` within k steps is a
// strictly stronger obligation than `F x`, so a controller for the bounded game
// still satisfies the unbounded spec.  Bounding an assumption would be unsound,
// so an `F` at negative polarity (an antecedent / fairness assumption) is left
// intact; it then fails `abssynthe_eligible` and the cluster stays on ltlsynt.
// This turns `G F g` into `G(g|..|X^k g)` and `G(req -> F grant)` into `G(req
// -> grant|..|X^k grant)`, both pure-safety games the existing AbsSynthe safety
// encoder handles.
static Node *bound_liveness(Arena *a, const Node *n, uint32_t k, bool pos) {
  switch (n->kind) {
  case NODE_F:
    if (pos && abssynthe_body_supported(n->arg))
      return bounded_eventually(a, bound_liveness(a, n->arg, k, pos), k);
    return node_f(a, bound_liveness(a, n->arg, k, pos));
  case NODE_G:
    return node_g(a, bound_liveness(a, n->arg, k, pos));
  case NODE_X:
    return node_x(a, bound_liveness(a, n->arg, k, pos));
  case NODE_X_STRONG:
    return node_x_strong(a, bound_liveness(a, n->arg, k, pos));
  case NODE_NOT:
    return node_not(a, bound_liveness(a, n->arg, k, !pos));
  case NODE_AND:
    return node_and(a, bound_liveness(a, n->lhs, k, pos),
                    bound_liveness(a, n->rhs, k, pos));
  case NODE_OR:
    return node_or(a, bound_liveness(a, n->lhs, k, pos),
                   bound_liveness(a, n->rhs, k, pos));
  case NODE_IMPL:
    return node_impl(a, bound_liveness(a, n->lhs, k, !pos),
                     bound_liveness(a, n->rhs, k, pos));
  case NODE_U:
    if (pos && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs))
      return bounded_until(a, bound_liveness(a, n->lhs, k, pos),
                           bound_liveness(a, n->rhs, k, pos), k);
    return node_u(a, bound_liveness(a, n->lhs, k, pos),
                  bound_liveness(a, n->rhs, k, pos));
  case NODE_W: // a W b: strengthen to bounded(a U b) (sound: bounded => U => W)
    if (pos && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs))
      return bounded_until(a, bound_liveness(a, n->lhs, k, pos),
                           bound_liveness(a, n->rhs, k, pos), k);
    return node_w(a, bound_liveness(a, n->lhs, k, pos),
                  bound_liveness(a, n->rhs, k, pos));
  case NODE_R: // a R b: strengthen to bounded(b U (a&b)) (sound: => R)
  case NODE_M: // a M b == b U (a&b); bounded form is sound
    if (pos && abssynthe_body_supported(n->lhs) &&
        abssynthe_body_supported(n->rhs)) {
      Node *bl = bound_liveness(a, n->lhs, k, pos);
      Node *br = bound_liveness(a, n->rhs, k, pos);
      return bounded_until(a, br, node_and(a, bl, br), k);
    }
    return n->kind == NODE_R ? node_r(a, bound_liveness(a, n->lhs, k, pos),
                                      bound_liveness(a, n->rhs, k, pos))
                             : node_m(a, bound_liveness(a, n->lhs, k, pos),
                                      bound_liveness(a, n->rhs, k, pos));
  default:
    // AP / constant, or EQUIV left intact — a positive liveness operator
    // surviving inside it fails eligibility and the cluster stays on ltlsynt.
    return (Node *)n;
  }
}

typedef struct {
  int gr_level;
  bool has_liveness;
  bool has_weak_until;
  bool has_release;
  bool has_strong_next;
  bool has_high_level;
} ClusterShape;

// True if n contains at least one safety temporal operator (G, W, R) and no
// liveness operators (F, U, M) — i.e., NOT(n) would be liveness.  A purely
// propositional n (no temporal operators) returns false because NOT(prop) is
// still propositional, not liveness.
static bool is_safety_temporal(const Node *n) {
  switch (n->kind) {
  case NODE_G:
  case NODE_W:
  case NODE_R:
    return true; // explicit safety temporal operator
  case NODE_X:
  case NODE_X_STRONG:
    return is_safety_temporal(n->arg);
  case NODE_AND:
    return is_safety_temporal(n->lhs) || is_safety_temporal(n->rhs);
  default:
    // Propositional (AP, TRUE, FALSE), liveness ops, NOT, OR, IMPL —
    // none qualify as "safety temporal" for this check.
    return false;
  }
}

static void cluster_shape_visit(const Node *n, ClusterShape *shape) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
  case NODE_INT:
    return;
  case NODE_X_STRONG:
    shape->has_strong_next = true;
    [[fallthrough]];
  case NODE_X:
  case NODE_G:
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_NOT:
    // NOT(safety_temporal) is liveness: the parser simplifies `G(w) -> false`
    // to NOT(G(w)) = F(!w), and NOT(AND(G(a), G(b))) similarly.  Detect this
    // so has_liveness is set correctly for routing.  Pure propositional NOT
    // (is_safety_temporal returns false) falls through to normal recursion.
    if (is_safety_temporal(n->arg)) {
      shape->has_liveness = true;
      return;
    }
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_F:
    shape->has_liveness = true;
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_W:
    shape->has_weak_until = true;
    return; // inner structure checked by wr_structural_supported; don't recurse
  case NODE_R:
    shape->has_release = true;
    return; // inner structure checked by wr_structural_supported; don't recurse
  case NODE_U:
  case NODE_M:
    shape->has_liveness = true;
    break;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    break;
  default:
    if (node_kind_is_high_level(n->kind))
      shape->has_high_level = true;
    return;
  }
  cluster_shape_visit(n->lhs, shape);
  cluster_shape_visit(n->rhs, shape);
}

static ClusterShape cluster_shape(TlsfSpec *spec, const Node *root) {
  ClusterShape shape = {.gr_level = gr_level(spec)};
  cluster_shape_visit(root, &shape);
  return shape;
}

static const char *cluster_ltlsynt_reason(const ClusterShape *shape,
                                          bool finite, bool abs_configured,
                                          char *buf, size_t buf_sz) {
  if (finite) {
    snprintf(buf, buf_sz, "finite semantics are not supported by AbsSynthe");
  } else if (shape->gr_level >= 0 && shape->has_liveness) {
    snprintf(buf, buf_sz,
             "GR(%d) residual with liveness; no GR backend is available "
             "without ltlsynt",
             shape->gr_level);
  } else if (shape->has_liveness) {
    snprintf(buf, buf_sz,
             "liveness temporal operators are not "
             "AbsSynthe-eligible");
  } else if (shape->has_weak_until) {
    snprintf(buf, buf_sz,
             "weak-until safety release is not AbsSynthe-eligible");
  } else if (shape->has_release) {
    snprintf(buf, buf_sz, "release safety shape is not AbsSynthe-eligible");
  } else if (shape->has_strong_next) {
    snprintf(buf, buf_sz, "finite-only strong-next is not AbsSynthe-eligible");
  } else if (shape->has_high_level) {
    snprintf(buf, buf_sz,
             "unexpanded high-level operators are not backend-eligible");
  } else if (!abs_configured) {
    snprintf(buf, buf_sz,
             "no AbsSynthe backend configured for this safety cluster");
  } else {
    snprintf(buf, buf_sz, "unsupported temporal shape");
  }
  return buf;
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
    default: { // EQUIV: sequence for determinism across compilers
      uint32_t e0 = aig_or(ctx->g, aig_not(a), b);
      uint32_t e1 = aig_or(ctx->g, a, aig_not(b));
      return aig_and(ctx->g, e0, e1);
    }
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
    // At an early lag an X-depth assumption reaches before the window start and
    // is not yet evaluable; it is vacuously satisfied there, so skip it.  The
    // caller has already checked the assumption is encodable (finite X-depth).
    if (at_lag == UINT32_MAX)
      continue;
    ok = aig_and(ctx->g, ok, at_lag);
  }
  return ok;
}

static uint32_t abssynthe_compile_safety_initial(AbssyntheCompile *ctx,
                                                 const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_G:
    return AIG_TRUE;
  case NODE_AND: {
    uint32_t a = abssynthe_compile_safety_initial(ctx, n->lhs);
    uint32_t b = abssynthe_compile_safety_initial(ctx, n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return aig_and(ctx->g, a, b);
  }
  default:
    return abssynthe_compile_at_lag(ctx, n, 0);
  }
}

static uint32_t abssynthe_compile_safety_global_at_lag(AbssyntheCompile *ctx,
                                                       const Node *n,
                                                       uint32_t lag) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_G:
    return abssynthe_compile_at_lag(ctx, n->arg, lag);
  case NODE_AND: {
    uint32_t a = abssynthe_compile_safety_global_at_lag(ctx, n->lhs, lag);
    uint32_t b = abssynthe_compile_safety_global_at_lag(ctx, n->rhs, lag);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return aig_and(ctx->g, a, b);
  }
  default:
    return AIG_TRUE;
  }
}

static uint32_t guarded_current_ok(Aig *g, uint32_t guard, uint32_t ok) {
  return aig_or(g, aig_not(guard), ok);
}

// Like wr_emit_g_body but with an additional `arm_gate` that limits when new
// obligations can be armed and when invariants are checked.  Once armed, a
// response obligation remains active under `valid` regardless of `arm_gate`
// (the gate only controls arming, not the subsequent tracking/bad signal).
// This implements G(outer_req -> body): distribute outer_req over each conjunct
// so that obligations arm only when outer_req holds, yet once armed they fire
// under the original `valid`.
static bool wr_emit_g_body_gated(AbssyntheCompile *ctx, const Node *n,
                                 uint32_t depth, uint32_t valid,
                                 uint32_t arm_gate, uint32_t *bad) {
  Aig *g = ctx->g;
  switch (n->kind) {
  case NODE_AND:
    return wr_emit_g_body_gated(ctx, n->lhs, depth, valid, arm_gate, bad) &&
           wr_emit_g_body_gated(ctx, n->rhs, depth, valid, arm_gate, bad);
  case NODE_W: { // G(outer_req -> (a W b)) == G(outer_req -> (a|b))
    uint32_t a = abssynthe_compile_at_lag(ctx, n->lhs, depth);
    uint32_t b = abssynthe_compile_at_lag(ctx, n->rhs, depth);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return false;
    *bad = aig_or(
        g, *bad,
        aig_and(g, aig_and(g, valid, arm_gate), aig_not(aig_or(g, a, b))));
    return true;
  }
  case NODE_R: { // G(outer_req -> (a R b)) == G(outer_req -> b)
    uint32_t b = abssynthe_compile_at_lag(ctx, n->rhs, depth);
    if (b == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, aig_and(g, valid, arm_gate), aig_not(b)));
    return true;
  }
  case NODE_IMPL: {
    const Node *rqn, *inner;
    bool xdelay;
    if (wr_response_parts(n, &rqn, &inner, &xdelay)) {
      // G(outer_req -> req -> [X](a W/R b)): arm when both outer_req and req
      // hold; once armed, track the obligation under `valid` (no outer_req
      // gate).
      uint32_t req = abssynthe_compile_at_lag(ctx, rqn, depth);
      uint32_t a = abssynthe_compile_at_lag(ctx, inner->lhs, depth);
      uint32_t b = abssynthe_compile_at_lag(ctx, inner->rhs, depth);
      if (req == UINT32_MAX || a == UINT32_MAX || b == UINT32_MAX)
        return false;
      uint32_t release = inner->kind == NODE_W ? b : aig_and(g, a, b);
      uint32_t fail = inner->kind == NODE_W ? aig_and(g, aig_not(a), aig_not(b))
                                            : aig_not(b);
      uint32_t owe = aig_latch(g, AIG_FALSE, AIG_FALSE);
      uint32_t arm = aig_and(g, aig_and(g, valid, arm_gate), req);
      uint32_t active;
      if (xdelay) {
        active = owe;
        if (!aig_set_latch_next(
                g, owe, aig_or(g, arm, aig_and(g, owe, aig_not(release)))))
          return false;
      } else {
        active = aig_or(g, arm, owe);
        if (!aig_set_latch_next(g, owe, aig_and(g, active, aig_not(release))))
          return false;
      }
      // Bad under `valid` only: once armed, obligation must be satisfied even
      // when outer_req is not currently asserted.
      *bad = aig_or(g, *bad, aig_and(g, valid, aig_and(g, active, fail)));
      return true;
    }
    // Nested distributable: G(outer_req -> inner_req -> body)
    if (abssynthe_body_supported(n->lhs)) {
      uint32_t inner_gate = abssynthe_compile_at_lag(ctx, n->lhs, depth);
      if (inner_gate == UINT32_MAX)
        return false;
      return wr_emit_g_body_gated(ctx, n->rhs, depth, valid,
                                  aig_and(g, arm_gate, inner_gate), bad);
    }
    [[fallthrough]];
  }
  default: {
    uint32_t ok = abssynthe_compile_at_lag(ctx, n, depth);
    if (ok == UINT32_MAX)
      return false;
    *bad =
        aig_or(g, *bad, aig_and(g, aig_and(g, valid, arm_gate), aig_not(ok)));
    return true;
  }
  }
}

// Accumulate the obligations of a `G(...)` body into *bad.  A Boolean conjunct
// adds `valid & !body`.  `G(a W b) == G(a|b)` and `G(a R b) == G(b)` collapse
// to invariants.  A response `G(req -> X(a W b))` re-arms a weak-until each
// time req fires: an `owe` latch (owe' = (valid & req) | (owe & !b)) tracks an
// outstanding obligation, and the system loses if a and b both fail while owed.
static bool wr_emit_g_body(AbssyntheCompile *ctx, const Node *n, uint32_t depth,
                           uint32_t valid, uint32_t *bad) {
  Aig *g = ctx->g;
  switch (n->kind) {
  case NODE_AND:
    return wr_emit_g_body(ctx, n->lhs, depth, valid, bad) &&
           wr_emit_g_body(ctx, n->rhs, depth, valid, bad);
  case NODE_W: { // G(a W b) == G(a | b)
    uint32_t a = abssynthe_compile_at_lag(ctx, n->lhs, depth);
    uint32_t b = abssynthe_compile_at_lag(ctx, n->rhs, depth);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_not(aig_or(g, a, b))));
    return true;
  }
  case NODE_R: { // G(a R b) == G(b)
    uint32_t b = abssynthe_compile_at_lag(ctx, n->rhs, depth);
    if (b == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_not(b)));
    return true;
  }
  case NODE_IMPL: {
    const Node *rqn, *inner;
    bool xdelay;
    if (wr_response_parts(n, &rqn, &inner, &xdelay)) {
      // G(req -> [X](a W/R b)): a re-armed response monitor.  An `owe` latch
      // tracks an outstanding obligation; `a W b` releases on b (fails on
      // !a&!b), `a R b` releases on a&b (fails on !b).  Without X the
      // obligation is active the same step req fires; with X it is delayed one
      // step.
      uint32_t req = abssynthe_compile_at_lag(ctx, rqn, depth);
      uint32_t a = abssynthe_compile_at_lag(ctx, inner->lhs, depth);
      uint32_t b = abssynthe_compile_at_lag(ctx, inner->rhs, depth);
      if (req == UINT32_MAX || a == UINT32_MAX || b == UINT32_MAX)
        return false;
      uint32_t release =
          inner->kind == NODE_W ? b : aig_and(g, a, b); // W: b; R: a&b
      uint32_t fail = inner->kind == NODE_W ? aig_and(g, aig_not(a), aig_not(b))
                                            : aig_not(b); // W: !a&!b; R: !b
      uint32_t owe = aig_latch(g, AIG_FALSE, AIG_FALSE);
      uint32_t active; // obligation active this step
      if (xdelay) {
        active = owe;
        uint32_t owe_next = aig_or(g, aig_and(g, valid, req),
                                   aig_and(g, owe, aig_not(release)));
        if (!aig_set_latch_next(g, owe, owe_next))
          return false;
      } else {
        active = aig_or(g, aig_and(g, valid, req), owe);
        if (!aig_set_latch_next(g, owe, aig_and(g, active, aig_not(release))))
          return false;
      }
      *bad = aig_or(g, *bad, aig_and(g, valid, aig_and(g, active, fail)));
      return true;
    }
    // Distributable: G(outer_req -> body) — delegate to the gated emitter which
    // arms obligations under outer_req but tracks them under the original
    // valid.
    if (abssynthe_body_supported(n->lhs)) {
      uint32_t outer = abssynthe_compile_at_lag(ctx, n->lhs, depth);
      if (outer == UINT32_MAX)
        return false;
      return wr_emit_g_body_gated(ctx, n->rhs, depth, valid, outer, bad);
    }
    [[fallthrough]];
  }
  default: {
    uint32_t ok = abssynthe_compile_at_lag(ctx, n, depth);
    if (ok == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_not(ok)));
    return true;
  }
  }
}

// Accumulate a safety guarantee's obligations into *bad.  `G(body)` adds the
// combinational `valid & !body@depth` (W/R inside the body collapse to
// invariants).  A top-level weak-until `a W b` (a holds until b, or forever)
// and release `a R b` (b holds until a&b, or forever) are genuine safety
// properties: each gets a "released" monitor latch and the system loses only if
// the obligation fails before the release.  A bare Boolean conjunct is an
// initial-state constraint, charged only on the first valid step (`first`).
// Returns false on an unsupported conjunct.
static bool wr_emit_guarantee(AbssyntheCompile *ctx, const Node *n,
                              uint32_t depth, uint32_t valid, uint32_t first,
                              uint32_t *bad) {
  Aig *g = ctx->g;
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_AND:
    return wr_emit_guarantee(ctx, n->lhs, depth, valid, first, bad) &&
           wr_emit_guarantee(ctx, n->rhs, depth, valid, first, bad);
  case NODE_G:
    return wr_emit_g_body(ctx, n->arg, depth, valid, bad);
  case NODE_W:
  case NODE_R: {
    uint32_t av = abssynthe_compile_at_lag(ctx, n->lhs, depth);
    uint32_t bv = abssynthe_compile_at_lag(ctx, n->rhs, depth);
    if (av == UINT32_MAX || bv == UINT32_MAX)
      return false;
    uint32_t rel = aig_latch(g, AIG_FALSE, AIG_FALSE);
    // a W b releases on b; a R b releases on (a & b).
    uint32_t release = n->kind == NODE_W ? bv : aig_and(g, av, bv);
    if (!aig_set_latch_next(g, rel, aig_or(g, rel, aig_and(g, valid, release))))
      return false;
    // a W b fails when a and b both fail before release; a R b when b fails.
    uint32_t fail =
        n->kind == NODE_W ? aig_and(g, aig_not(av), aig_not(bv)) : aig_not(bv);
    *bad = aig_or(g, *bad, aig_and(g, valid, aig_and(g, aig_not(rel), fail)));
    return true;
  }
  default: {
    // Bare Boolean: an initial-state constraint, evaluated only on the first
    // logical step (the rising edge of valid).
    if (!abssynthe_initial_supported(n))
      return false;
    uint32_t ok = abssynthe_compile_at_lag(ctx, n, depth);
    if (ok == UINT32_MAX)
      return false;
    *bad = aig_or(g, *bad, aig_and(g, first, aig_not(ok)));
    return true;
  }
  }
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
  uint32_t gua_depth = abssynthe_safety_wr_x_depth(guarantee);
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

  // The rising edge of valid (first logical step) charges initial constraints;
  // build the marker latch only when the guarantee actually has an initial.
  uint32_t first = AIG_FALSE;
  if (wr_has_initial(guarantee)) {
    uint32_t seen_valid = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, seen_valid, aig_or(g, seen_valid, valid))) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    first = aig_and(g, valid, aig_not(seen_valid));
  }

  uint32_t bad = AIG_FALSE;
  if (!wr_emit_guarantee(&ctx, guarantee, depth, valid, first, &bad)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
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

// A safety cluster `AND(U..., IMPL(A, G))`: unconditional safety U plus one
// assume->guarantee, where U/A/G are W/R-safety (`g_body`/top-level monitors).
static bool wr_structural_supported(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return wr_structural_supported(n->lhs) && wr_structural_supported(n->rhs);
  case NODE_IMPL:
    return abssynthe_safety_wr_supported(n->lhs) &&
           abssynthe_safety_wr_supported(n->rhs);
  default:
    return abssynthe_safety_wr_supported(n);
  }
}

static bool wr_structural_has_initial(const Node *n) {
  switch (n->kind) {
  case NODE_AND:
    return wr_structural_has_initial(n->lhs) ||
           wr_structural_has_initial(n->rhs);
  case NODE_IMPL:
    return wr_has_initial(n->lhs) || wr_has_initial(n->rhs);
  default:
    return wr_has_initial(n);
  }
}

static uint32_t wr_structural_x_depth(const Node *n) {
  switch (n->kind) {
  case NODE_AND: {
    uint32_t a = wr_structural_x_depth(n->lhs);
    uint32_t b = wr_structural_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  case NODE_IMPL: {
    uint32_t a = abssynthe_safety_wr_x_depth(n->lhs);
    uint32_t b = abssynthe_safety_wr_x_depth(n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    return a > b ? a : b;
  }
  default:
    return abssynthe_safety_wr_x_depth(n);
  }
}

// Emit the obligations of `AND(U..., IMPL(A, G))`: unconditional U conjuncts
// into *bad, the assume A's violations into *viol_a (drive `violated`), the
// guarantee G's into *bad_cond (gated by !released).  At most one implication.
static bool wr_emit_structural(AbssyntheCompile *ctx, const Node *n,
                               uint32_t depth, uint32_t valid, uint32_t first,
                               uint32_t *bad, uint32_t *viol_a,
                               uint32_t *bad_cond, int *nimpl) {
  if (n->kind == NODE_AND)
    return wr_emit_structural(ctx, n->lhs, depth, valid, first, bad, viol_a,
                              bad_cond, nimpl) &&
           wr_emit_structural(ctx, n->rhs, depth, valid, first, bad, viol_a,
                              bad_cond, nimpl);
  if (n->kind == NODE_IMPL) {
    if (++(*nimpl) > 1)
      return false;
    return wr_emit_guarantee(ctx, n->lhs, depth, valid, first, viol_a) &&
           wr_emit_guarantee(ctx, n->rhs, depth, valid, first, bad_cond);
  }
  return wr_emit_guarantee(ctx, n, depth, valid, first, bad);
}

// Safety game for `AND(U..., IMPL(A, G))` with W/R on any side.  Reuses the
// verified wr_emit_guarantee walk; the assume's violations latch `violated`
// (the system is released once the env breaks an assumption), so the guarantee
// bad is gated by `!released` while the unconditional U bad is not.
static Aig *build_abssynthe_wr_game(ConstraintCover *cov, const bool *seen,
                                    const Node *root) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;
  uint32_t depth = wr_structural_x_depth(root);
  if (depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AbssyntheCompile ctx = {g, cov, hist, A ? A : 1};
  for (uint32_t a = 0; a < cov->aps.count; a++)
    if (seen[a] && residual_signal_matches(cov, a, AP_FLAG_INPUT))
      hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
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
  for (uint32_t d = 1; d <= depth; d++)
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);
  // The rising edge of valid (first logical step) charges initial constraints;
  // build the marker latch only when some conjunct actually has an initial.
  uint32_t first = AIG_FALSE;
  if (wr_structural_has_initial(root)) {
    uint32_t seen_valid = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, seen_valid, aig_or(g, seen_valid, valid))) {
      free(hist);
      aig_free(g);
      return nullptr;
    }
    first = aig_and(g, valid, aig_not(seen_valid));
  }

  uint32_t bad = AIG_FALSE, viol_a = AIG_FALSE, bad_cond = AIG_FALSE;
  int nimpl = 0;
  if (!wr_emit_structural(&ctx, root, depth, valid, first, &bad, &viol_a,
                          &bad_cond, &nimpl)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  // released = env has broken an assumption now or in the past.
  uint32_t violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
  uint32_t released = aig_or(g, violated, viol_a);
  if (!aig_set_latch_next(g, violated, released)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  bad = aig_or(g, bad, aig_and(g, aig_not(released), bad_cond));
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}

static Aig *build_abssynthe_strict_safety_game(ConstraintCover *cov,
                                               const bool *seen,
                                               const Node *sys,
                                               const Node *env) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;

  uint32_t env_depth = abssynthe_safety_condition_x_depth(env);
  uint32_t sys_depth = abssynthe_safety_condition_x_depth(sys);
  if (env_depth == UINT32_MAX || sys_depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t depth = env_depth > sys_depth ? env_depth : sys_depth;
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
  uint32_t past_first = aig_latch(g, AIG_TRUE, AIG_FALSE);
  uint32_t first = aig_not(past_first);

  uint32_t env_init_ok = abssynthe_compile_safety_initial(&ctx, env);
  uint32_t sys_init_ok = abssynthe_compile_safety_initial(&ctx, sys);
  uint32_t env_global_ok =
      abssynthe_compile_safety_global_at_lag(&ctx, env, depth);
  uint32_t sys_global_ok =
      abssynthe_compile_safety_global_at_lag(&ctx, sys, depth);
  if (env_init_ok == UINT32_MAX || sys_init_ok == UINT32_MAX ||
      env_global_ok == UINT32_MAX || sys_global_ok == UINT32_MAX) {
    free(hist);
    aig_free(g);
    return nullptr;
  }

  uint32_t env_ok = aig_and(g, guarded_current_ok(g, first, env_init_ok),
                            guarded_current_ok(g, valid, env_global_ok));
  uint32_t sys_ok = aig_and(g, guarded_current_ok(g, first, sys_init_ok),
                            guarded_current_ok(g, valid, sys_global_ok));
  uint32_t violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
  uint32_t violated_next = aig_or(g, violated, aig_not(env_ok));
  if (!aig_set_latch_next(g, violated, violated_next)) {
    free(hist);
    aig_free(g);
    return nullptr;
  }
  uint32_t bad =
      aig_and(g, aig_not(violated), aig_and(g, env_ok, aig_not(sys_ok)));
  aig_set_output(g, "bad", bad);
  free(hist);
  return g;
}

// Complete (unbounded) GR(1): the safety part (history latches, the valid
// window, the guarantee/assumption masking) is encoded exactly like
// build_abssynthe_game, but liveness is emitted as real AIGER justice /
// fairness records for AbsSynthe's GR(1) solver rather than bounded counters.
// Each justice goal `J` becomes a deterministic pending monitor
// (`pending' = !violated & !grant & (pending | req)`, with `req = true` for a
// recurrence `G F J`) so its justice literal `!pending` is a STATE predicate
// and G F !pending <=> the goal is met infinitely often.  The fairness
// assumption `a` is sampled into a latch (`fa' = a`) so its fairness literal is
// a state predicate too.  State predicates are required: AbsSynthe's
// controllable predecessor (and its multi-goal justice-counter
// degeneralization) mishandle goals/assumptions that mention inputs directly.
// When the environment breaks the SAFETY assumption (`violated` latches), the
// monitors are forced to clear, lifting the liveness obligation just as the
// safety `bad` masking lifts the safety obligation -- the GR(1) implication is
// then vacuously won.
static Aig *build_abssynthe_unbounded_gr1_game(ConstraintCover *cov,
                                               const bool *seen,
                                               const Gr1Parts *parts) {
  Aig *g = aig_new();
  if (!g)
    return nullptr;
  const Node *assume = parts->safety_assume, *guarantee = parts->safety_gua;
  uint32_t ass_depth = abssynthe_global_x_depth(assume);
  uint32_t gua_depth = abssynthe_global_x_depth(guarantee);
  if (ass_depth == UINT32_MAX || gua_depth == UINT32_MAX) {
    aig_free(g);
    return nullptr;
  }
  uint32_t A = cov->aps.count;
  uint32_t depth = ass_depth > gua_depth ? ass_depth : gua_depth;
  // Weak-until operands may carry their own X-depth; widen the history window.
  for (uint32_t w = 0; w < parts->nweak; w++) {
    uint32_t da = abssynthe_x_depth(parts->weak[w].a);
    uint32_t db = abssynthe_x_depth(parts->weak[w].b);
    if (da > depth)
      depth = da;
    if (db > depth)
      depth = db;
  }
  uint32_t hist_count = (depth + 1) * (A ? A : 1);
  uint32_t *hist = malloc(hist_count * sizeof(uint32_t));
  if (!hist) {
    aig_free(g);
    return nullptr;
  }
  memset(hist, 0xff, hist_count * sizeof(uint32_t));
  AbssyntheCompile ctx = {g, cov, hist, A ? A : 1};
  for (uint32_t a = 0; a < cov->aps.count; a++)
    if (seen[a] && residual_signal_matches(cov, a, AP_FLAG_INPUT))
      hist_set(&ctx, 0, a, aig_input(g, ap_table_name(&cov->aps, a)));
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
  for (uint32_t d = 1; d <= depth; d++)
    for (uint32_t a = 0; a < A; a++) {
      uint32_t prev = hist_lit(&ctx, d - 1, a);
      if (prev != UINT32_MAX)
        hist_set(&ctx, d, a, aig_latch(g, prev, AIG_FALSE));
    }
  uint32_t valid = AIG_TRUE;
  for (uint32_t d = 0; d < depth; d++)
    valid = aig_latch(g, valid, AIG_FALSE);
  // `first` marks t=0 (latch is 0 at t=0, 1 ever after), gating initial
  // conditions, exactly as the strict-safety encoder does.
  uint32_t past_first = aig_latch(g, AIG_TRUE, AIG_FALSE);
  uint32_t first = aig_not(past_first);

#define UGR1_FAIL()                                                            \
  do {                                                                         \
    free(hist);                                                                \
    aig_free(g);                                                               \
    return nullptr;                                                            \
  } while (0)

  uint32_t gua_ok = abssynthe_compile_global_at_lag(&ctx, guarantee, depth);
  if (gua_ok == UINT32_MAX)
    UGR1_FAIL();
  uint32_t bad = aig_and(g, valid, aig_not(gua_ok));

  // Compile the initial conditions (Boolean, evaluated at t=0 / lag 0).
  uint32_t env_init_ok = abssynthe_compile_at_lag(&ctx, parts->env_init, 0);
  uint32_t sys_init_ok = abssynthe_compile_at_lag(&ctx, parts->sys_init, 0);
  if (env_init_ok == UINT32_MAX || sys_init_ok == UINT32_MAX)
    UGR1_FAIL();
  bool has_env_init = parts->env_init->kind != NODE_TRUE;
  bool has_sys_init = parts->sys_init->kind != NODE_TRUE;

  // Safety assumption and env-init first, so `violated` can lift the liveness
  // obligation too (a broken env assumption wins the GR(1) implication
  // vacuously).
  uint32_t violated = AIG_FALSE;
  uint32_t ass_window_ok = AIG_TRUE;
  if (assume->kind != NODE_TRUE || has_env_init) {
    uint32_t vnext;
    violated = aig_latch(g, AIG_FALSE, AIG_FALSE);
    vnext = violated;
    if (assume->kind != NODE_TRUE) {
      uint32_t ass_ok = abssynthe_compile_global_at_lag(&ctx, assume, depth);
      ass_window_ok = abssynthe_compile_assumption_window(&ctx, assume, depth);
      if (ass_ok == UINT32_MAX || ass_window_ok == UINT32_MAX)
        UGR1_FAIL();
      vnext = aig_or(g, vnext, aig_and(g, valid, aig_not(ass_ok)));
    }
    if (has_env_init)
      vnext = aig_or(g, vnext, aig_and(g, first, aig_not(env_init_ok)));
    if (!aig_set_latch_next(g, violated, vnext))
      UGR1_FAIL();
  }

  // System justice goals: each is G F !pending via a pending monitor latch.
  for (uint32_t j = 0; j < parts->njustice; j++) {
    uint32_t tgt =
        abssynthe_compile_at_lag(&ctx, parts->justice[j].target, depth);
    if (tgt == UINT32_MAX)
      UGR1_FAIL();
    uint32_t req = AIG_TRUE; // recurrence G F J == response with req = true
    if (parts->justice[j].req) {
      req = abssynthe_compile_at_lag(&ctx, parts->justice[j].req, depth);
      if (req == UINT32_MAX)
        UGR1_FAIL();
    }
    uint32_t p = aig_latch(g, AIG_FALSE, AIG_FALSE);
    uint32_t next = aig_and(g, aig_not(violated),
                            aig_and(g, aig_not(tgt), aig_or(g, p, req)));
    if (!aig_set_latch_next(g, p, next))
      UGR1_FAIL();
    uint32_t jlit = aig_not(p);
    aig_add_justice(g, &jlit, 1, "gr1_justice");
  }

  // Environment fairness assumptions G F a, each sampled into a latch so its
  // fairness literal is a state predicate.
  for (uint32_t i = 0; i < parts->nfairness; i++) {
    uint32_t fair = abssynthe_compile_at_lag(&ctx, parts->fairness[i], depth);
    if (fair == UINT32_MAX)
      UGR1_FAIL();
    uint32_t fa = aig_latch(g, fair, AIG_FALSE);
    aig_add_fairness(g, fa, "gr1_fairness");
  }

  // Weak-until guarantees `a W b`: a pure-safety obligation that a holds until
  // b (or forever).  A `released` latch records that b has held; the system
  // loses if a fails before b is ever seen.
  for (uint32_t w = 0; w < parts->nweak; w++) {
    uint32_t a_ok = abssynthe_compile_at_lag(&ctx, parts->weak[w].a, depth);
    uint32_t b_ok = abssynthe_compile_at_lag(&ctx, parts->weak[w].b, depth);
    if (a_ok == UINT32_MAX || b_ok == UINT32_MAX)
      UGR1_FAIL();
    uint32_t released = aig_latch(g, AIG_FALSE, AIG_FALSE);
    if (!aig_set_latch_next(g, released,
                            aig_or(g, released, aig_and(g, valid, b_ok))))
      UGR1_FAIL();
    uint32_t weak_bad =
        aig_and(g, valid,
                aig_and(g, aig_not(released),
                        aig_and(g, aig_not(a_ok), aig_not(b_ok))));
    bad = aig_or(g, bad, weak_bad);
  }

  // The system must also satisfy its initial condition at t=0.
  if (has_sys_init)
    bad = aig_or(g, bad, aig_and(g, first, aig_not(sys_init_ok)));
  bad = aig_and(g, bad, aig_and(g, aig_not(violated), ass_window_ok));
#undef UGR1_FAIL
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

// Synthesize one safety game with AbsSynthe.  The backend slice accepts
// strategy AAGs that expose each controllable as an output named either
// `<name>` or `controllable_<name>`.
static Aig *run_abssynthe_game(const char *prog, ConstraintCover *cov,
                               const bool *seen, Aig *game, int *unreal) {
  *unreal = 0;
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

  // Extra AbsSynthe solver flags (e.g. "-a" abstraction, "-t" transition
  // decomposition) from $ABSSYNTHE_FLAGS, space-separated.  Parallel/ordering
  // flags (-p/-s) are unsafe here: their forked workers race on the -o strategy
  // file.  Flags go before -o (getopt scans options up to the positional spec).
#define MAX_ABS_FLAGS 8
  char *argv[MAX_ABS_FLAGS + 5];
  uint32_t an = 0;
  argv[an++] = (char *)prog;
  const char *flagenv = getenv("ABSSYNTHE_FLAGS");
  char *flagbuf = (flagenv && *flagenv) ? strdup(flagenv) : nullptr;
  if (flagbuf)
    for (char *t = strtok(flagbuf, " \t"); t && an <= MAX_ABS_FLAGS;
         t = strtok(nullptr, " \t"))
      argv[an++] = t;
  argv[an++] = (char *)"-o";
  argv[an++] = strat_path;
  argv[an++] = game_path;
  argv[an] = nullptr;
#undef MAX_ABS_FLAGS
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  posix_spawn_file_actions_addopen(&fa, 1, "/dev/null", O_WRONLY, 0);
  posix_spawn_file_actions_addopen(&fa, 2, "/dev/null", O_WRONLY, 0);
  pid_t pid;
  int rc = posix_spawnp(&pid, prog, &fa, nullptr, argv, environ);
  posix_spawn_file_actions_destroy(&fa);
  free(flagbuf);
  if (rc != 0) {
    cleanup_abssynthe_tmp(dir, game_path, strat_path);
    return nullptr;
  }

  // Optional wall-clock cap on the AbsSynthe child ($ABSSYNTHE_TIMEOUT seconds;
  // 0/unset = unbounded).  On timeout, kill the child and return no strategy so
  // the caller falls back to ltlsynt rather than hanging on a hard BDD game.
  const char *to_env = getenv("ABSSYNTHE_TIMEOUT");
  long timeout_s = (to_env && *to_env) ? strtol(to_env, nullptr, 10) : 0;
  int status;
  if (timeout_s > 0) {
    struct timespec slice = {0, 20L * 1000 * 1000}; // 20 ms
    long ticks = timeout_s * 50, i = 0;             // 50 polls per second
    pid_t r = 0;
    for (; i < ticks; i++) {
      r = waitpid(pid, &status, WNOHANG);
      if (r != 0)
        break;
      nanosleep(&slice, nullptr);
    }
    if (r == 0) { // still running at the deadline
      kill(pid, SIGKILL);
      waitpid(pid, &status, 0);
      cleanup_abssynthe_tmp(dir, game_path, strat_path);
      return nullptr;
    }
    if (r < 0) {
      cleanup_abssynthe_tmp(dir, game_path, strat_path);
      return nullptr;
    }
  } else {
    waitpid(pid, &status, 0);
  }
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

// Self-verification: run the external verifier (PROG --aiger FILE --formula
// LTL) on a synthesized controller against the original cluster spec.  Returns
// true ONLY when the verifier reports a definite violation (exit 1).  On
// "verified" (0), an AP mismatch, a verifier error/timeout/OOM, or any other
// code it returns false (keep the controller) -- an inconclusive check never
// turns a sound solve into a fallback.  `controller` has cluster-named
// inputs/outputs (the controllable_ prefix was stripped on read-back), matching
// the formula.
static bool controller_violates_spec(const char *verifier, Aig *controller,
                                     const Node *root, LtlFormat fmt,
                                     bool finite) {
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

static Aig *run_abssynthe(const char *prog, ConstraintCover *cov,
                          const bool *seen, const Node *root, int *unreal) {
  return run_abssynthe_game(prog, cov, seen,
                            build_abssynthe_game(cov, seen, root), unreal);
}

static Aig *run_abssynthe_wr(const char *prog, ConstraintCover *cov,
                             const bool *seen, const Node *root, int *unreal) {
  return run_abssynthe_game(prog, cov, seen,
                            build_abssynthe_wr_game(cov, seen, root), unreal);
}

static Aig *run_abssynthe_strict_safety(const char *prog, ConstraintCover *cov,
                                        const bool *seen, const Node *sys,
                                        const Node *env, int *unreal) {
  return run_abssynthe_game(
      prog, cov, seen, build_abssynthe_strict_safety_game(cov, seen, sys, env),
      unreal);
}

static Aig *run_abssynthe_gr1(const char *prog, ConstraintCover *cov,
                              const bool *seen, const Gr1Parts *parts,
                              int *unreal) {
  return run_abssynthe_game(
      prog, cov, seen, build_abssynthe_unbounded_gr1_game(cov, seen, parts),
      unreal);
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
      "  --bound N                    step bound for the bounded-liveness "
      "AbsSynthe path (default 4 / $ABSSYNTHE_BOUND)\n"
      "  $ABSSYNTHE_FLAGS             extra AbsSynthe solver flags, e.g. "
      "\"-a\" "
      "(abstraction) or \"-t\"; -p/-s are unsafe with -o\n"
      "  $ABSSYNTHE_TIMEOUT           per-call wall-clock cap for AbsSynthe "
      "(seconds; 0/unset = unlimited); on timeout falls back to ltlsynt\n"
      "  $ABSSYNTHE_MIN_APS           skip AbsSynthe for clusters with fewer "
      "APs than this (0/unset = no gate; ltlsynt is faster on tiny clusters)\n"
      "  --verify PROG                self-verify each AbsSynthe controller "
      "(PROG --aiger F --formula L; exit 1 = violation) and fall back to "
      "ltlsynt ($TLSFCOMPOSE_VERIFY)\n"
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
  const char *abssynthe_path = nullptr, *verify_path = nullptr;
  unsigned long bound_opt = 0; // 0 = unset (use $ABSSYNTHE_BOUND or default)
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
    } else if (strcmp(a, "--verify") == 0) {
      verify_path = NEED_ARG();
    } else if (strcmp(a, "--bound") == 0) {
      const char *v = NEED_ARG();
      char *end;
      bound_opt = strtoul(v, &end, 10);
      if (*end != '\0' || bound_opt == 0) {
        fprintf(stderr, "tlsfcompose: --bound expects a positive integer\n");
        return 1;
      }
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
    if (aiger && csnf_constraint_has_local_aiger(csnf, comp, i))
      continue; // discharged by a direct local AIGER controller
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
    // Optional self-verification: when set, each AbsSynthe-synthesized cluster
    // controller is model-checked against the cluster spec and, if it provably
    // violates it, discarded in favour of the ltlsynt fallback.
    const char *verify_env = getenv("TLSFCOMPOSE_VERIFY");
    const char *verifier = verify_path                   ? verify_path
                           : (verify_env && *verify_env) ? verify_env
                                                         : nullptr;
    // Bound for the bounded-liveness AbsSynthe path: --bound, else
    // $ABSSYNTHE_BOUND, else a small default.
    const char *bound_env = getenv("ABSSYNTHE_BOUND");
    uint32_t bound_k = bound_opt ? (uint32_t)bound_opt
                       : (bound_env && *bound_env)
                           ? (uint32_t)strtoul(bound_env, nullptr, 10)
                           : 4;
    if (bound_k == 0)
      bound_k = 4;
    // Cost gate: skip AbsSynthe for clusters with fewer than this many APs
    // ($ABSSYNTHE_MIN_APS, default 0 = no gate).  AbsSynthe's fixed spawn +
    // CUDD-init overhead dominates on small clusters; ltlsynt is faster there.
    const char *min_aps_env = getenv("ABSSYNTHE_MIN_APS");
    uint32_t abs_min_aps = (min_aps_env && *min_aps_env)
                               ? (uint32_t)strtoul(min_aps_env, nullptr, 10)
                               : 0;
    Aig *g = aig_new();
    for (uint32_t o = 0; o < A; o++) // all declared and residual env inputs
      if (residual_signal_matches(cov, o, AP_FLAG_INPUT))
        (void)aig_input(g, ap_table_name(&cov->aps, o));

    // Clusters first (so a decoder reading a synthesized output resolves).
    for (uint32_t k = 0; k < K && rc == 0; k++) {
      if (keys[k] == A) // output-free: no controller needed, skip
        continue;
      Node *root =
          residual_build_cluster(spec, cov, rf, key, keys[k], false, N, seen);
      if (!root) {
        rc = 1;
        break;
      }
      ClusterShape shape = cluster_shape(spec, root);
      int unreal = 0;
      Aig *sub = nullptr;
      const char *fallback_detail =
          nullptr; // set when AbsSynthe ran but failed
      const Node *strict_sys = nullptr, *strict_env = nullptr;
      // Cost gate: only engage AbsSynthe backends if the cluster meets the AP
      // minimum (spawn + CUDD-init overhead dominates on tiny clusters).
      bool abs_cost_ok = cov->aps.count >= abs_min_aps;
      bool use_abs_direct =
          abs_prog && abs_cost_ok && abssynthe_eligible(root, finite);
      bool use_abs_strict =
          abs_prog && abs_cost_ok && !finite && !use_abs_direct &&
          shape.gr_level == 0 && !shape.has_liveness &&
          abssynthe_strict_safety_parts(root, &strict_sys, &strict_env);
      // Weak-until / release safety: a pure-safety cluster `AND(U, A -> G)`
      // with W/R on any side is encoded exactly (monitors), preferred over the
      // lossy bounded reduction below.
      bool use_abs_wr = abs_prog && abs_cost_ok && !finite && !use_abs_direct &&
                        !use_abs_strict && !shape.has_liveness &&
                        (shape.has_weak_until || shape.has_release) &&
                        wr_structural_supported(root);
      // Bounded GR(1): bound the guarantee liveness (F -> within k steps); if
      // the cluster then becomes a pure-safety game (no fairness assumption
      // survives), solve it with the existing AbsSynthe safety solver.
      const Node *bounded_root = nullptr;
      if (abs_prog && abs_cost_ok && !finite && !use_abs_direct &&
          !use_abs_strict && !use_abs_wr &&
          (shape.has_liveness || shape.has_weak_until || shape.has_release)) {
        Node *br = bound_liveness(spec->arena, root, bound_k, true);
        if (abssynthe_eligible(br, finite))
          bounded_root = br;
      }
      // Complete GR(1): a fairness-bearing cluster `G F a -> safety & justice`
      // (which the bounded-liveness path cannot handle because the `G F a`
      // assumption is unsound to bound) is emitted as a real justice/fairness
      // game and solved by AbsSynthe's GR(1) fixpoint.
      Gr1Parts gp;
      bool use_gr1 = abs_prog && abs_cost_ok && !finite && !use_abs_direct &&
                     !use_abs_strict && !use_abs_wr && !bounded_root &&
                     abssynthe_gr1_parts(spec->arena, root, &gp);
      bool use_abs = use_abs_direct || use_abs_strict || use_abs_wr ||
                     bounded_root || use_gr1;
      const char *backend = use_abs ? "AbsSynthe" : "ltlsynt fallback";
      if (use_abs_direct) {
        sub = run_abssynthe(abs_prog, cov, seen, root, &unreal);
        if (!sub && !unreal) {
          // AbsSynthe failed (timeout / error): fall back to ltlsynt.
          use_abs = false;
          backend = "ltlsynt fallback (safety miss)";
          fallback_detail = "AbsSynthe returned no strategy; ltlsynt also "
                            "returned no strategy";
          sub =
              run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
        }
      } else if (use_abs_strict) {
        sub = run_abssynthe_strict_safety(abs_prog, cov, seen, strict_sys,
                                          strict_env, &unreal);
        if (!sub && !unreal) {
          // AbsSynthe failed: fall back to ltlsynt on the original formula.
          use_abs = false;
          backend = "ltlsynt fallback (strict safety miss)";
          fallback_detail = "AbsSynthe returned no strategy; ltlsynt also "
                            "returned no strategy";
          sub =
              run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
        }
      } else if (use_abs_wr) {
        backend = "AbsSynthe (W/R safety)";
        sub = run_abssynthe_wr(abs_prog, cov, seen, root, &unreal);
        if (!sub && !unreal) {
          // W/R monitor encoding is exact: trust UNREALIZABLE; fall back only
          // on error/timeout (unreal=0, no strategy).
          use_abs = false;
          backend = "ltlsynt fallback (W/R miss)";
          fallback_detail = "AbsSynthe returned no strategy; ltlsynt also "
                            "returned no strategy";
          sub =
              run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
        }
      } else if (bounded_root) {
        backend = "AbsSynthe (bounded)";
        sub = run_abssynthe(abs_prog, cov, seen, bounded_root, &unreal);
        if (!sub) {
          // Bounded miss (unrealizable at this k, or no strategy): the
          // unbounded game may still be realizable, so fall back to ltlsynt
          // rather than failing the spec.
          unreal = 0;
          use_abs = false;
          backend = "ltlsynt fallback (bounded miss)";
          sub =
              run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
        }
      } else if (use_gr1) {
        backend = "AbsSynthe (GR(1))";
        sub = run_abssynthe_gr1(abs_prog, cov, seen, &gp, &unreal);
        if (!sub) {
          // The complete GR(1) solver found no strategy (or called it
          // unrealizable -- the recognizer may over-constrain); defer to
          // ltlsynt rather than risk a false UNREALIZABLE.
          unreal = 0;
          use_abs = false;
          backend = "ltlsynt fallback (GR(1) miss)";
          sub =
              run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
        }
      } else {
        sub = run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
      }
      // Self-verification gate: a synthesized controller must satisfy the
      // ORIGINAL cluster spec (`root`, not a bounded/strict surrogate).  If it
      // provably violates it, discard it and fall back to ltlsynt, so a
      // recognizer/encoder bug becomes a sound fallback rather than a wrong
      // controller.  Inconclusive checks (verifier error/OOM) keep the result.
      if (verifier && use_abs && sub &&
          controller_violates_spec(verifier, sub, root, fmt, finite)) {
        fprintf(stderr,
                "tlsfcompose: cluster %u controller failed self-verification "
                "(%s); falling back to ltlsynt\n",
                k, backend);
        aig_free(sub);
        sub = nullptr;
        unreal = 0;
        use_abs = false;
        backend = "ltlsynt fallback (self-verification)";
        sub = run_ltlsynt_cluster(prog, cov, seen, root, fmt, finite, &unreal);
      }
      if (getenv("TLSFCOMPOSE_DEBUG"))
        fprintf(stderr, "tlsfcompose: cluster %u routed to %s\n", k, backend);
      if (unreal) {
        fprintf(stderr, "tlsfcompose: cluster %u is UNREALIZABLE (%s)\n", k,
                backend);
        rc = 1;
      } else if (!sub) {
        char reason[192];
        const char *detail =
            use_abs ? "AbsSynthe returned no usable strategy"
            : fallback_detail
                ? fallback_detail
                : cluster_ltlsynt_reason(&shape, finite, abs_prog != NULL,
                                         reason, sizeof reason);
        fprintf(stderr,
                "tlsfcompose: synthesis backend failed for cluster %u (%s: "
                "%s)\n",
                k, backend, detail);
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
    if (rc == 0 && !csnf_emit_local_aiger(csnf, comp, g)) {
      fprintf(stderr, "tlsfcompose: cannot encode local template controller\n");
      rc = 1;
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

  uint32_t K_visible = 0;
  for (uint32_t k = 0; k < K; k++)
    if (keys[k] != A)
      K_visible++;
  fprintf(out, "c compose: controllers=%u clusters=%u\n", comp->nelim,
          K_visible);

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
    print_ltl(dst, comp->elim[k].value, fmt, /*full_parens=*/false, finite,
              /*lower_atoms=*/false);
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

  for (uint32_t k = 0, ck = 0; k < K && rc == 0; k++) {
    if (keys[k] == A) // output-free: no controller needed, skip
      continue;
    Node *root =
        residual_build_cluster(spec, cov, rf, key, keys[k], false, N, seen);
    if (!root) {
      rc = 1;
      break;
    }
    if (out_dir) {
      char path[4096];
      snprintf(path, sizeof path, "%s/cluster.%u.ltl", out_dir, ck);
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
      print_ltl(cf, root, fmt, false, finite, /*lower_atoms=*/false);
      fclose(cf);
      fprintf(shf, "run cluster.%u.ltl \"", ck);
      residual_print_signals(shf, cov, seen, AP_FLAG_INPUT);
      fprintf(shf, "\" \"");
      residual_print_signals(shf, cov, seen, AP_FLAG_OUTPUT);
      fprintf(shf, "\"\n");
      fprintf(out, "c cluster %u file=cluster.%u.ltl outs=", ck, ck);
      residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, " ins=");
      residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
    } else {
      fprintf(out, "c cluster %u outs=", ck);
      residual_print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, " ins=");
      residual_print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
      print_ltl(out, root, fmt, false, finite, /*lower_atoms=*/false);
    }
    ck++;
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
