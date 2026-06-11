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

// Synthesize one cluster with ltlsynt: render `root` to LTL and pass the
// cluster's input/output interface.  Caller frees the returned strategy AIG.
static Aig *run_ltlsynt_cluster(const char *prog, ConstraintCover *cov,
                                const bool *seen, const Node *root,
                                LtlFormat fmt, bool finite, int *unreal) {
  char *ltl = ltl_string(root, fmt, finite);
  char *ins = nullptr, *outs = nullptr;
  size_t isz = 0, osz = 0;
  FILE *fi = open_memstream(&ins, &isz), *fo = open_memstream(&outs, &osz);
  residual_print_signals(fi, cov, seen, AP_FLAG_INPUT);
  residual_print_signals(fo, cov, seen, AP_FLAG_OUTPUT);
  fclose(fi);
  fclose(fo);
  Aig *sub = ltl ? run_ltlsynt(prog, ins, outs, ltl, unreal) : nullptr;
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

static bool abssynthe_eligible(const Node *root, bool finite) {
  if (finite)
    return false;
  if (root->kind == NODE_IMPL)
    return abssynthe_global_supported(root->lhs) &&
           abssynthe_global_x_depth(root->lhs) == 0 &&
           abssynthe_global_supported(root->rhs);
  return abssynthe_global_supported(root);
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

// Bucket the GR(1) consequent: sys-init Boolean conjuncts go to `sys_init`, the
// flat `assume -> guarantee` implication is split with gr1_collect, and a bare
// guarantee conjunct (no assume side) is collected directly.
static bool gr1_collect_consequent(Arena *a, const Node *n, Gr1Parts *p) {
  if (n->kind == NODE_AND)
    return gr1_collect_consequent(a, n->lhs, p) &&
           gr1_collect_consequent(a, n->rhs, p);
  if (abssynthe_initial_supported(n)) {
    p->sys_init = p->sys_init->kind == NODE_TRUE
                      ? n
                      : node_and(a, (Node *)p->sys_init, (Node *)n);
    return true;
  }
  if (n->kind == NODE_IMPL) // the flat GR(1) implication: assume -> guarantee
    return gr1_collect(a, n->lhs, true, p) && gr1_collect(a, n->rhs, false, p);
  return gr1_collect(a, n, false, p);
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
  // The remainder is the guarantee side: sys-init conjuncts, safety, and the
  // flat `(AND G F a) -> (AND justice)` implication (anywhere in the AND tree).
  // gr1_collect_consequent buckets them; the fairness/justice counts below
  // reject anything that is not actually a GR(1) cluster.
  if (!gr1_collect_consequent(a, root, p))
    return false;
  return p->nfairness > 0 && p->njustice > 0 &&
         abssynthe_global_x_depth(p->safety_assume) == 0;
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
  case NODE_NOT:
  case NODE_X:
  case NODE_G:
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_F:
    shape->has_liveness = true;
    cluster_shape_visit(n->arg, shape);
    return;
  case NODE_W:
    shape->has_weak_until = true;
    break;
  case NODE_R:
    shape->has_release = true;
    break;
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

static Aig *run_abssynthe(const char *prog, ConstraintCover *cov,
                          const bool *seen, const Node *root, int *unreal) {
  return run_abssynthe_game(prog, cov, seen,
                            build_abssynthe_game(cov, seen, root), unreal);
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
    // Bound for the bounded-liveness AbsSynthe path: --bound, else
    // $ABSSYNTHE_BOUND, else a small default.
    const char *bound_env = getenv("ABSSYNTHE_BOUND");
    uint32_t bound_k = bound_opt ? (uint32_t)bound_opt
                       : (bound_env && *bound_env)
                           ? (uint32_t)strtoul(bound_env, nullptr, 10)
                           : 4;
    if (bound_k == 0)
      bound_k = 4;
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
      ClusterShape shape = cluster_shape(spec, root);
      int unreal = 0;
      Aig *sub = nullptr;
      const Node *strict_sys = nullptr, *strict_env = nullptr;
      bool use_abs_direct = abs_prog && abssynthe_eligible(root, finite);
      bool use_abs_strict =
          abs_prog && !finite && !use_abs_direct && shape.gr_level == 0 &&
          !shape.has_liveness &&
          abssynthe_strict_safety_parts(root, &strict_sys, &strict_env);
      // Bounded GR(1): bound the guarantee liveness (F -> within k steps); if
      // the cluster then becomes a pure-safety game (no fairness assumption
      // survives), solve it with the existing AbsSynthe safety solver.
      const Node *bounded_root = nullptr;
      if (abs_prog && !finite && !use_abs_direct && !use_abs_strict &&
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
      bool use_gr1 = abs_prog && !finite && !use_abs_direct &&
                     !use_abs_strict && !bounded_root &&
                     abssynthe_gr1_parts(spec->arena, root, &gp);
      bool use_abs =
          use_abs_direct || use_abs_strict || bounded_root || use_gr1;
      const char *backend = use_abs ? "AbsSynthe" : "ltlsynt fallback";
      if (use_abs_direct) {
        sub = run_abssynthe(abs_prog, cov, seen, root, &unreal);
      } else if (use_abs_strict) {
        sub = run_abssynthe_strict_safety(abs_prog, cov, seen, strict_sys,
                                          strict_env, &unreal);
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
      if (unreal) {
        fprintf(stderr, "tlsfcompose: cluster %u is UNREALIZABLE (%s)\n", k,
                backend);
        rc = 1;
      } else if (!sub) {
        char reason[192];
        const char *detail =
            use_abs ? "AbsSynthe returned no usable strategy"
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
