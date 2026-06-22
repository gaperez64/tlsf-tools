// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/normalize.h"

#include "tlsf/nnf.h"
#include "tlsf/rewrite.h"

#include <stdlib.h>
#include <string.h>
#include <time.h>

// ---------------------------------------------------------------------------
// Name tables
// ---------------------------------------------------------------------------

static const char *const PASS_NAMES[TLSF_NORM_PASS_COUNT] = {
    [TLSF_NORM_PASS_SPLIT] = "split",
    [TLSF_NORM_PASS_NNF] = "nnf",
    [TLSF_NORM_PASS_WEAK] = "weak",
    [TLSF_NORM_PASS_BOOL_CANON] = "bool-canon",
    [TLSF_NORM_PASS_OR_TO_IMPL_PATTERN] = "or-to-impl-pattern",
    [TLSF_NORM_PASS_EQUIV_OUTPUT_SIDE] = "equiv-output-side",
    [TLSF_NORM_PASS_MUTEX_DEMORGAN] = "mutex-demorgan",
    [TLSF_NORM_PASS_ROUTE_SAFE] = "route-safe",
    [TLSF_NORM_PASS_SICKERT_STAGE2] = "sickert-stage2",
    [TLSF_NORM_PASS_SICKERT_STAGE3] = "sickert-stage3",
    [TLSF_NORM_PASS_PRE_INDEXED_X] = "pre-indexed-x",
    [TLSF_NORM_PASS_PRE_BOUNDED_BOOL] = "pre-bounded-bool",
    [TLSF_NORM_PASS_PRE_SPINE_SPLIT] = "pre-spine-split",
    [TLSF_NORM_PASS_PRE_WEAK] = "pre-weak",
};

static const char *const PHASE_NAMES[TLSF_NORM_PHASE_COUNT] = {
    [TLSF_NORM_PHASE_PRE_EXPAND] = "pre_expand",
    [TLSF_NORM_PHASE_MATCH] = "match",
    [TLSF_NORM_PHASE_ROUTE] = "route",
    [TLSF_NORM_PHASE_VISIBLE] = "visible",
    [TLSF_NORM_PHASE_BENCH] = "bench",
};

const char *tlsf_norm_pass_name(TlsfNormPass p) {
  return p < TLSF_NORM_PASS_COUNT ? PASS_NAMES[p] : "?";
}
const char *tlsf_norm_phase_name(TlsfNormPhase p) {
  return p < TLSF_NORM_PHASE_COUNT ? PHASE_NAMES[p] : "?";
}
const char *tlsf_norm_reject_name(TlsfNormRejectReason r) {
  switch (r) {
  case TLSF_NORM_REJECT_NONE:
    return "none";
  case TLSF_NORM_REJECT_GROWTH:
    return "growth";
  case TLSF_NORM_REJECT_NODES:
    return "nodes";
  case TLSF_NORM_REJECT_FINITE_WORD:
    return "finite_word";
  case TLSF_NORM_REJECT_PHASE:
    return "phase";
  case TLSF_NORM_REJECT_NOT_APPLICABLE:
    return "not_applicable";
  }
  return "?";
}

// ---------------------------------------------------------------------------
// Rule metadata.  Booleans are: equiv_inf, equiv_fin, pre, match, route, vis,
// may_grow, growth_cap%.
// ---------------------------------------------------------------------------

#define RI(R, N, EI, EF, PR, MA, RO, VI, GROW, CAP, NOTE)                      \
  [R] = {.rule = R,                                                            \
         .name = N,                                                            \
         .equivalence_infinite = EI,                                           \
         .equivalence_finite = EF,                                             \
         .allowed_pre_expand = PR,                                             \
         .allowed_match = MA,                                                  \
         .allowed_route = RO,                                                  \
         .allowed_visible = VI,                                                \
         .may_increase_nodes = GROW,                                           \
         .default_growth_cap_percent = CAP,                                    \
         .proof_note = NOTE}

static const TlsfNormRuleInfo RULES[TLSF_NORM_RULE_COUNT] = {
    RI(TLSF_NORM_RULE_WEAK_DOUBLE_NEG, "weak-double-neg", true, true, false,
       true, true, true, false, 0, "!!x = x"),
    RI(TLSF_NORM_RULE_WEAK_CONST_FOLD, "weak-const-fold", true, true, false,
       true, true, true, false, 0, "syfco -s0 constant folding"),
    RI(TLSF_NORM_RULE_WEAK_IDEMPOTENT, "weak-idempotent", true, true, false,
       true, true, true, false, 0, "x&&x=x, GGx=Gx, FFx=Fx"),
    RI(TLSF_NORM_RULE_BOOL_FLATTEN_AND, "bool-flatten-and", true, true, false,
       true, true, true, false, 0, "associativity of &&"),
    RI(TLSF_NORM_RULE_BOOL_FLATTEN_OR, "bool-flatten-or", true, true, false,
       true, true, true, false, 0, "associativity of ||"),
    RI(TLSF_NORM_RULE_BOOL_SORT_AND, "bool-sort-and", true, true, false, true,
       true, true, false, 0, "commutativity + idempotence of &&"),
    RI(TLSF_NORM_RULE_BOOL_SORT_OR, "bool-sort-or", true, true, false, true,
       true, true, false, 0, "commutativity + idempotence of ||"),
    RI(TLSF_NORM_RULE_OR_TO_RESPONSE_IMPL, "or-to-response-impl", true, true,
       false, true, true, true, false, 0, "!r||Fg = r->Fg"),
    RI(TLSF_NORM_RULE_OR_TO_GUARDED_NEXT_IMPL, "or-to-guarded-next-impl", true,
       true, false, true, true, true, false, 0, "!r||Xo = r->Xo"),
    RI(TLSF_NORM_RULE_EQUIV_OUTPUT_LEFT, "equiv-output-left", true, true, false,
       true, true, true, false, 0, "a<->b = b<->a"),
    RI(TLSF_NORM_RULE_MUTEX_DEMORGAN_PAIR, "mutex-demorgan-pair", true, true,
       false, true, true, true, false, 0, "!a||!b = !(a&&b)"),
    RI(TLSF_NORM_RULE_ROUTE_NNF, "route-nnf", true, true, false, true, true,
       true, false, 0, "negation normal form"),
    RI(TLSF_NORM_RULE_ROUTE_PUSH_G_IN, "route-push-g-in", true, true, false,
       true, true, true, true, 200, "G(a&&b)=Ga&&Gb"),
    RI(TLSF_NORM_RULE_ROUTE_PUSH_X_IN, "route-push-x-in", true, true, false,
       true, true, true, true, 200, "X(a&&b)=Xa&&Xb"),
    RI(TLSF_NORM_RULE_SICKERT_LIMIT_LIFT, "sickert-limit-lift", true, false,
       false, true, true, true, true, 400, "C[GF p]=(GF p&&C[true])||C[false]"),
    RI(TLSF_NORM_RULE_SICKERT_GF_W, "sickert-gf-w", true, false, false, true,
       true, true, true, 400, "GF C[a W b] = GF C[a U b]||(FG a&&GF C[true])"),
    RI(TLSF_NORM_RULE_SICKERT_FG_U, "sickert-fg-u", true, false, false, true,
       true, true, true, 400, "FG C[a U b]=(GF b&&FG C[a W b])||FG C[false]"),
    RI(TLSF_NORM_RULE_PRE_X0, "pre-x0", true, true, true, false, false, false,
       false, 0, "X[0] p = p"),
    RI(TLSF_NORM_RULE_PRE_XN_FLATTEN, "pre-xn-flatten", true, true, true, false,
       false, false, false, 0, "X[m]X[n] p = X[m+n] p"),
    RI(TLSF_NORM_RULE_PRE_XN_BOOL_DISTRIBUTE, "pre-xn-bool-distribute", true,
       true, true, false, false, false, true, 300, "X[n](a&&b)=X[n]a&&X[n]b"),
    RI(TLSF_NORM_RULE_PRE_BOUNDED_SINGLETON, "pre-bounded-singleton", true,
       true, true, false, false, false, false, 0, "&&[i:i] p = p[i]"),
    RI(TLSF_NORM_RULE_PRE_BOUNDED_EMPTY, "pre-bounded-empty", true, true, true,
       false, false, false, false, 0, "&&[i:j>i] = true / ||[..] = false"),
    RI(TLSF_NORM_RULE_PRE_BOUNDED_CONST_FOLD, "pre-bounded-const-fold", true,
       true, true, false, false, false, false, 0, "&&[i:j] true = true"),
    RI(TLSF_NORM_RULE_PRE_SPINE_SPLIT, "pre-spine-split", true, true, true,
       false, false, false, false, 0, "G(A&&B) -> G A, G B"),
    RI(TLSF_NORM_RULE_PRE_WEAK, "pre-weak", true, true, true, false, false,
       false, false, 0, "high-level weak simplification"),
};
#undef RI

const TlsfNormRuleInfo *tlsf_norm_rule_info(TlsfNormRule r) {
  return r < TLSF_NORM_RULE_COUNT ? &RULES[r] : nullptr;
}
const char *tlsf_norm_rule_name(TlsfNormRule r) {
  return r < TLSF_NORM_RULE_COUNT ? RULES[r].name : "?";
}

// ---------------------------------------------------------------------------
// Pass -> rules mapping (for soundness/phase checking) and primary rule (for
// stats attribution).
// ---------------------------------------------------------------------------

static uint32_t pass_rules(TlsfNormPass p, TlsfNormRule out[4]) {
  switch (p) {
  case TLSF_NORM_PASS_SPLIT:
    return 0; // distributes G/X over && + splits; equivalence-preserving
  case TLSF_NORM_PASS_NNF:
    out[0] = TLSF_NORM_RULE_ROUTE_NNF;
    return 1;
  case TLSF_NORM_PASS_WEAK:
    out[0] = TLSF_NORM_RULE_WEAK_DOUBLE_NEG;
    out[1] = TLSF_NORM_RULE_WEAK_CONST_FOLD;
    out[2] = TLSF_NORM_RULE_WEAK_IDEMPOTENT;
    return 3;
  case TLSF_NORM_PASS_BOOL_CANON:
    out[0] = TLSF_NORM_RULE_BOOL_FLATTEN_AND;
    out[1] = TLSF_NORM_RULE_BOOL_FLATTEN_OR;
    out[2] = TLSF_NORM_RULE_BOOL_SORT_AND;
    out[3] = TLSF_NORM_RULE_BOOL_SORT_OR;
    return 4;
  case TLSF_NORM_PASS_OR_TO_IMPL_PATTERN:
    out[0] = TLSF_NORM_RULE_OR_TO_RESPONSE_IMPL;
    out[1] = TLSF_NORM_RULE_OR_TO_GUARDED_NEXT_IMPL;
    return 2;
  case TLSF_NORM_PASS_EQUIV_OUTPUT_SIDE:
    out[0] = TLSF_NORM_RULE_EQUIV_OUTPUT_LEFT;
    return 1;
  case TLSF_NORM_PASS_MUTEX_DEMORGAN:
    out[0] = TLSF_NORM_RULE_MUTEX_DEMORGAN_PAIR;
    return 1;
  case TLSF_NORM_PASS_ROUTE_SAFE:
    out[0] = TLSF_NORM_RULE_ROUTE_NNF;
    out[1] = TLSF_NORM_RULE_ROUTE_PUSH_G_IN;
    out[2] = TLSF_NORM_RULE_ROUTE_PUSH_X_IN;
    return 3;
  case TLSF_NORM_PASS_SICKERT_STAGE2:
    out[0] = TLSF_NORM_RULE_SICKERT_LIMIT_LIFT;
    return 1;
  case TLSF_NORM_PASS_SICKERT_STAGE3:
    out[0] = TLSF_NORM_RULE_SICKERT_GF_W;
    out[1] = TLSF_NORM_RULE_SICKERT_FG_U;
    return 2;
  case TLSF_NORM_PASS_PRE_INDEXED_X:
    out[0] = TLSF_NORM_RULE_PRE_X0;
    out[1] = TLSF_NORM_RULE_PRE_XN_FLATTEN;
    return 2;
  case TLSF_NORM_PASS_PRE_BOUNDED_BOOL:
    out[0] = TLSF_NORM_RULE_PRE_BOUNDED_SINGLETON;
    out[1] = TLSF_NORM_RULE_PRE_BOUNDED_EMPTY;
    out[2] = TLSF_NORM_RULE_PRE_BOUNDED_CONST_FOLD;
    return 3;
  case TLSF_NORM_PASS_PRE_SPINE_SPLIT:
    out[0] = TLSF_NORM_RULE_PRE_SPINE_SPLIT;
    return 1;
  case TLSF_NORM_PASS_PRE_WEAK:
    out[0] = TLSF_NORM_RULE_PRE_WEAK;
    return 1;
  default:
    return 0;
  }
}

static TlsfNormRule pass_primary_rule(TlsfNormPass p) {
  TlsfNormRule r[4];
  return pass_rules(p, r) ? r[0] : TLSF_NORM_RULE_COUNT;
}

static bool rule_allowed_in_phase(const TlsfNormRuleInfo *ri,
                                  TlsfNormPhase phase) {
  switch (phase) {
  case TLSF_NORM_PHASE_PRE_EXPAND:
    return ri->allowed_pre_expand;
  case TLSF_NORM_PHASE_MATCH:
    return ri->allowed_match;
  case TLSF_NORM_PHASE_ROUTE:
    return ri->allowed_route;
  case TLSF_NORM_PHASE_VISIBLE:
  case TLSF_NORM_PHASE_BENCH:
    return ri->allowed_visible;
  default:
    return false;
  }
}

static bool pass_is_pre(TlsfNormPass p) {
  return p == TLSF_NORM_PASS_PRE_INDEXED_X ||
         p == TLSF_NORM_PASS_PRE_BOUNDED_BOOL ||
         p == TLSF_NORM_PASS_PRE_SPINE_SPLIT || p == TLSF_NORM_PASS_PRE_WEAK;
}

bool tlsf_norm_schedule_is_pre(const TlsfNormSchedule *sch) {
  for (uint32_t i = 0; i < sch->count; i++)
    if (pass_is_pre(sch->items[i].pass))
      return true;
  return false;
}
bool tlsf_norm_schedule_is_post(const TlsfNormSchedule *sch) {
  for (uint32_t i = 0; i < sch->count; i++)
    if (!pass_is_pre(sch->items[i].pass))
      return true;
  return false;
}

// ---------------------------------------------------------------------------
// Schedule parsing
// ---------------------------------------------------------------------------

typedef struct {
  TlsfNormPassSpec *v;
  uint32_t n, cap;
} SpecVec;

static bool sv_push(SpecVec *s, TlsfNormPass p, uint32_t iter) {
  if (s->n == s->cap) {
    uint32_t nc = s->cap ? s->cap * 2 : 16;
    TlsfNormPassSpec *nv = realloc(s->v, nc * sizeof(*nv));
    if (!nv)
      return false;
    s->v = nv;
    s->cap = nc;
  }
  s->v[s->n].pass = p;
  s->v[s->n].max_iter = iter;
  s->n++;
  return true;
}

// Resolve a bare pass name (or the "boolean" alias) to a pass id.
static bool pass_from_name(const char *name, TlsfNormPass *out) {
  if (strcmp(name, "boolean") == 0) {
    *out = TLSF_NORM_PASS_WEAK;
    return true;
  }
  for (TlsfNormPass p = 0; p < TLSF_NORM_PASS_COUNT; p++)
    if (strcmp(name, PASS_NAMES[p]) == 0) {
      *out = p;
      return true;
    }
  return false;
}

#define PROFILE_REPEAT_CAP 16

// Expand one token "name[:N]" into specs.  Returns false on unknown name.
static bool expand_token(SpecVec *out, const char *base, uint32_t iter) {
  TlsfNormPass p;
  if (pass_from_name(base, &p))
    return sv_push(out, p, iter);

  uint32_t rep = iter ? iter : 1;
  if (rep > PROFILE_REPEAT_CAP)
    rep = PROFILE_REPEAT_CAP;

  if (strcmp(base, "off") == 0)
    return true;
  if (strcmp(base, "match-safe") == 0) {
    static const TlsfNormPass blk[] = {
        TLSF_NORM_PASS_WEAK,
        TLSF_NORM_PASS_BOOL_CANON,
        TLSF_NORM_PASS_OR_TO_IMPL_PATTERN,
        TLSF_NORM_PASS_EQUIV_OUTPUT_SIDE,
        TLSF_NORM_PASS_MUTEX_DEMORGAN,
    };
    for (uint32_t r = 0; r < rep; r++)
      for (size_t k = 0; k < sizeof blk / sizeof *blk; k++)
        if (!sv_push(out, blk[k], 1))
          return false;
    return true;
  }
  if (strcmp(base, "pre-safe") == 0) {
    static const TlsfNormPass blk[] = {
        TLSF_NORM_PASS_PRE_INDEXED_X,
        TLSF_NORM_PASS_PRE_BOUNDED_BOOL,
        TLSF_NORM_PASS_PRE_SPINE_SPLIT,
    };
    for (uint32_t r = 0; r < rep; r++)
      for (size_t k = 0; k < sizeof blk / sizeof *blk; k++)
        if (!sv_push(out, blk[k], 1))
          return false;
    return true;
  }
  if (strcmp(base, "sickert-bounded") == 0) {
    if (!sv_push(out, TLSF_NORM_PASS_SICKERT_STAGE2, rep))
      return false;
    return sv_push(out, TLSF_NORM_PASS_SICKERT_STAGE3, rep);
  }
  return false;
}

bool tlsf_norm_parse_schedule(Arena *a, const char *s, const char *tool,
                              TlsfNormSchedule *out) {
  out->items = nullptr;
  out->count = 0;
  if (!s || !*s)
    return true;

  SpecVec sv = {0};
  char *dup = strdup(s);
  if (!dup)
    return false;
  bool ok = true;
  for (char *tok = strtok(dup, ","); tok; tok = strtok(nullptr, ",")) {
    while (*tok == ' ')
      tok++;
    char *colon = strchr(tok, ':');
    uint32_t iter = 0;
    if (colon) {
      *colon = '\0';
      char *end;
      long v = strtol(colon + 1, &end, 10);
      if (*end != '\0' || v < 0) {
        fprintf(stderr, "%s: bad iteration count in '%s'\n", tool, tok);
        ok = false;
        break;
      }
      iter = (uint32_t)v;
    }
    if (!*tok)
      continue;
    if (!expand_token(&sv, tok, iter)) {
      fprintf(stderr, "%s: unknown normalization pass/profile '%s'\n", tool,
              tok);
      ok = false;
      break;
    }
  }
  free(dup);
  if (!ok) {
    free(sv.v);
    return false;
  }

  out->items = ARENA_ALLOC_N(a, TlsfNormPassSpec, sv.n ? sv.n : 1);
  for (uint32_t i = 0; i < sv.n; i++)
    out->items[i] = sv.v[i];
  out->count = sv.n;
  free(sv.v);
  return true;
}

const char *tlsf_norm_schedule_string(Arena *a, const TlsfNormSchedule *sch) {
  if (sch->count == 0)
    return "off";
  size_t cap = 1;
  for (uint32_t i = 0; i < sch->count; i++)
    cap += strlen(tlsf_norm_pass_name(sch->items[i].pass)) + 14;
  char *buf = ARENA_ALLOC_N(a, char, cap);
  size_t off = 0;
  for (uint32_t i = 0; i < sch->count; i++) {
    const char *nm = tlsf_norm_pass_name(sch->items[i].pass);
    uint32_t it = sch->items[i].max_iter;
    if (i)
      buf[off++] = ',';
    if (it > 1)
      off += (size_t)snprintf(buf + off, cap - off, "%s:%u", nm, it);
    else
      off += (size_t)snprintf(buf + off, cap - off, "%s", nm);
  }
  buf[off] = '\0';
  return buf;
}

// ---------------------------------------------------------------------------
// Soundness / phase check
// ---------------------------------------------------------------------------

bool tlsf_norm_schedule_check(const TlsfNormSchedule *sch,
                              const TlsfNormOptions *opts, const char *tool,
                              TlsfNormRejectReason *reason) {
  if (reason)
    *reason = TLSF_NORM_REJECT_NONE;
  for (uint32_t i = 0; i < sch->count; i++) {
    TlsfNormRule rs[4];
    uint32_t nr = pass_rules(sch->items[i].pass, rs);
    for (uint32_t k = 0; k < nr; k++) {
      const TlsfNormRuleInfo *ri = &RULES[rs[k]];
      if (opts->finite_word && !ri->equivalence_finite) {
        if (reason)
          *reason = TLSF_NORM_REJECT_FINITE_WORD;
        fprintf(stderr,
                "%s: rule '%s' (pass '%s') is infinite-word-only; refusing on "
                "a finite-word spec\n",
                tool, ri->name, tlsf_norm_pass_name(sch->items[i].pass));
        return false;
      }
      if (!rule_allowed_in_phase(ri, opts->phase)) {
        if (reason)
          *reason = TLSF_NORM_REJECT_PHASE;
        fprintf(stderr,
                "%s: rule '%s' (pass '%s') is not allowed in phase '%s'\n",
                tool, ri->name, tlsf_norm_pass_name(sch->items[i].pass),
                tlsf_norm_phase_name(opts->phase));
        return false;
      }
    }
  }
  return true;
}

// ---------------------------------------------------------------------------
// Boolean canonicalization (flatten + sort + dedup over && / ||).
// ---------------------------------------------------------------------------

// Stable structural order; atoms compared by interned name string so the order
// is reproducible across runs (interned pointers are not).
static int struct_cmp(const Node *x, const Node *y) {
  if (x->kind != y->kind)
    return x->kind < y->kind ? -1 : 1;
  switch (x->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return 0;
  case NODE_AP:
    return strcmp(x->name, y->name);
  case NODE_INT:
    return x->ival < y->ival ? -1 : (x->ival > y->ival ? 1 : 0);
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return struct_cmp(x->arg, y->arg);
  default: {
    int c = struct_cmp(x->lhs, y->lhs);
    return c ? c : struct_cmp(x->rhs, y->rhs);
  }
  }
}

typedef struct {
  Node **v;
  uint32_t n, cap;
} NodeVec;

static void nv_push(Arena *a, NodeVec *s, Node *n) {
  if (s->n == s->cap) {
    uint32_t nc = s->cap ? s->cap * 2 : 8;
    Node **nv = ARENA_ALLOC_N(a, Node *, nc);
    for (uint32_t i = 0; i < s->n; i++)
      nv[i] = s->v[i];
    s->v = nv;
    s->cap = nc;
  }
  s->v[s->n++] = n;
}

static Node *bool_canon(Arena *a, Node *n);

static void collect_operands(Arena *a, Node *n, NodeKind k, NodeVec *out) {
  if (n->kind == k) {
    collect_operands(a, n->lhs, k, out);
    collect_operands(a, n->rhs, k, out);
  } else {
    nv_push(a, out, bool_canon(a, n));
  }
}

static Node *bool_canon(Arena *a, Node *n) {
  switch (n->kind) {
  case NODE_AND:
  case NODE_OR: {
    NodeKind k = n->kind;
    NodeVec ops = {0};
    collect_operands(a, n, k, &ops);
    // insertion sort (operand lists are small)
    for (uint32_t i = 1; i < ops.n; i++) {
      Node *key = ops.v[i];
      int32_t j = (int32_t)i - 1;
      while (j >= 0 && struct_cmp(ops.v[j], key) > 0) {
        ops.v[j + 1] = ops.v[j];
        j--;
      }
      ops.v[j + 1] = key;
    }
    // dedup adjacent equal
    uint32_t m = 0;
    for (uint32_t i = 0; i < ops.n; i++)
      if (i == 0 || struct_cmp(ops.v[i], ops.v[m - 1]) != 0)
        ops.v[m++] = ops.v[i];
    Node *acc = ops.v[0];
    for (uint32_t i = 1; i < m; i++)
      acc = k == NODE_AND ? node_and(a, acc, ops.v[i])
                          : node_or(a, acc, ops.v[i]);
    return acc;
  }
  case NODE_NOT:
    return node_not(a, bool_canon(a, n->arg));
  case NODE_X:
    return node_x(a, bool_canon(a, n->arg));
  case NODE_X_STRONG:
    return node_x_strong(a, bool_canon(a, n->arg));
  case NODE_F:
    return node_f(a, bool_canon(a, n->arg));
  case NODE_G:
    return node_g(a, bool_canon(a, n->arg));
  case NODE_IMPL:
    return node_impl(a, bool_canon(a, n->lhs), bool_canon(a, n->rhs));
  case NODE_EQUIV:
    return node_equiv(a, bool_canon(a, n->lhs), bool_canon(a, n->rhs));
  case NODE_U:
    return node_u(a, bool_canon(a, n->lhs), bool_canon(a, n->rhs));
  case NODE_R:
    return node_r(a, bool_canon(a, n->lhs), bool_canon(a, n->rhs));
  case NODE_W:
    return node_w(a, bool_canon(a, n->lhs), bool_canon(a, n->rhs));
  case NODE_M:
    return node_m(a, bool_canon(a, n->lhs), bool_canon(a, n->rhs));
  default:
    return n;
  }
}

// ---------------------------------------------------------------------------
// Per-pass transforms (pure: input AST untouched, result arena-allocated).
// Passes not yet implemented are no-ops; their schedules still parse, run, and
// report attempts so observability is available before the rewrite lands.
// ---------------------------------------------------------------------------

static Node *apply_pass_once(Arena *a, TlsfNormPass p, Node *n) {
  switch (p) {
  case TLSF_NORM_PASS_NNF:
    return to_nnf(a, n, true);
  case TLSF_NORM_PASS_WEAK:
    return apply_rewrites(a, n, RW_SIMPLIFY_WEAK);
  case TLSF_NORM_PASS_BOOL_CANON:
    return bool_canon(a, n);
  default:
    return n; // split + pre-* handled by callers; others land in later PRs
  }
}

// Structural equality (reuse the conservative interned-pointer comparison).
static bool node_eq(const Node *x, const Node *y) {
  if (x == y)
    return true;
  if (x->kind != y->kind)
    return false;
  switch (x->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_AP:
    return x->name == y->name;
  case NODE_INT:
    return x->ival == y->ival;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return node_eq(x->arg, y->arg);
  default:
    return node_eq(x->lhs, y->lhs) && node_eq(x->rhs, y->rhs);
  }
}

static uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

void tlsf_norm_options_default(TlsfNormOptions *opts, TlsfNormPhase phase) {
  *opts = (TlsfNormOptions){0};
  opts->phase = phase;
  opts->max_iter_default = 32;
  opts->max_growth_percent = 200;
  opts->max_nodes = 20000;
}

void tlsf_norm_stats_init(TlsfNormStats *s, TlsfNormPhase phase,
                          const char *schedule) {
  memset(s, 0, sizeof *s);
  s->phase = phase;
  s->schedule = schedule;
}

static void trace_row(const TlsfNormOptions *o, TlsfNormPass pass,
                      uint32_t iter, uint32_t nb, uint32_t na, bool changed,
                      TlsfNormRejectReason reason) {
  if (!o->trace)
    return;
  fprintf(o->trace, "%s\t%s\t%s\t%s\t%s\t%u\t%u\t%u\t%d\t%s\n",
          o->trace_file ? o->trace_file : "-", tlsf_norm_phase_name(o->phase),
          o->trace_constraint ? o->trace_constraint : "-",
          o->trace_role ? o->trace_role : "-", tlsf_norm_pass_name(pass), iter,
          nb, na, changed ? 1 : 0, tlsf_norm_reject_name(reason));
}

Node *tlsf_normalize_formula(Arena *a, Node *root, const TlsfNormOptions *opts,
                             TlsfNormStats *stats) {
  if (!root || opts->schedule.count == 0)
    return root;

  uint32_t n0 = ast_node_count(root);
  if (stats) {
    stats->formulas_seen++;
    if (n0 > stats->nodes_max_before)
      stats->nodes_max_before = n0;
    stats->nodes_before += n0;
  }

  Node *cur = root;
  bool any_changed = false, rejected = false;

  for (uint32_t i = 0; i < opts->schedule.count; i++) {
    TlsfNormPass pass = opts->schedule.items[i].pass;
    if (pass == TLSF_NORM_PASS_SPLIT || pass_is_pre(pass))
      continue; // list-level / pre-expansion: handled by the caller

    uint32_t iters = opts->schedule.items[i].max_iter;
    if (iters == 0)
      iters = 1;
    if (iters > opts->max_iter_default && opts->max_iter_default)
      iters = opts->max_iter_default;
    TlsfNormRule prim = pass_primary_rule(pass);

    for (uint32_t it = 0; it < iters; it++) {
      uint32_t nb = ast_node_count(cur);
      uint64_t t0 = now_ns();
      Node *cand = apply_pass_once(a, pass, cur);
      uint64_t dt = now_ns() - t0;
      if (!cand)
        cand = cur;
      uint32_t na = ast_node_count(cand);

      TlsfNormRejectReason rej = TLSF_NORM_REJECT_NONE;
      if (opts->max_nodes && na > opts->max_nodes)
        rej = TLSF_NORM_REJECT_NODES;
      else if (opts->max_growth_percent &&
               (uint64_t)na >
                   (uint64_t)n0 + (uint64_t)n0 * opts->max_growth_percent / 100)
        rej = TLSF_NORM_REJECT_GROWTH;

      if (rej != TLSF_NORM_REJECT_NONE) {
        if (stats && prim < TLSF_NORM_RULE_COUNT) {
          if (rej == TLSF_NORM_REJECT_NODES)
            stats->rules[prim].rejected_nodes++;
          else
            stats->rules[prim].rejected_growth++;
        }
        trace_row(opts, pass, it, nb, na, false, rej);
        rejected = true;
        break; // abandon this pass, keep last good `cur`
      }

      bool changed = !node_eq(cand, cur);
      if (stats && prim < TLSF_NORM_RULE_COUNT) {
        TlsfNormRuleStats *r = &stats->rules[prim];
        r->attempts++;
        r->time_ns += dt;
        r->nodes_before_sum += nb;
        r->nodes_after_sum += na;
        if (changed)
          r->fired++;
        else
          r->noops++;
        stats->iterations_total++;
      }
      trace_row(opts, pass, it, nb, na, changed, TLSF_NORM_REJECT_NONE);
      cur = cand;
      if (changed)
        any_changed = true;
      else
        break; // stable: stop iterating this pass
    }
  }

  if (stats) {
    uint32_t nf = ast_node_count(cur);
    stats->nodes_after += nf;
    if (nf > stats->nodes_max_after)
      stats->nodes_max_after = nf;
    if (any_changed)
      stats->formulas_changed++;
    if (rejected)
      stats->formulas_rejected++;
  }
  return cur;
}

// ---------------------------------------------------------------------------
// Stats output
// ---------------------------------------------------------------------------

void tlsf_norm_stats_print_human(FILE *out, const TlsfNormStats *s) {
  fprintf(out,
          "norm phase=%s schedule=%s formulas=%u changed=%u rejected=%u "
          "nodes=%llu->%llu iters=%u time=%.2fms\n",
          tlsf_norm_phase_name(s->phase), s->schedule ? s->schedule : "off",
          s->formulas_seen, s->formulas_changed, s->formulas_rejected,
          (unsigned long long)s->nodes_before,
          (unsigned long long)s->nodes_after, s->iterations_total,
          (double)s->time_ns / 1e6);
  for (TlsfNormRule r = 0; r < TLSF_NORM_RULE_COUNT; r++) {
    const TlsfNormRuleStats *rs = &s->rules[r];
    if (rs->attempts == 0 && rs->rejected_growth == 0 &&
        rs->rejected_nodes == 0)
      continue;
    fprintf(out,
            "  %s: fired=%llu noop=%llu rej_growth=%llu rej_nodes=%llu "
            "nodes=%llu->%llu\n",
            tlsf_norm_rule_name(r), (unsigned long long)rs->fired,
            (unsigned long long)rs->noops,
            (unsigned long long)rs->rejected_growth,
            (unsigned long long)rs->rejected_nodes,
            (unsigned long long)rs->nodes_before_sum,
            (unsigned long long)rs->nodes_after_sum);
  }
}

void tlsf_norm_stats_print_tsv_header(FILE *out) {
  fprintf(out, "phase\tschedule\tformulas_seen\tformulas_changed\t"
               "formulas_rejected\titerations_total\tnodes_before\t"
               "nodes_after\ttime_ns\trules_fired_total\trejected_growth");
  for (TlsfNormRule r = 0; r < TLSF_NORM_RULE_COUNT; r++)
    fprintf(out, "\t%s", tlsf_norm_rule_name(r));
  fprintf(out, "\n");
}

void tlsf_norm_stats_print_tsv_row(FILE *out, const TlsfNormStats *s) {
  uint64_t fired = 0, rej = 0;
  for (TlsfNormRule r = 0; r < TLSF_NORM_RULE_COUNT; r++) {
    fired += s->rules[r].fired;
    rej += s->rules[r].rejected_growth + s->rules[r].rejected_nodes;
  }
  fprintf(out, "%s\t%s\t%u\t%u\t%u\t%u\t%llu\t%llu\t%llu\t%llu\t%llu",
          tlsf_norm_phase_name(s->phase), s->schedule ? s->schedule : "off",
          s->formulas_seen, s->formulas_changed, s->formulas_rejected,
          s->iterations_total, (unsigned long long)s->nodes_before,
          (unsigned long long)s->nodes_after, (unsigned long long)s->time_ns,
          (unsigned long long)fired, (unsigned long long)rej);
  for (TlsfNormRule r = 0; r < TLSF_NORM_RULE_COUNT; r++)
    fprintf(out, "\t%llu", (unsigned long long)s->rules[r].fired);
  fprintf(out, "\n");
}
