#include "tlsf/expand.h"

#include <assert.h>
#include <stdio.h>
#include <string.h>

// Guard against non-terminating (mis-written) recursive definitions.
// Bounds definition/expression recursion. Kept well below the depth at which a
// runaway self-reference would overflow the C stack, while far exceeding any
// nesting a real specification needs.
#define MAX_DEPTH 2000

// ===========================================================================
// Integer-evaluation environment
//
// A scope chain mapping interned variable names (parameters and bounded-
// quantifier variables) to concrete integer values.  Definition formals are
// handled by substitution, not by this environment.
// ===========================================================================

typedef struct Binding {
  const char *name;
  int64_t value;
} Binding;

typedef struct Env {
  Binding b;
  const struct Env *parent;
} Env;

static bool env_lookup(const Env *env, const char *name, int64_t *out) {
  for (const Env *e = env; e; e = e->parent)
    if (e->b.name == name) {
      *out = e->b.value;
      return true;
    }
  return false;
}

// ===========================================================================
// Definition lookup
// ===========================================================================

static const DefDecl *find_def(const TlsfSpec *spec, const char *name,
                               uint16_t argc) {
  for (uint16_t i = 0; i < spec->def_count; i++)
    if (spec->defs[i].name == name && spec->defs[i].param_count == argc)
      return &spec->defs[i];
  return nullptr;
}

// ===========================================================================
// Substitution: deep-copy a definition body, replacing each formal name with
// the corresponding actual argument node.
// ===========================================================================

// If `name` is a formal bound to a plain-identifier actual, return that
// identifier; otherwise return `name` unchanged.
static const char *subst_name(const char *name, const char *const *formals,
                              Node *const *actuals, uint16_t nf) {
  for (uint16_t k = 0; k < nf; k++)
    if (formals[k] == name)
      return actuals[k]->kind == NODE_AP ? actuals[k]->name : name;
  return name;
}

static Node *subst(Arena *a, const Node *n, const char *const *formals,
                   Node *const *actuals, uint16_t nf) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
    return (Node *)n;

  case NODE_AP:
  case NODE_INT_VAR:
    for (uint16_t k = 0; k < nf; k++)
      if (formals[k] == n->name)
        return actuals[k];
    return (Node *)n;

  case NODE_SIZEOF: {
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = NODE_SIZEOF;
    m->sizeof_name = subst_name(n->sizeof_name, formals, actuals, nf);
    return m;
  }
  case NODE_BUS_INDEX: {
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = NODE_BUS_INDEX;
    m->bus_name = subst_name(n->bus_name, formals, actuals, nf);
    m->bus_index = subst(a, n->bus_index, formals, actuals, nf);
    return m;
  }
  case NODE_DEF_CALL:
  case NODE_PATTERN: {
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = n->kind;
    m->callee = n->callee;
    m->call_argc = n->call_argc;
    m->call_args = ARENA_ALLOC_N(a, Node *, n->call_argc);
    for (uint16_t i = 0; i < n->call_argc; i++)
      m->call_args[i] = subst(a, n->call_args[i], formals, actuals, nf);
    return m;
  }
  case NODE_ITE: {
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = NODE_ITE;
    m->if_cond = subst(a, n->if_cond, formals, actuals, nf);
    m->if_then = subst(a, n->if_then, formals, actuals, nf);
    m->if_else = subst(a, n->if_else, formals, actuals, nf);
    return m;
  }
  case NODE_FORALL:
  case NODE_EXISTS: {
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = n->kind;
    m->qvar = n->qvar;
    m->qlo = subst(a, n->qlo, formals, actuals, nf);
    m->qhi = subst(a, n->qhi, formals, actuals, nf);
    m->qbody = subst(a, n->qbody, formals, actuals, nf);
    m->qlo_strict = n->qlo_strict;
    m->qhi_strict = n->qhi_strict;
    return m;
  }
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG: {
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = n->kind;
    m->arg = subst(a, n->arg, formals, actuals, nf);
    return m;
  }
  default: { // all binary nodes (boolean / temporal / arithmetic / compare)
    Node *m = ARENA_ALLOC(a, Node);
    m->kind = n->kind;
    m->lhs = subst(a, n->lhs, formals, actuals, nf);
    m->rhs = subst(a, n->rhs, formals, actuals, nf);
    return m;
  }
  }
}

// ===========================================================================
// Bus-width lookup (for SIZEOF)
// ===========================================================================

static bool bus_width(const TlsfSpec *spec, const char *name, int64_t *out) {
  const SignalDecl *lists[2] = {spec->inputs, spec->outputs};
  uint32_t counts[2] = {spec->input_count, spec->output_count};
  for (int k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++)
      if (lists[k][i].name == name) {
        *out = lists[k][i].is_bus
                   ? (int64_t)lists[k][i].bus_hi - lists[k][i].bus_lo + 1
                   : 1;
        return true;
      }
  return false;
}

// ===========================================================================
// Integer / boolean evaluation
// ===========================================================================

static bool eval_int(const TlsfSpec *spec, const Node *n, const Env *env,
                     int64_t *out, int depth);
static bool eval_bool(const TlsfSpec *spec, const Node *n, const Env *env,
                      bool *out, int depth);

static bool eval_int(const TlsfSpec *spec, const Node *n, const Env *env,
                     int64_t *out, int depth) {
  if (depth > MAX_DEPTH) {
    fprintf(stderr, "expand: recursion too deep\n");
    return false;
  }
  switch (n->kind) {
  case NODE_INT:
    *out = n->ival;
    return true;
  case NODE_INT_VAR:
  case NODE_AP:
    if (env_lookup(env, n->name, out))
      return true;
    { // a nullary definition used in numeric position
      const DefDecl *d = find_def(spec, n->name, 0);
      if (d)
        return eval_int(spec, d->body, env, out, depth + 1);
    }
    fprintf(stderr, "expand: undefined parameter/variable '%s'\n", n->name);
    return false;
  case NODE_SIZEOF:
    if (!bus_width(spec, n->sizeof_name, out)) {
      fprintf(stderr, "expand: SIZEOF of unknown signal '%s'\n",
              n->sizeof_name);
      return false;
    }
    return true;
  case NODE_INT_NEG: {
    int64_t a;
    if (!eval_int(spec, n->arg, env, &a, depth))
      return false;
    *out = -a;
    return true;
  }
  case NODE_DEF_CALL: {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(stderr, "expand: no definition '%s'/%u\n", n->callee,
              n->call_argc);
      return false;
    }
    Node *body =
        subst(spec->arena, d->body, d->params, n->call_args, d->param_count);
    return eval_int(spec, body, env, out, depth + 1);
  }
  case NODE_ITE: {
    bool c;
    if (!eval_bool(spec, n->if_cond, env, &c, depth))
      return false;
    return eval_int(spec, c ? n->if_then : n->if_else, env, out, depth);
  }
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD: {
    int64_t a, b;
    if (!eval_int(spec, n->lhs, env, &a, depth) ||
        !eval_int(spec, n->rhs, env, &b, depth))
      return false;
    if ((n->kind == NODE_INT_DIV || n->kind == NODE_INT_MOD) && b == 0) {
      fprintf(stderr, "expand: division by zero\n");
      return false;
    }
    switch (n->kind) {
    case NODE_INT_ADD:
      *out = a + b;
      break;
    case NODE_INT_SUB:
      *out = a - b;
      break;
    case NODE_INT_MUL:
      *out = a * b;
      break;
    case NODE_INT_DIV:
      *out = a / b;
      break;
    default:
      *out = a % b;
      break;
    }
    return true;
  }
  default:
    fprintf(stderr, "expand: non-integer expression in numeric context\n");
    return false;
  }
}

static bool eval_bool(const TlsfSpec *spec, const Node *n, const Env *env,
                      bool *out, int depth) {
  if (depth > MAX_DEPTH) {
    fprintf(stderr, "expand: recursion too deep\n");
    return false;
  }
  switch (n->kind) {
  case NODE_TRUE:
    *out = true;
    return true;
  case NODE_FALSE:
    *out = false;
    return true;
  case NODE_CMP_EQ:
  case NODE_CMP_NE:
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE: {
    int64_t a, b;
    if (!eval_int(spec, n->lhs, env, &a, depth) ||
        !eval_int(spec, n->rhs, env, &b, depth))
      return false;
    switch (n->kind) {
    case NODE_CMP_EQ:
      *out = a == b;
      break;
    case NODE_CMP_NE:
      *out = a != b;
      break;
    case NODE_CMP_LT:
      *out = a < b;
      break;
    case NODE_CMP_LE:
      *out = a <= b;
      break;
    case NODE_CMP_GT:
      *out = a > b;
      break;
    default:
      *out = a >= b;
      break;
    }
    return true;
  }
  case NODE_NOT: {
    bool x;
    if (!eval_bool(spec, n->arg, env, &x, depth))
      return false;
    *out = !x;
    return true;
  }
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    bool a, b;
    if (!eval_bool(spec, n->lhs, env, &a, depth) ||
        !eval_bool(spec, n->rhs, env, &b, depth))
      return false;
    switch (n->kind) {
    case NODE_AND:
      *out = a && b;
      break;
    case NODE_OR:
      *out = a || b;
      break;
    case NODE_IMPL:
      *out = !a || b;
      break;
    default:
      *out = a == b;
      break;
    }
    return true;
  }
  case NODE_ITE: {
    bool c;
    if (!eval_bool(spec, n->if_cond, env, &c, depth))
      return false;
    return eval_bool(spec, c ? n->if_then : n->if_else, env, out, depth);
  }
  case NODE_DEF_CALL: {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(stderr, "expand: no definition '%s'/%u\n", n->callee,
              n->call_argc);
      return false;
    }
    Node *body =
        subst(spec->arena, d->body, d->params, n->call_args, d->param_count);
    return eval_bool(spec, body, env, out, depth + 1);
  }
  default:
    fprintf(stderr, "expand: non-boolean expression in a guard\n");
    return false;
  }
}

// ===========================================================================
// Formula expansion
// ===========================================================================

static Node *expand_node(TlsfSpec *spec, const Node *n, const Env *env,
                         bool *ok, int depth);

static const char *bus_elem_name(TlsfSpec *spec, const char *bus, int64_t idx) {
  char buf[256];
  snprintf(buf, sizeof buf, "%s_%lld", bus, (long long)idx);
  return intern(spec->intern, buf);
}

static Node *expand_quantifier(TlsfSpec *spec, const Node *n, const Env *env,
                               bool *ok, int depth) {
  int64_t lo, hi;
  if (!eval_int(spec, n->qlo, env, &lo, depth) ||
      !eval_int(spec, n->qhi, env, &hi, depth)) {
    *ok = false;
    return nullptr;
  }
  int64_t start = n->qlo_strict ? lo + 1 : lo;
  int64_t end = n->qhi_strict ? hi - 1 : hi;
  bool is_all = (n->kind == NODE_FORALL);

  if (start > end)
    return is_all ? node_true(spec->arena) : node_false(spec->arena);

  Node *acc = nullptr;
  for (int64_t v = start; v <= end; v++) {
    Env child = {.b = {.name = n->qvar, .value = v}, .parent = env};
    Node *term = expand_node(spec, n->qbody, &child, ok, depth);
    if (!*ok)
      return nullptr;
    acc = !acc ? term
               : (is_all ? node_and(spec->arena, acc, term)
                         : node_or(spec->arena, acc, term));
  }
  return acc;
}

static Node *expand_node(TlsfSpec *spec, const Node *n, const Env *env,
                         bool *ok, int depth) {
  if (!*ok || !n)
    return nullptr;
  Arena *a = spec->arena;
  if (depth > MAX_DEPTH) {
    fprintf(stderr, "expand: recursion too deep\n");
    *ok = false;
    return nullptr;
  }

#define XUNARY(ctor)                                                           \
  do {                                                                         \
    Node *x = expand_node(spec, n->arg, env, ok, depth);                       \
    if (!*ok)                                                                  \
      return nullptr;                                                          \
    return ctor(a, x);                                                         \
  } while (0)
#define XBINARY(ctor)                                                          \
  do {                                                                         \
    Node *l = expand_node(spec, n->lhs, env, ok, depth);                       \
    Node *r = expand_node(spec, n->rhs, env, ok, depth);                       \
    if (!*ok)                                                                  \
      return nullptr;                                                          \
    return ctor(a, l, r);                                                      \
  } while (0)

  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return (Node *)n;

  // A bare identifier: a nullary definition (inline it) or a signal.
  case NODE_AP: {
    const DefDecl *d = find_def(spec, n->name, 0);
    if (d)
      return expand_node(spec, d->body, env, ok, depth + 1);
    return (Node *)n;
  }

  case NODE_NOT:
    XUNARY(node_not);
  case NODE_AND:
    XBINARY(node_and);
  case NODE_OR:
    XBINARY(node_or);
  case NODE_IMPL:
    XBINARY(node_impl);
  case NODE_EQUIV:
    XBINARY(node_equiv);

  case NODE_X:
    XUNARY(node_x);
  case NODE_X_STRONG:
    XUNARY(node_x_strong);
  case NODE_F:
    XUNARY(node_f);
  case NODE_G:
    XUNARY(node_g);
  case NODE_U:
    XBINARY(node_u);
  case NODE_R:
    XBINARY(node_r);
  case NODE_W:
    XBINARY(node_w);
  case NODE_M:
    XBINARY(node_m);

  case NODE_BUS_INDEX: {
    int64_t idx;
    if (!eval_int(spec, n->bus_index, env, &idx, depth)) {
      *ok = false;
      return nullptr;
    }
    return node_ap(a, bus_elem_name(spec, n->bus_name, idx));
  }

  case NODE_FORALL:
  case NODE_EXISTS:
    return expand_quantifier(spec, n, env, ok, depth);

  case NODE_NEXT_N: {
    // X[count] body  ==  count-fold application of X to the expanded body.
    int64_t count;
    if (!eval_int(spec, n->lhs, env, &count, depth)) {
      *ok = false;
      return nullptr;
    }
    if (count < 0) {
      fprintf(stderr, "expand: negative count in X[...]\n");
      *ok = false;
      return nullptr;
    }
    Node *body = expand_node(spec, n->rhs, env, ok, depth);
    if (!*ok)
      return nullptr;
    for (int64_t i = 0; i < count; i++)
      body = node_x(a, body);
    return body;
  }

  // Definition guard: evaluate the condition, expand the chosen branch.
  case NODE_ITE: {
    bool c;
    if (!eval_bool(spec, n->if_cond, env, &c, depth)) {
      *ok = false;
      return nullptr;
    }
    return expand_node(spec, c ? n->if_then : n->if_else, env, ok, depth);
  }

  // Definition call: substitute the actuals into the body and expand.
  case NODE_DEF_CALL: {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(stderr, "expand: no definition '%s'/%u\n", n->callee,
              n->call_argc);
      *ok = false;
      return nullptr;
    }
    Node *body = subst(a, d->body, d->params, n->call_args, d->param_count);
    return expand_node(spec, body, env, ok, depth + 1);
  }

  case NODE_PATTERN:
    fprintf(stderr, "expand: pattern '%s' not supported\n", n->callee);
    *ok = false;
    return nullptr;

  default:
    fprintf(stderr, "expand: unexpected node kind %d in formula\n", n->kind);
    *ok = false;
    return nullptr;
  }
#undef XUNARY
#undef XBINARY
}

// ===========================================================================
// Parameter environment and signal explosion
// ===========================================================================

static Env *build_param_env(TlsfSpec *spec) {
  Env *head = nullptr;
  for (uint16_t i = 0; i < spec->param_count; i++) {
    Env *e = ARENA_ALLOC(spec->arena, Env);
    e->b.name = spec->params[i].name;
    e->b.value = spec->params[i].value;
    e->parent = head;
    head = e;
  }
  return head;
}

static int explode_signals(TlsfSpec *spec, bool is_output) {
  SignalDecl *old = is_output ? spec->outputs : spec->inputs;
  uint32_t n = is_output ? spec->output_count : spec->input_count;

  if (is_output) {
    spec->outputs = nullptr;
    spec->output_count = 0;
    spec->output_cap = 0;
  } else {
    spec->inputs = nullptr;
    spec->input_count = 0;
    spec->input_cap = 0;
  }

  for (uint32_t i = 0; i < n; i++) {
    const SignalDecl *s = &old[i];
    if (!s->is_bus) {
      if (!spec_add_signal(spec, is_output, s->name, false, nullptr, nullptr))
        return -1;
      continue;
    }
    for (int64_t v = s->bus_lo; v <= (int64_t)s->bus_hi; v++)
      if (!spec_add_signal(spec, is_output, bus_elem_name(spec, s->name, v),
                           false, nullptr, nullptr))
        return -1;
  }
  return 0;
}

// ===========================================================================
// Public entry point
// ===========================================================================

int expand(TlsfSpec *spec, const ParamOverride *overrides, size_t n_overrides) {
  assert(spec);

  // --- Phase 1: resolve parameter values (apply overrides over defaults). ---
  for (size_t i = 0; i < n_overrides; i++) {
    const char *iname = intern(spec->intern, overrides[i].name);
    bool found = false;
    for (uint16_t j = 0; j < spec->param_count; j++)
      if (spec->params[j].name == iname) {
        spec->params[j].value = overrides[i].value;
        spec->params[j].has_default = true;
        found = true;
        break;
      }
    if (!found) {
      fprintf(stderr, "expand: unknown parameter '%s'\n", overrides[i].name);
      return -1;
    }
  }
  for (uint16_t i = 0; i < spec->param_count; i++)
    if (!spec->params[i].has_default) {
      fprintf(stderr, "expand: parameter '%s' has no value (use --param)\n",
              spec->params[i].name);
      return -1;
    }

  Env *env = build_param_env(spec);

  // --- Phase 2: resolve bus declaration bounds. ---
  SignalDecl *sig_lists[2] = {spec->inputs, spec->outputs};
  uint32_t sig_counts[2] = {spec->input_count, spec->output_count};
  for (int k = 0; k < 2; k++)
    for (uint32_t i = 0; i < sig_counts[k]; i++) {
      SignalDecl *s = &sig_lists[k][i];
      if (!s->is_bus)
        continue;
      int64_t lo = s->bus_lo, hi = s->bus_hi;
      if (s->bus_lo_expr && !eval_int(spec, s->bus_lo_expr, env, &lo, 0))
        return -1;
      if (s->bus_hi_expr && !eval_int(spec, s->bus_hi_expr, env, &hi, 0))
        return -1;
      s->bus_lo = (uint16_t)lo;
      s->bus_hi = (uint16_t)hi;
    }

  // --- Phase 3: expand every formula. ---
  bool ok = true;
#define EXPAND_LIST(list)                                                      \
  do {                                                                         \
    for (uint32_t _i = 0; _i < (list).count; _i++) {                           \
      (list).formulas[_i] =                                                    \
          expand_node(spec, (list).formulas[_i], env, &ok, 0);                 \
      if (!ok)                                                                 \
        return -1;                                                             \
    }                                                                          \
  } while (0)

  EXPAND_LIST(spec->initially);
  EXPAND_LIST(spec->require);
  EXPAND_LIST(spec->assume);
  EXPAND_LIST(spec->preset);
  EXPAND_LIST(spec->assert_);
  EXPAND_LIST(spec->guarantee);
#undef EXPAND_LIST

  // Explode bus declarations into scalar signals (basic fragment).
  if (explode_signals(spec, false) != 0 || explode_signals(spec, true) != 0)
    return -1;

  // Clear the GLOBAL section — it has been expanded away.
  spec->params = nullptr;
  spec->param_count = 0;
  spec->defs = nullptr;
  spec->def_count = 0;
  return 0;
}
