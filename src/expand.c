#include "tlsf/expand.h"

#include <assert.h>
#include <stdio.h>
#include <string.h>

// ===========================================================================
// Integer-evaluation environment
//
// A scope chain mapping interned variable names (parameters and bounded-
// quantifier variables) to concrete integer values.  Names are interned, so
// lookups use pointer equality.
// ===========================================================================

typedef struct Binding {
  const char *name;
  int64_t value;
} Binding;

typedef struct Env {
  Binding b;          // single binding introduced at this level
  const struct Env *parent;
} Env;

static bool env_lookup(const Env *env, const char *name, int64_t *out) {
  for (const Env *e = env; e; e = e->parent) {
    if (e->b.name == name) {
      *out = e->b.value;
      return true;
    }
  }
  return false;
}

// ===========================================================================
// Bus-width lookup (for SIZEOF)
// ===========================================================================

static bool bus_width(const TlsfSpec *spec, const char *name, int64_t *out) {
  const SignalDecl *lists[2] = {spec->inputs, spec->outputs};
  uint32_t counts[2] = {spec->input_count, spec->output_count};
  for (int k = 0; k < 2; k++) {
    for (uint32_t i = 0; i < counts[k]; i++) {
      const SignalDecl *s = &lists[k][i];
      if (s->name == name) {
        if (!s->is_bus) {
          *out = 1;
        } else {
          *out = (int64_t)s->bus_hi - (int64_t)s->bus_lo + 1;
        }
        return true;
      }
    }
  }
  return false;
}

// ===========================================================================
// Integer expression evaluation
// ===========================================================================

static bool eval_int(const TlsfSpec *spec, const Node *n, const Env *env,
                     int64_t *out) {
  switch (n->kind) {
  case NODE_INT:
    *out = n->ival;
    return true;
  case NODE_INT_VAR:
  case NODE_AP: // a bare identifier used in numeric position is a variable
    if (!env_lookup(env, n->name, out)) {
      fprintf(stderr, "expand: undefined parameter/variable '%s'\n", n->name);
      return false;
    }
    return true;
  case NODE_SIZEOF:
    if (!bus_width(spec, n->sizeof_name, out)) {
      fprintf(stderr, "expand: SIZEOF of unknown signal '%s'\n",
              n->sizeof_name);
      return false;
    }
    return true;
  case NODE_INT_NEG: {
    int64_t a;
    if (!eval_int(spec, n->arg, env, &a))
      return false;
    *out = -a;
    return true;
  }
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD: {
    int64_t a, b;
    if (!eval_int(spec, n->lhs, env, &a) || !eval_int(spec, n->rhs, env, &b))
      return false;
    if ((n->kind == NODE_INT_DIV || n->kind == NODE_INT_MOD) && b == 0) {
      fprintf(stderr, "expand: division by zero\n");
      return false;
    }
    switch (n->kind) {
    case NODE_INT_ADD: *out = a + b; break;
    case NODE_INT_SUB: *out = a - b; break;
    case NODE_INT_MUL: *out = a * b; break;
    case NODE_INT_DIV: *out = a / b; break;
    default:           *out = a % b; break;
    }
    return true;
  }
  default:
    fprintf(stderr, "expand: non-integer expression in numeric context\n");
    return false;
  }
}

// ===========================================================================
// Formula expansion: a deep copy that resolves parameters, SIZEOF, bus
// indices, and bounded quantifiers under the current environment.
//
// The copy must be fresh because a quantifier body is expanded once per value
// of the bound variable; mutating in place would alias the shared subtree.
// ===========================================================================

static Node *expand_node(TlsfSpec *spec, const Node *n, const Env *env,
                         bool *ok);

// Build the interned name for bus element `bus[idx]` (syfco default: bus_idx).
static const char *bus_elem_name(TlsfSpec *spec, const char *bus, int64_t idx) {
  char buf[256];
  snprintf(buf, sizeof buf, "%s_%lld", bus, (long long)idx);
  return intern(spec->intern, buf);
}

// Expand a bounded quantifier into an AND/OR chain over its range.
static Node *expand_quantifier(TlsfSpec *spec, const Node *n, const Env *env,
                               bool *ok) {
  int64_t lo, hi;
  if (!eval_int(spec, n->qlo, env, &lo) || !eval_int(spec, n->qhi, env, &hi)) {
    *ok = false;
    return nullptr;
  }
  int64_t start = n->qlo_strict ? lo + 1 : lo;
  int64_t end = n->qhi_strict ? hi - 1 : hi;

  bool is_all = (n->kind == NODE_FORALL);

  // Empty range: conjunction is true, disjunction is false.
  if (start > end)
    return is_all ? node_true(spec->arena) : node_false(spec->arena);

  Node *acc = nullptr;
  for (int64_t v = start; v <= end; v++) {
    Env child = {.b = {.name = n->qvar, .value = v}, .parent = env};
    Node *term = expand_node(spec, n->qbody, &child, ok);
    if (!*ok)
      return nullptr;
    if (!acc)
      acc = term;
    else
      acc = is_all ? node_and(spec->arena, acc, term)
                   : node_or(spec->arena, acc, term);
  }
  return acc;
}

static Node *expand_node(TlsfSpec *spec, const Node *n, const Env *env,
                         bool *ok) {
  if (!*ok || !n)
    return nullptr;
  Arena *a = spec->arena;

// Expand a single child, then bail (returning nullptr) if expansion failed,
// so node constructors are never called with a null operand.
#define XUNARY(ctor)                                                           \
  do {                                                                         \
    Node *x = expand_node(spec, n->arg, env, ok);                              \
    if (!*ok)                                                                  \
      return nullptr;                                                          \
    return ctor(a, x);                                                         \
  } while (0)
#define XBINARY(ctor)                                                          \
  do {                                                                         \
    Node *l = expand_node(spec, n->lhs, env, ok);                              \
    Node *r = expand_node(spec, n->rhs, env, ok);                              \
    if (!*ok)                                                                  \
      return nullptr;                                                          \
    return ctor(a, l, r);                                                      \
  } while (0)

  switch (n->kind) {
  // Atoms: immutable, safe to share.
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return (Node *)n;

  // Boolean connectives.
  case NODE_NOT:   XUNARY(node_not);
  case NODE_AND:   XBINARY(node_and);
  case NODE_OR:    XBINARY(node_or);
  case NODE_IMPL:  XBINARY(node_impl);
  case NODE_EQUIV: XBINARY(node_equiv);

  // Temporal operators.
  case NODE_X:        XUNARY(node_x);
  case NODE_X_STRONG: XUNARY(node_x_strong);
  case NODE_F:        XUNARY(node_f);
  case NODE_G:        XUNARY(node_g);
  case NODE_U: XBINARY(node_u);
  case NODE_R: XBINARY(node_r);
  case NODE_W: XBINARY(node_w);
  case NODE_M: XBINARY(node_m);

  // Bus index: evaluate the index, produce the scalar AP.
  case NODE_BUS_INDEX: {
    int64_t idx;
    if (!eval_int(spec, n->bus_index, env, &idx)) {
      *ok = false;
      return nullptr;
    }
    return node_ap(a, bus_elem_name(spec, n->bus_name, idx));
  }

  // Bounded quantifiers.
  case NODE_FORALL:
  case NODE_EXISTS:
    return expand_quantifier(spec, n, env, ok);

  // Definitions / patterns are not yet expanded.
  case NODE_DEF_CALL:
    fprintf(stderr, "expand: definition '%s' not yet supported\n", n->callee);
    *ok = false;
    return nullptr;
  case NODE_PATTERN:
    fprintf(stderr, "expand: pattern '%s' not yet supported\n", n->callee);
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
// Parameter environment construction
// ===========================================================================

// Build a flat chained environment of all parameter bindings.  The Env nodes
// are arena-allocated and chained; returns the head (or nullptr if no params).
static Env *build_param_env(TlsfSpec *spec) {
  Env *head = nullptr;
  for (uint16_t i = 0; i < spec->param_count; i++) {
    Env *e = ARENA_ALLOC(spec->arena, Env);
    e->b.name = spec->params[i].name;
    e->b.value = spec->params[i].value; // value already holds default/override
    e->parent = head;
    head = e;
  }
  return head;
}

// Replace bus declarations with their scalar elements (bus_i), so the
// expanded spec is in the basic fragment (no buses) and its signal lists
// match the scalar APs now used in the formulas.
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
    for (int64_t v = s->bus_lo; v <= (int64_t)s->bus_hi; v++) {
      const char *nm = bus_elem_name(spec, s->name, v);
      if (!spec_add_signal(spec, is_output, nm, false, nullptr, nullptr))
        return -1;
    }
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
    for (uint16_t j = 0; j < spec->param_count; j++) {
      if (spec->params[j].name == iname) {
        spec->params[j].value = overrides[i].value;
        spec->params[j].has_default = true;
        found = true;
        break;
      }
    }
    if (!found) {
      fprintf(stderr, "expand: unknown parameter '%s'\n", overrides[i].name);
      return -1;
    }
  }
  for (uint16_t i = 0; i < spec->param_count; i++) {
    if (!spec->params[i].has_default) {
      fprintf(stderr, "expand: parameter '%s' has no value (use --param)\n",
              spec->params[i].name);
      return -1;
    }
  }

  Env *env = build_param_env(spec);

  // --- Phase 2: resolve bus declaration bounds (so SIZEOF and the expanded
  //     INPUTS/OUTPUTS lists are correct). ---
  SignalDecl *sig_lists[2] = {spec->inputs, spec->outputs};
  uint32_t sig_counts[2] = {spec->input_count, spec->output_count};
  for (int k = 0; k < 2; k++) {
    for (uint32_t i = 0; i < sig_counts[k]; i++) {
      SignalDecl *s = &sig_lists[k][i];
      if (!s->is_bus)
        continue;
      int64_t lo = s->bus_lo, hi = s->bus_hi;
      if (s->bus_lo_expr && !eval_int(spec, s->bus_lo_expr, env, &lo))
        return -1;
      if (s->bus_hi_expr && !eval_int(spec, s->bus_hi_expr, env, &hi))
        return -1;
      s->bus_lo = (uint16_t)lo;
      s->bus_hi = (uint16_t)hi;
    }
  }

  // --- Phase 3: expand every formula (params, SIZEOF, bus indices, bounded
  //     quantifiers). ---
  bool ok = true;
#define EXPAND_LIST(list)                                                      \
  do {                                                                         \
    for (uint32_t _i = 0; _i < (list).count; _i++) {                           \
      (list).formulas[_i] = expand_node(spec, (list).formulas[_i], env, &ok);  \
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
