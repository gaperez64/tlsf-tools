#include "tlsf/expand.h"

#include <assert.h>
#include <stdio.h>
#include "diagnostic.h"
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

typedef struct SubstCopy {
  const Node *source;
  Node node;
  struct SubstCopy *next;
} SubstCopy;

typedef struct Env {
  Binding b;
  const struct Env *parent;
  uint32_t binder_id;
  SubstCopy **copies;
} Env;

static const Node *subst_source(const Node *n, const Env *env) {
  if (n && !n->source_id)
    for (SubstCopy *copy = *env->copies; copy; copy = copy->next)
      if (copy->source == n)
        return &copy->node;
  return n;
}

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
                   Node *const *actuals, uint16_t nf, const Env *env) {
  n = subst_source(n, env);
  if (!n || arena_failed(a))
    return nullptr;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
    return (Node *)n;

  case NODE_AP:
  case NODE_INT_VAR:
    for (uint16_t k = 0; k < nf; k++)
      if (formals[k] == n->name) {
        Node *actual = (Node *)subst_source(actuals[k], env);
        if (actual == n || actual->source_id || !n->source_id)
          return actual;
        // Keep the old first-use fallback, but annotate a private copy.
        // Reuse it across substitutions so shared unnumbered actuals keep
        // the same ID without changing any caller-owned node.
        SubstCopy *copy = ARENA_ALLOC(a, SubstCopy);
        if (!copy)
          return nullptr;
        *copy = (SubstCopy){
            .source = actual, .node = *actual, .next = *env->copies};
        copy->node.source_id = n->source_id;
        *env->copies = copy;
        return &copy->node;
      }
    return (Node *)n;

  default:
    break;
  }

  Node *m = ARENA_ALLOC(a, Node);
  if (!m)
    return nullptr;
  m->kind = n->kind;
#define SUBST(field)                                                           \
  do {                                                                         \
    if (!(m->field = subst(a, n->field, formals, actuals, nf, env)))           \
      return nullptr;                                                          \
  } while (0)

  switch (n->kind) {
  case NODE_SIZEOF: {
    m->sizeof_name = subst_name(n->sizeof_name, formals, actuals, nf);
    break;
  }
  case NODE_BUS_INDEX: {
    m->bus_name = subst_name(n->bus_name, formals, actuals, nf);
    SUBST(bus_index);
    break;
  }
  case NODE_DEF_CALL:
  case NODE_PATTERN: {
    m->callee = n->callee;
    m->call_argc = n->call_argc;
    m->call_args = ARENA_ALLOC_N(a, Node *, n->call_argc);
    if (!m->call_args)
      return nullptr;
    for (uint16_t i = 0; i < n->call_argc; i++)
      SUBST(call_args[i]);
    break;
  }
  case NODE_ITE: {
    SUBST(if_cond);
    SUBST(if_then);
    SUBST(if_else);
    break;
  }
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER: {
    m->qvar = n->qvar;
    if (n->qlo)
      SUBST(qlo);
    if (n->qhi)
      SUBST(qhi);
    if (n->qset)
      SUBST(qset);
    SUBST(qbody);
    m->qlo_strict = n->qlo_strict;
    m->qhi_strict = n->qhi_strict;
    break;
  }
  case NODE_G_RANGE:
  case NODE_F_RANGE: {
    // Bounded temporal: only the bounds and body are used (no qvar/strict).
    SUBST(qlo);
    SUBST(qhi);
    SUBST(qbody);
    m->bounded.strong = n->bounded.strong;
    break;
  }
  case NODE_SET:
  case NODE_SET_ENUM: {
    m->set_size = n->set_size;
    m->set_elems = ARENA_ALLOC_N(a, Node *, n->set_size);
    if (!m->set_elems)
      return nullptr;
    for (uint16_t i = 0; i < n->set_size; i++)
      SUBST(set_elems[i]);
    break;
  }
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX: {
    SUBST(arg);
    break;
  }
  case NODE_NEXT_N: {
    SUBST(lhs);
    SUBST(rhs);
    m->bounded.strong = n->bounded.strong;
    break;
  }
  default: { // all binary nodes (boolean / temporal / arithmetic / compare)
    SUBST(lhs);
    SUBST(rhs);
    break;
  }
  }
#undef SUBST
  // Recursion may introduce a fallback for a shared source node.
  // Only annotate the fresh copy after resolving that fallback.
  m->source_id = subst_source(n, env)->source_id;
  return m;
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
static Node *expand_node(TlsfSpec *spec, const Node *n, const Env *env,
                         bool *ok, int depth);
static Node *expand_node_impl(TlsfSpec *spec, const Node *n, const Env *env,
                              bool *ok, int depth);
static bool select_ite_branch(const TlsfSpec *spec, const Node *n,
                              const Env *env, Node **out, int depth);

typedef enum EvalValueKind {
  EVAL_VALUE_INT,
  EVAL_VALUE_NODE,
  EVAL_VALUE_SET,
} EvalValueKind;

typedef struct EvalSet EvalSet;

typedef struct EvalValue {
  EvalValueKind kind;
  int64_t integer;
  const Node *node;
  EvalSet *set;
  const Node *source;
} EvalValue;

struct EvalSet {
  EvalValue *items;
  uint32_t count;
};

static bool eval_value(const TlsfSpec *spec, const Node *n, const Env *env,
                       EvalValue *out, int depth);
static bool eval_set(const TlsfSpec *spec, const Node *n, const Env *env,
                     EvalSet **out, int depth);
static bool eval_int_reduction(const TlsfSpec *spec, const Node *n,
                               const Env *env, int64_t *out, int depth);
static bool eval_set_reduction(const TlsfSpec *spec, const Node *n,
                               const Env *env, EvalSet **out, int depth);
static bool value_equal(const EvalValue *lhs, const EvalValue *rhs);

static bool eval_int(const TlsfSpec *spec, const Node *n, const Env *env,
                     int64_t *out, int depth) {
  if (depth > MAX_DEPTH) {
    fprintf(tlsf_diagnostic_stream(), "expand: recursion too deep\n");
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
    fprintf(tlsf_diagnostic_stream(),
            "expand: undefined parameter/variable '%s'\n", n->name);
    return false;
  case NODE_SIZEOF:
    if (!bus_width(spec, n->sizeof_name, out)) {
      fprintf(tlsf_diagnostic_stream(),
              "expand: SIZEOF of unknown signal '%s'\n", n->sizeof_name);
      return false;
    }
    return true;
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX: {
    EvalSet *set;
    if (!eval_set(spec, n->arg, env, &set, depth + 1))
      return false;
    if (n->kind == NODE_SET_SIZE) {
      *out = (int64_t)set->count;
      return true;
    }
    if (set->count == 0) {
      fprintf(tlsf_diagnostic_stream(), "expand: %s of an empty set\n",
              n->kind == NODE_SET_MIN ? "MIN" : "MAX");
      return false;
    }
    int64_t value;
    if (set->items[0].kind != EVAL_VALUE_INT) {
      fprintf(tlsf_diagnostic_stream(),
              "expand: %s requires a set of integers\n",
              n->kind == NODE_SET_MIN ? "MIN" : "MAX");
      return false;
    }
    value = set->items[0].integer;
    for (uint32_t i = 1; i < set->count; i++) {
      if (set->items[i].kind != EVAL_VALUE_INT) {
        fprintf(tlsf_diagnostic_stream(),
                "expand: %s requires a set of integers\n",
                n->kind == NODE_SET_MIN ? "MIN" : "MAX");
        return false;
      }
      int64_t x = set->items[i].integer;
      if ((n->kind == NODE_SET_MIN && x < value) ||
          (n->kind == NODE_SET_MAX && x > value))
        value = x;
    }
    *out = value;
    return true;
  }
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
      fprintf(tlsf_diagnostic_stream(), "expand: no definition '%s'/%u\n",
              n->callee, n->call_argc);
      return false;
    }
    Node *body = subst(spec->arena, d->body, d->params, n->call_args,
                       d->param_count, env);
    return body && eval_int(spec, body, env, out, depth + 1);
  }
  case NODE_ITE: {
    Node *branch;
    if (!select_ite_branch(spec, n, env, &branch, depth + 1))
      return false;
    return eval_int(spec, branch, env, out, depth + 1);
  }
  case NODE_SUM:
  case NODE_PRODUCT:
    return eval_int_reduction(spec, n, env, out, depth + 1);
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
      fprintf(tlsf_diagnostic_stream(), "expand: division by zero\n");
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
    fprintf(tlsf_diagnostic_stream(),
            "expand: non-integer expression in numeric context\n");
    return false;
  }
}

static bool eval_bool(const TlsfSpec *spec, const Node *n, const Env *env,
                      bool *out, int depth) {
  if (depth > MAX_DEPTH) {
    fprintf(tlsf_diagnostic_stream(), "expand: recursion too deep\n");
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
  case NODE_CMP_NE: {
    EvalValue a, b;
    if (!eval_value(spec, n->lhs, env, &a, depth + 1) ||
        !eval_value(spec, n->rhs, env, &b, depth + 1))
      return false;
    bool equal = value_equal(&a, &b);
    *out = n->kind == NODE_CMP_EQ ? equal : !equal;
    return true;
  }
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE: {
    int64_t a, b;
    if (!eval_int(spec, n->lhs, env, &a, depth) ||
        !eval_int(spec, n->rhs, env, &b, depth))
      return false;
    switch (n->kind) {
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
  case NODE_IN: {
    EvalValue value;
    EvalSet *set;
    if (!eval_value(spec, n->lhs, env, &value, depth + 1) ||
        !eval_set(spec, n->rhs, env, &set, depth + 1))
      return false;
    *out = false;
    for (uint32_t i = 0; i < set->count; i++)
      if (value_equal(&value, &set->items[i])) {
        *out = true;
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
    Node *branch;
    if (!select_ite_branch(spec, n, env, &branch, depth + 1))
      return false;
    return eval_bool(spec, branch, env, out, depth + 1);
  }
  case NODE_DEF_CALL: {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(tlsf_diagnostic_stream(), "expand: no definition '%s'/%u\n",
              n->callee, n->call_argc);
      return false;
    }
    Node *body = subst(spec->arena, d->body, d->params, n->call_args,
                       d->param_count, env);
    return body && eval_bool(spec, body, env, out, depth + 1);
  }
  default:
    fprintf(tlsf_diagnostic_stream(),
            "expand: non-boolean expression in a guard\n");
    return false;
  }
}

// ===========================================================================
// General values and sets
// ===========================================================================

static bool node_structural_equal(const Node *lhs, const Node *rhs) {
  if (lhs == rhs)
    return true;
  if (!lhs || !rhs || lhs->kind != rhs->kind)
    return false;
  // Compare the active payload of every kind. Source IDs, origin bindings and
  // expanded bounded metadata describe provenance, not formula meaning. The
  // strong flag is semantic on the three pre-expansion bounded kinds below.
  switch (lhs->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_INT:
    return lhs->ival == rhs->ival;
  case NODE_AP:
  case NODE_INT_VAR:
    return lhs->name == rhs->name;
  case NODE_SIZEOF:
    return lhs->sizeof_name == rhs->sizeof_name;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    return node_structural_equal(lhs->arg, rhs->arg);
  case NODE_BUS_INDEX:
    return lhs->bus_name == rhs->bus_name &&
           node_structural_equal(lhs->bus_index, rhs->bus_index);
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    if (lhs->callee != rhs->callee || lhs->call_argc != rhs->call_argc)
      return false;
    for (uint16_t i = 0; i < lhs->call_argc; i++)
      if (!node_structural_equal(lhs->call_args[i], rhs->call_args[i]))
        return false;
    return true;
  case NODE_ITE:
    return node_structural_equal(lhs->if_cond, rhs->if_cond) &&
           node_structural_equal(lhs->if_then, rhs->if_then) &&
           node_structural_equal(lhs->if_else, rhs->if_else);
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
    return lhs->qvar == rhs->qvar &&
           node_structural_equal(lhs->qlo, rhs->qlo) &&
           node_structural_equal(lhs->qhi, rhs->qhi) &&
           node_structural_equal(lhs->qset, rhs->qset) &&
           node_structural_equal(lhs->qbody, rhs->qbody) &&
           lhs->qlo_strict == rhs->qlo_strict &&
           lhs->qhi_strict == rhs->qhi_strict;
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    return node_structural_equal(lhs->qlo, rhs->qlo) &&
           node_structural_equal(lhs->qhi, rhs->qhi) &&
           node_structural_equal(lhs->qbody, rhs->qbody) &&
           lhs->bounded.strong == rhs->bounded.strong;
  case NODE_SET:
  case NODE_SET_ENUM:
    if (lhs->set_size != rhs->set_size)
      return false;
    for (uint16_t i = 0; i < lhs->set_size; i++)
      if (!node_structural_equal(lhs->set_elems[i], rhs->set_elems[i]))
        return false;
    return true;
  case NODE_NEXT_N:
    return lhs->bounded.strong == rhs->bounded.strong &&
           node_structural_equal(lhs->lhs, rhs->lhs) &&
           node_structural_equal(lhs->rhs, rhs->rhs);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_R:
  case NODE_W:
  case NODE_U:
  case NODE_M:
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
  case NODE_CMP_EQ:
  case NODE_CMP_NE:
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE:
  case NODE_SET_UNION:
  case NODE_SET_INTER:
  case NODE_SET_DIFF:
  case NODE_IN:
  case NODE_MATCH:
    return node_structural_equal(lhs->lhs, rhs->lhs) &&
           node_structural_equal(lhs->rhs, rhs->rhs);
  case NODE_KIND_COUNT:
    return false;
  }
  return false;
}

static bool value_equal(const EvalValue *lhs, const EvalValue *rhs) {
  if (lhs->kind != rhs->kind)
    return false;
  switch (lhs->kind) {
  case EVAL_VALUE_INT:
    return lhs->integer == rhs->integer;
  case EVAL_VALUE_NODE:
    return node_structural_equal(lhs->node, rhs->node);
  case EVAL_VALUE_SET:
    if (lhs->set->count != rhs->set->count)
      return false;
    for (uint32_t i = 0; i < lhs->set->count; i++) {
      bool found = false;
      for (uint32_t j = 0; j < rhs->set->count; j++)
        if (value_equal(&lhs->set->items[i], &rhs->set->items[j])) {
          found = true;
          break;
        }
      if (!found)
        return false;
    }
    return true;
  }
  return false;
}

static EvalSet *set_new(Arena *arena) { return ARENA_ALLOC(arena, EvalSet); }

static bool set_add(Arena *arena, EvalSet *set, EvalValue value) {
  for (uint32_t i = 0; i < set->count; i++)
    if (value_equal(&set->items[i], &value))
      return true;
  EvalValue *items = ARENA_ALLOC_N(arena, EvalValue, set->count + 1);
  if (!items)
    return false;
  for (uint32_t i = 0; i < set->count; i++)
    items[i] = set->items[i];
  items[set->count++] = value;
  set->items = items;
  return true;
}

static bool eval_value(const TlsfSpec *spec, const Node *n, const Env *env,
                       EvalValue *out, int depth) {
  if (depth > MAX_DEPTH) {
    fprintf(tlsf_diagnostic_stream(), "expand: recursion too deep\n");
    return false;
  }
  out->source = n;
  switch (n->kind) {
  case NODE_INT:
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
  case NODE_INT_NEG:
  case NODE_SIZEOF:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
  case NODE_SUM:
  case NODE_PRODUCT:
    out->kind = EVAL_VALUE_INT;
    return eval_int(spec, n, env, &out->integer, depth + 1);
  case NODE_SET:
  case NODE_SET_ENUM:
  case NODE_SET_UNION:
  case NODE_SET_INTER:
  case NODE_SET_DIFF:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
    out->kind = EVAL_VALUE_SET;
    return eval_set(spec, n, env, &out->set, depth + 1);
  case NODE_AP:
  case NODE_INT_VAR:
    if (env_lookup(env, n->name, &out->integer)) {
      out->kind = EVAL_VALUE_INT;
      return true;
    }
    {
      const DefDecl *d = find_def(spec, n->name, 0);
      if (d)
        return eval_value(spec, d->body, env, out, depth + 1);
    }
    out->kind = EVAL_VALUE_NODE;
    out->node = n;
    return true;
  case NODE_DEF_CALL: {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(tlsf_diagnostic_stream(), "expand: no definition '%s'/%u\n",
              n->callee, n->call_argc);
      return false;
    }
    Node *body = subst(spec->arena, d->body, d->params, n->call_args,
                       d->param_count, env);
    return body && eval_value(spec, body, env, out, depth + 1);
  }
  case NODE_ITE: {
    Node *branch;
    if (!select_ite_branch(spec, n, env, &branch, depth + 1))
      return false;
    return eval_value(spec, branch, env, out, depth + 1);
  }
  default:
    out->kind = EVAL_VALUE_NODE;
    out->node = n;
    return true;
  }
}

static bool eval_set(const TlsfSpec *spec, const Node *n, const Env *env,
                     EvalSet **out, int depth) {
  if (depth > MAX_DEPTH) {
    fprintf(tlsf_diagnostic_stream(), "expand: recursion too deep\n");
    return false;
  }
  Arena *arena = spec->arena;
  if (n->kind == NODE_SET) {
    EvalSet *set = set_new(arena);
    if (!set)
      return false;
    for (uint16_t i = 0; i < n->set_size; i++) {
      EvalValue value;
      if (!eval_value(spec, n->set_elems[i], env, &value, depth + 1) ||
          !set_add(arena, set, value))
        return false;
    }
    *out = set;
    return true;
  }
  if (n->kind == NODE_SET_ENUM) {
    int64_t first, second, last;
    if (n->set_size != 3 ||
        !eval_int(spec, n->set_elems[0], env, &first, depth + 1) ||
        !eval_int(spec, n->set_elems[1], env, &second, depth + 1) ||
        !eval_int(spec, n->set_elems[2], env, &last, depth + 1))
      return false;
    int64_t step = second - first;
    if (step == 0) {
      fprintf(tlsf_diagnostic_stream(), "expand: zero step in set range\n");
      return false;
    }
    EvalSet *set = set_new(arena);
    if (!set)
      return false;
    for (int64_t value = first;
         (step > 0 && value <= last) || (step < 0 && value >= last);) {
      Node *source = node_int(arena, value);
      if (!source)
        return false;
      EvalValue item = {
          .kind = EVAL_VALUE_INT, .integer = value, .source = source};
      if (!set_add(arena, set, item))
        return false;
      if ((step > 0 && value > INT64_MAX - step) ||
          (step < 0 && value < INT64_MIN - step))
        break;
      value += step;
    }
    *out = set;
    return true;
  }
  if (n->kind == NODE_SET_UNION || n->kind == NODE_SET_INTER ||
      n->kind == NODE_SET_DIFF) {
    EvalSet *lhs, *rhs;
    if (!eval_set(spec, n->lhs, env, &lhs, depth + 1) ||
        !eval_set(spec, n->rhs, env, &rhs, depth + 1))
      return false;
    EvalSet *set = set_new(arena);
    if (!set)
      return false;
    for (uint32_t i = 0; i < lhs->count; i++) {
      bool in_rhs = false;
      for (uint32_t j = 0; j < rhs->count; j++)
        if (value_equal(&lhs->items[i], &rhs->items[j])) {
          in_rhs = true;
          break;
        }
      if ((n->kind == NODE_SET_INTER && in_rhs) ||
          (n->kind == NODE_SET_DIFF && !in_rhs) || n->kind == NODE_SET_UNION)
        if (!set_add(arena, set, lhs->items[i]))
          return false;
    }
    if (n->kind == NODE_SET_UNION)
      for (uint32_t i = 0; i < rhs->count; i++)
        if (!set_add(arena, set, rhs->items[i]))
          return false;
    *out = set;
    return true;
  }
  if (n->kind == NODE_AP || n->kind == NODE_INT_VAR) {
    const DefDecl *d = find_def(spec, n->name, 0);
    if (d)
      return eval_set(spec, d->body, env, out, depth + 1);
  }
  if (n->kind == NODE_DEF_CALL) {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(tlsf_diagnostic_stream(), "expand: no definition '%s'/%u\n",
              n->callee, n->call_argc);
      return false;
    }
    Node *body =
        subst(arena, d->body, d->params, n->call_args, d->param_count, env);
    return body && eval_set(spec, body, env, out, depth + 1);
  }
  if (n->kind == NODE_ITE) {
    Node *branch;
    if (!select_ite_branch(spec, n, env, &branch, depth + 1))
      return false;
    return eval_set(spec, branch, env, out, depth + 1);
  }
  if (n->kind == NODE_SET_BIG_UNION || n->kind == NODE_SET_BIG_INTER) {
    return eval_set_reduction(spec, n, env, out, depth + 1);
  }
  fprintf(tlsf_diagnostic_stream(),
          "expand: non-set expression in set context\n");
  return false;
}

static bool eval_domain(const TlsfSpec *spec, const Node *n, const Env *env,
                        EvalSet **out, int depth) {
  if (n->qset)
    return eval_set(spec, n->qset, env, out, depth + 1);
  int64_t lo, hi;
  if (!eval_int(spec, n->qlo, env, &lo, depth + 1) ||
      !eval_int(spec, n->qhi, env, &hi, depth + 1))
    return false;
  int64_t first = n->qlo_strict ? lo + 1 : lo;
  int64_t last = n->qhi_strict ? hi - 1 : hi;
  EvalSet *set = set_new(spec->arena);
  if (!set)
    return false;
  for (int64_t value = first; value <= last;) {
    EvalValue item = {.kind = EVAL_VALUE_INT,
                      .integer = value,
                      .source = node_int(spec->arena, value)};
    if (!item.source)
      return false;
    if (!set_add(spec->arena, set, item))
      return false;
    if (value == INT64_MAX)
      break;
    value++;
  }
  *out = set;
  return true;
}

static bool bind_reduction_body(const TlsfSpec *spec, const Node *n,
                                const Env *env, const EvalValue *value,
                                Env *child, const Env **body_env, Node **body) {
  n = subst_source(n, env);
  *body = n->qbody;
  *body_env = env;
  if (value->kind == EVAL_VALUE_INT) {
    *child = (Env){.b = {.name = n->qvar, .value = value->integer},
                   .parent = env,
                   .binder_id = n->source_id,
                   .copies = env->copies};
    *body_env = child;
    return true;
  }
  if (!value->source) {
    fprintf(tlsf_diagnostic_stream(),
            "expand: set binder value cannot be substituted\n");
    return false;
  }
  if (spec->capture_provenance)
    ((TlsfSpec *)spec)->provenance_ambiguous = true;
  const char *formal = n->qvar;
  Node *actual = (Node *)value->source;
  *body = subst(spec->arena, n->qbody, &formal, &actual, 1, env);
  return *body != nullptr;
}

static bool eval_int_reduction(const TlsfSpec *spec, const Node *n,
                               const Env *env, int64_t *out, int depth) {
  EvalSet *domain;
  if (!eval_domain(spec, n, env, &domain, depth + 1))
    return false;
  int64_t acc = n->kind == NODE_PRODUCT ? 1 : 0;
  for (uint32_t i = 0; i < domain->count; i++) {
    Env child;
    const Env *body_env;
    Node *body;
    int64_t value;
    if (!bind_reduction_body(spec, n, env, &domain->items[i], &child, &body_env,
                             &body) ||
        !eval_int(spec, body, body_env, &value, depth + 1))
      return false;
    acc = n->kind == NODE_PRODUCT ? acc * value : acc + value;
  }
  *out = acc;
  return true;
}

static bool eval_set_reduction(const TlsfSpec *spec, const Node *n,
                               const Env *env, EvalSet **out, int depth) {
  EvalSet *domain;
  if (!eval_domain(spec, n, env, &domain, depth + 1))
    return false;
  if (n->kind == NODE_SET_BIG_INTER && domain->count == 0) {
    fprintf(tlsf_diagnostic_stream(),
            "expand: intersection over an empty domain\n");
    return false;
  }
  EvalSet *acc = set_new(spec->arena);
  if (!acc)
    return false;
  bool first = true;
  for (uint32_t i = 0; i < domain->count; i++) {
    Env child;
    const Env *body_env;
    Node *body;
    EvalSet *term;
    if (!bind_reduction_body(spec, n, env, &domain->items[i], &child, &body_env,
                             &body) ||
        !eval_set(spec, body, body_env, &term, depth + 1))
      return false;
    if (n->kind == NODE_SET_BIG_UNION) {
      for (uint32_t j = 0; j < term->count; j++)
        if (!set_add(spec->arena, acc, term->items[j]))
          return false;
    } else if (first) {
      for (uint32_t j = 0; j < term->count; j++)
        if (!set_add(spec->arena, acc, term->items[j]))
          return false;
    } else {
      EvalSet *next = set_new(spec->arena);
      if (!next)
        return false;
      for (uint32_t j = 0; j < acc->count; j++)
        for (uint32_t k = 0; k < term->count; k++)
          if (value_equal(&acc->items[j], &term->items[k])) {
            if (!set_add(spec->arena, next, acc->items[j]))
              return false;
            break;
          }
      acc = next;
    }
    first = false;
  }
  *out = acc;
  return true;
}

// ===========================================================================
// Structural pattern guards
// ===========================================================================

typedef struct PatternBinding {
  const char *name;
  Node *value;
  struct PatternBinding *next;
} PatternBinding;

static bool name_is_declared(const TlsfSpec *spec, const char *name) {
  for (uint16_t i = 0; i < spec->param_count; i++)
    if (spec->params[i].name == name)
      return true;
  for (uint16_t i = 0; i < spec->def_count; i++)
    if (spec->defs[i].name == name)
      return true;
  for (uint32_t i = 0; i < spec->input_count; i++)
    if (spec->inputs[i].name == name)
      return true;
  for (uint32_t i = 0; i < spec->output_count; i++)
    if (spec->outputs[i].name == name)
      return true;
  return false;
}

static bool match_pattern(const TlsfSpec *spec, Node *subject,
                          const Node *pattern, PatternBinding **bindings,
                          bool *ok) {
  if (pattern->kind == NODE_AP) {
    if (strcmp(pattern->name, "_") == 0)
      return true;
    if (name_is_declared(spec, pattern->name)) {
      fprintf(tlsf_diagnostic_stream(),
              "expand: Binding Error: pattern identifier '%s' has a "
              "conflicting definition\n",
              pattern->name);
      *ok = false;
      return false;
    }
    for (PatternBinding *b = *bindings; b; b = b->next)
      if (b->name == pattern->name)
        return node_structural_equal(b->value, subject);
    PatternBinding *binding = ARENA_ALLOC(spec->arena, PatternBinding);
    if (!binding) {
      *ok = false;
      return false;
    }
    binding->name = pattern->name;
    binding->value = subject;
    binding->next = *bindings;
    *bindings = binding;
    return true;
  }
  if (subject->kind != pattern->kind)
    return false;
  switch (pattern->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return match_pattern(spec, subject->arg, pattern->arg, bindings, ok);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return match_pattern(spec, subject->lhs, pattern->lhs, bindings, ok) &&
           match_pattern(spec, subject->rhs, pattern->rhs, bindings, ok);
  case NODE_DEF_CALL:
    fprintf(tlsf_diagnostic_stream(),
            "expand: Binding Error: pattern identifier '%s' has a "
            "conflicting definition\n",
            pattern->callee);
    *ok = false;
    return false;
  default:
    return false;
  }
}

static bool select_ite_branch(const TlsfSpec *spec, const Node *n,
                              const Env *env, Node **out, int depth) {
  if (n->if_cond->kind != NODE_MATCH) {
    bool condition;
    if (!eval_bool(spec, n->if_cond, env, &condition, depth + 1))
      return false;
    *out = condition ? n->if_then : n->if_else;
    return true;
  }

  bool ok = true;
  Node *subject =
      expand_node((TlsfSpec *)spec, n->if_cond->lhs, env, &ok, depth + 1);
  if (!ok)
    return false;
  PatternBinding *bindings = nullptr;
  bool matched = match_pattern(spec, subject, n->if_cond->rhs, &bindings, &ok);
  if (!ok)
    return false;
  if (!matched) {
    *out = n->if_else;
    return true;
  }

  uint16_t count = 0;
  for (PatternBinding *b = bindings; b; b = b->next)
    count++;
  if (count == 0) {
    *out = n->if_then;
    return true;
  }
  const char **formals = ARENA_ALLOC_N(spec->arena, const char *, count);
  if (!formals)
    return false;
  Node **actuals = ARENA_ALLOC_N(spec->arena, Node *, count);
  if (!actuals)
    return false;
  uint16_t i = 0;
  for (PatternBinding *b = bindings; b; b = b->next) {
    formals[i] = b->name;
    actuals[i] = b->value;
    i++;
  }
  *out = subst(spec->arena, n->if_then, formals, actuals, count, env);
  return *out != nullptr;
}

// ===========================================================================
// Formula expansion
// ===========================================================================

static const char *bus_elem_name(TlsfSpec *spec, const char *bus, int64_t idx) {
  char buf[256];
  snprintf(buf, sizeof buf, "%s_%lld", bus, (long long)idx);
  return intern(spec->intern, buf);
}

static Node *bus_elem_node(TlsfSpec *spec, const char *bus, int64_t idx) {
  const char *name = bus_elem_name(spec, bus, idx);
  return name ? node_ap(spec->arena, name) : nullptr;
}

static Node *with_bounded(Arena *arena, const Node *node, const Node *source,
                          BoundedTemporalOrigin origin, int64_t lo, int64_t hi,
                          Node *body) {
  // A zero bound can return a source atom directly. Never attach metadata to
  // that shared input: expansion must leave it untouched on failure.
  Node *copy = ARENA_ALLOC(arena, Node);
  if (!copy)
    return nullptr;
  *copy = *node;
  copy->bounded.strong = source->bounded.strong;
  node_set_bounded(copy, origin, lo, hi, body);
  return copy;
}

static Node *expand_quantifier(TlsfSpec *spec, const Node *n, const Env *env,
                               bool *ok, int depth) {
  EvalSet *domain;
  if (!eval_domain(spec, n, env, &domain, depth + 1)) {
    *ok = false;
    return nullptr;
  }
  bool is_all = (n->kind == NODE_FORALL);

  if (domain->count == 0)
    return is_all ? node_true(spec->arena) : node_false(spec->arena);

  Node *acc = nullptr;
  for (uint32_t i = 0; i < domain->count; i++) {
    Env child;
    const Env *body_env;
    Node *body;
    if (!bind_reduction_body(spec, n, env, &domain->items[i], &child, &body_env,
                             &body)) {
      *ok = false;
      return nullptr;
    }
    Node *term = expand_node(spec, body, body_env, ok, depth + 1);
    if (!*ok)
      return nullptr;
    acc = !acc ? term
               : (is_all ? node_and(spec->arena, acc, term)
                         : node_or(spec->arena, acc, term));
    if (!acc)
      return nullptr;
  }
  return acc;
}

static Node *expand_node(TlsfSpec *spec, const Node *n, const Env *env,
                         bool *ok, int depth) {
  n = subst_source(n, env);
  if (!*ok || !n || arena_failed(spec->arena)) {
    *ok = false;
    return nullptr;
  }
  Node *result = expand_node_impl(spec, n, env, ok, depth);
  if (!result || arena_failed(spec->arena)) {
    *ok = false;
    return nullptr;
  }
  if (!spec->capture_provenance)
    return result;
  Node *copy = ARENA_ALLOC(spec->arena, Node);
  if (!copy) {
    *ok = false;
    return nullptr;
  }
  *copy = *result;
  copy->source_id = n->source_id;
  const OriginBinding *bindings = nullptr;
  for (const Env *e = env; e; e = e->parent) {
    if (!e->binder_id)
      continue;
    OriginBinding *entry = ARENA_ALLOC(spec->arena, OriginBinding);
    if (!entry) {
      *ok = false;
      return nullptr;
    }
    *entry = (OriginBinding){.binder_id = e->binder_id,
                             .name = e->b.name,
                             .value = e->b.value,
                             .parent = bindings};
    bindings = entry;
  }
  copy->origin_bindings = bindings;
  return copy;
}

static Node *expand_node_impl(TlsfSpec *spec, const Node *n, const Env *env,
                              bool *ok, int depth) {
  if (!*ok || !n)
    return nullptr;
  Arena *a = spec->arena;
  if (depth > MAX_DEPTH) {
    fprintf(tlsf_diagnostic_stream(), "expand: recursion too deep\n");
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
    if (!*ok)                                                                  \
      return nullptr;                                                          \
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

  // Formula-level (in)equality.  `bus == LABEL` (LABEL an enum label) becomes a
  // positional bit match against the label's pattern; otherwise it is a plain
  // integer comparison that folds to a constant.
  case NODE_CMP_EQ:
  case NODE_CMP_NE: {
    const char *bits = nullptr;
    const Node *bus = nullptr;
    if (n->rhs->kind == NODE_AP)
      bits = spec_find_enum_label(spec, n->rhs->name);
    if (bits) {
      bus = n->lhs;
    } else if (n->lhs->kind == NODE_AP) {
      bits = spec_find_enum_label(spec, n->lhs->name);
      bus = n->rhs;
    }

    if (bits) {
      if (bus->kind != NODE_AP) {
        fprintf(tlsf_diagnostic_stream(),
                "expand: enum label compared against a non-signal\n");
        *ok = false;
        return nullptr;
      }
      // A label denotes a comma-separated union of valuations.  Within one
      // valuation, '*' leaves that bit unconstrained.
      Node *allowed = nullptr;
      const char *valuation = bits;
      while (*valuation) {
        const char *end = strchr(valuation, ',');
        size_t width = end ? (size_t)(end - valuation) : strlen(valuation);
        Node *match = nullptr;
        for (size_t i = 0; i < width; i++) {
          if (valuation[i] == '*')
            continue;
          Node *elem = bus_elem_node(spec, bus->name, (int64_t)i);
          if (!elem)
            return nullptr;
          Node *term = valuation[i] == '1' ? elem : node_not(a, elem);
          if (!term)
            return nullptr;
          match = match ? node_and(a, match, term) : term;
          if (!match)
            return nullptr;
        }
        if (!match)
          match = node_true(a);
        if (!match)
          return nullptr;
        allowed = allowed ? node_or(a, allowed, match) : match;
        if (!allowed)
          return nullptr;
        valuation = end ? end + 1 : valuation + width;
      }
      if (!allowed)
        allowed = node_false(a);
      if (!allowed)
        return nullptr;
      return n->kind == NODE_CMP_NE ? node_not(a, allowed) : allowed;
    }

    // Plain integer comparison in formula position: fold to a constant.
    bool b;
    if (!eval_bool(spec, n, env, &b, depth)) {
      *ok = false;
      return nullptr;
    }
    return b ? node_true(a) : node_false(a);
  }
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE:
  case NODE_IN: {
    bool value;
    if (!eval_bool(spec, n, env, &value, depth + 1)) {
      *ok = false;
      return nullptr;
    }
    return value ? node_true(a) : node_false(a);
  }

  case NODE_BUS_INDEX: {
    int64_t idx;
    if (!eval_int(spec, n->bus_index, env, &idx, depth)) {
      *ok = false;
      return nullptr;
    }
    return bus_elem_node(spec, n->bus_name, idx);
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
      fprintf(tlsf_diagnostic_stream(), "expand: negative count in X[...]\n");
      *ok = false;
      return nullptr;
    }
    Node *expanded_body = expand_node(spec, n->rhs, env, ok, depth);
    if (!*ok)
      return nullptr;
    Node *body = expanded_body;
    for (int64_t i = 0; i < count; i++) {
      body = n->bounded.strong ? node_x_strong(a, body) : node_x(a, body);
      if (!body)
        return nullptr;
    }
    return with_bounded(a, body, n, BOUNDED_NEXT, count, count, expanded_body);
  }

  case NODE_G_RANGE:
  case NODE_F_RANGE: {
    // G[lo:hi] b == AND_{k=lo..hi} X^k b ;  F[lo:hi] b == OR_{k=lo..hi} X^k b.
    int64_t lo, hi;
    if (!eval_int(spec, n->qlo, env, &lo, depth) ||
        !eval_int(spec, n->qhi, env, &hi, depth)) {
      *ok = false;
      return nullptr;
    }
    if (lo < 0 || hi < 0) {
      fprintf(tlsf_diagnostic_stream(),
              "expand: negative bound in G[..]/F[..]\n");
      *ok = false;
      return nullptr;
    }
    bool conj = (n->kind == NODE_G_RANGE);
    Node *acc = nullptr;
    Node *meta_body = nullptr;
    for (int64_t k = lo; k <= hi; k++) {
      // Expand the body afresh each step: the copies must not alias (later
      // passes such as the Mealy/Moore signal wrap mutate nodes in place).
      Node *body = expand_node(spec, n->qbody, env, ok, depth);
      if (!*ok)
        return nullptr;
      if (!meta_body)
        meta_body = body;
      for (int64_t i = 0; i < k; i++) {
        body = n->bounded.strong ? node_x_strong(a, body) : node_x(a, body);
        if (!body)
          return nullptr;
      }
      acc =
          acc ? (conj ? node_and(a, acc, body) : node_or(a, acc, body)) : body;
      if (!acc)
        return nullptr;
    }
    // Empty range (lo > hi): empty conjunction is true, empty disjunction
    // false.
    if (!acc)
      acc = conj ? node_true(a) : node_false(a);
    if (!acc)
      return nullptr;
    return with_bounded(a, acc, n, conj ? BOUNDED_G_RANGE : BOUNDED_F_RANGE, lo,
                        hi, meta_body);
  }

  // Definition guard: evaluate the condition, expand the chosen branch.
  case NODE_ITE: {
    Node *branch;
    if (!select_ite_branch(spec, n, env, &branch, depth + 1)) {
      *ok = false;
      return nullptr;
    }
    return expand_node(spec, branch, env, ok, depth + 1);
  }

  // Definition call: substitute the actuals into the body and expand.
  case NODE_DEF_CALL: {
    const DefDecl *d = find_def(spec, n->callee, n->call_argc);
    if (!d) {
      fprintf(tlsf_diagnostic_stream(), "expand: no definition '%s'/%u\n",
              n->callee, n->call_argc);
      *ok = false;
      return nullptr;
    }
    Node *body =
        subst(a, d->body, d->params, n->call_args, d->param_count, env);
    if (!body)
      return nullptr;
    return expand_node(spec, body, env, ok, depth + 1);
  }

  case NODE_PATTERN:
    fprintf(tlsf_diagnostic_stream(), "expand: pattern '%s' not supported\n",
            n->callee);
    *ok = false;
    return nullptr;

  default:
    fprintf(tlsf_diagnostic_stream(),
            "expand: unexpected node kind %d in formula\n", n->kind);
    *ok = false;
    return nullptr;
  }
#undef XUNARY
#undef XBINARY
}

// ===========================================================================
// Parameter environment and signal explosion
// ===========================================================================

static Env *build_param_env(TlsfSpec *spec, Env *head) {
  for (uint16_t i = 0; i < spec->param_count; i++) {
    Env *e = ARENA_ALLOC(spec->arena, Env);
    if (!e)
      return nullptr;
    e->b.name = spec->params[i].name;
    e->b.value = spec->params[i].value;
    e->parent = head;
    e->copies = head->copies;
    head = e;
  }
  return head;
}

// A narrow structural proof for a source-defined bit width: floor(log2(x))
// by halving, then 1+floor(log2(x-1)). Callee and formal names are irrelevant.
static bool is_formal(const Node *node, const char *formal) {
  return node && (node->kind == NODE_AP || node->kind == NODE_INT_VAR) &&
         node->name == formal;
}

static bool is_integer(const Node *node, int64_t value) {
  return node && node->kind == NODE_INT && node->ival == value;
}

static bool is_formal_comparison(const Node *node, NodeKind kind,
                                 const char *formal, int64_t value) {
  return node && node->kind == kind && is_formal(node->lhs, formal) &&
         is_integer(node->rhs, value);
}

static const Node *otherwise_value(const Node *node) {
  return node && node->kind == NODE_ITE && node->if_cond &&
                 node->if_cond->kind == NODE_TRUE
             ? node->if_then
             : nullptr;
}

static const Node *one_plus(const Node *node) {
  if (!node || node->kind != NODE_INT_ADD)
    return nullptr;
  if (is_integer(node->lhs, 1))
    return node->rhs;
  return is_integer(node->rhs, 1) ? node->lhs : nullptr;
}

static bool proves_floor_log2(const DefDecl *def) {
  if (!def || def->param_count != 1 || !def->body ||
      def->body->kind != NODE_ITE)
    return false;
  const char *formal = def->params[0];
  const Node *body = def->body;
  if (!is_formal_comparison(body->if_cond, NODE_CMP_LE, formal, 1) ||
      !is_integer(body->if_then, 0))
    return false;
  const Node *step = one_plus(otherwise_value(body->if_else));
  return step && step->kind == NODE_DEF_CALL && step->callee == def->name &&
         step->call_argc == 1 && step->call_args[0] &&
         step->call_args[0]->kind == NODE_INT_DIV &&
         is_formal(step->call_args[0]->lhs, formal) &&
         is_integer(step->call_args[0]->rhs, 2);
}

static bool proves_bit_width(const TlsfSpec *spec, const Node *width) {
  if (!width || width->kind != NODE_INT_SUB || !is_integer(width->rhs, 1) ||
      !width->lhs || width->lhs->kind != NODE_DEF_CALL ||
      width->lhs->call_argc != 1)
    return false;
  const DefDecl *def = find_def(spec, width->lhs->callee, 1);
  if (!def || !def->body || def->body->kind != NODE_ITE ||
      def->param_count != 1)
    return false;
  const char *formal = def->params[0];
  const Node *body = def->body;
  if (!is_formal_comparison(body->if_cond, NODE_CMP_EQ, formal, 0) ||
      !is_integer(body->if_then, 0))
    return false;
  const Node *step = one_plus(otherwise_value(body->if_else));
  if (!step || step->kind != NODE_DEF_CALL || step->call_argc != 1 ||
      !step->call_args[0] || step->call_args[0]->kind != NODE_INT_SUB ||
      !is_formal(step->call_args[0]->lhs, formal) ||
      !is_integer(step->call_args[0]->rhs, 1))
    return false;
  return proves_floor_log2(find_def(spec, step->callee, 1));
}

typedef struct SourceIdChange {
  Node *node;
  struct SourceIdChange *next;
} SourceIdChange;

typedef struct {
  Arena *arena;
  uint32_t next;
  SourceIdChange *changes;
} SourceIds;

static void assign_node_ids(Node *n, SourceIds *ids) {
  if (!n || n->source_id || arena_failed(ids->arena))
    return;
  SourceIdChange *change = ARENA_ALLOC(ids->arena, SourceIdChange);
  if (!change)
    return;
  *change = (SourceIdChange){.node = n, .next = ids->changes};
  ids->changes = change;
  n->source_id = ids->next++;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
  case NODE_AP:
  case NODE_INT_VAR:
  case NODE_SIZEOF:
    return;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    assign_node_ids(n->arg, ids);
    return;
  case NODE_BUS_INDEX:
    assign_node_ids(n->bus_index, ids);
    return;
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    for (uint16_t i = 0; i < n->call_argc; i++)
      assign_node_ids(n->call_args[i], ids);
    return;
  case NODE_ITE:
    assign_node_ids(n->if_cond, ids);
    assign_node_ids(n->if_then, ids);
    assign_node_ids(n->if_else, ids);
    return;
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    assign_node_ids(n->qlo, ids);
    assign_node_ids(n->qhi, ids);
    if (n->kind != NODE_G_RANGE && n->kind != NODE_F_RANGE)
      assign_node_ids(n->qset, ids);
    assign_node_ids(n->qbody, ids);
    return;
  case NODE_SET:
  case NODE_SET_ENUM:
    for (uint16_t i = 0; i < n->set_size; i++)
      assign_node_ids(n->set_elems[i], ids);
    return;
  default:
    assign_node_ids(n->lhs, ids);
    assign_node_ids(n->rhs, ids);
    return;
  }
}

static void assign_source_ids(TlsfSpec *spec, SourceIds *ids) {
  for (uint16_t i = 0; i < spec->def_count; i++)
    assign_node_ids(spec->defs[i].body, ids);
  FormulaList *lists[] = {&spec->initially, &spec->preset, &spec->require,
                          &spec->assert_,   &spec->assume, &spec->guarantee};
  for (size_t k = 0; k < sizeof lists / sizeof *lists; k++)
    for (uint32_t i = 0; i < lists[k]->count; i++)
      assign_node_ids(lists[k]->formulas[i], ids);
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
      SignalDecl *expanded = is_output ? &spec->outputs[spec->output_count - 1]
                                       : &spec->inputs[spec->input_count - 1];
      expanded->origin_id = s->origin_id;
      continue;
    }
    for (int64_t v = s->bus_lo; v <= (int64_t)s->bus_hi; v++) {
      const char *name = bus_elem_name(spec, s->name, v);
      if (!name ||
          !spec_add_signal(spec, is_output, name, false, nullptr, nullptr))
        return -1;
      SignalDecl *expanded = is_output ? &spec->outputs[spec->output_count - 1]
                                       : &spec->inputs[spec->input_count - 1];
      expanded->origin_name = s->name;
      expanded->origin_id = s->origin_id;
      expanded->origin_index = (uint16_t)v;
      expanded->origin_bus_lo = s->bus_lo;
      expanded->origin_bus_hi = s->bus_hi;
      expanded->origin_is_bus = true;
      expanded->origin_is_enum = s->origin_is_enum;
      expanded->origin_width_expr = s->origin_width_expr;
      expanded->bus_lo_expr = s->bus_lo_expr;
      expanded->origin_is_encoded_bit = s->origin_is_encoded_bit;
    }
  }
  return 0;
}

// ===========================================================================
// Public entry point
// ===========================================================================

static int expand_impl(TlsfSpec *spec, const ParamOverride *overrides,
                       size_t n_overrides) {
  // --- Phase 1: resolve parameter values (apply overrides over defaults). ---
  for (size_t i = 0; i < n_overrides; i++) {
    const char *iname = intern(spec->intern, overrides[i].name);
    if (!iname)
      return -1;
    bool found = false;
    for (uint16_t j = 0; j < spec->param_count; j++)
      if (spec->params[j].name == iname) {
        spec->params[j].value = overrides[i].value;
        spec->params[j].has_default = true;
        found = true;
        break;
      }
    if (!found) {
      fprintf(tlsf_diagnostic_stream(), "expand: unknown parameter '%s'\n",
              overrides[i].name);
      return -1;
    }
  }
  for (uint16_t i = 0; i < spec->param_count; i++)
    if (!spec->params[i].has_default) {
      fprintf(tlsf_diagnostic_stream(),
              "expand: parameter '%s' has no value (use --param)\n",
              spec->params[i].name);
      return -1;
    }

  SubstCopy *copies = nullptr;
  Env base = {.copies = &copies};
  Env *env = build_param_env(spec, &base);
  if (arena_failed(spec->arena))
    return -1;

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
      // Signal indices are stored as uint16_t; an empty or wider range would
      // otherwise wrap into a bus of up to 65536 bits.
      if (lo > hi) {
        fprintf(tlsf_diagnostic_stream(),
                "expand: bus '%s' has an empty range [%lld..%lld]\n", s->name,
                (long long)lo, (long long)hi);
        return -1;
      }
      if (lo < 0 || hi > UINT16_MAX) {
        fprintf(tlsf_diagnostic_stream(),
                "expand: bus '%s' range [%lld..%lld] is outside 0..%d\n",
                s->name, (long long)lo, (long long)hi, UINT16_MAX);
        return -1;
      }
      s->bus_lo = (uint16_t)lo;
      s->bus_hi = (uint16_t)hi;
      s->origin_bus_lo = s->bus_lo;
      s->origin_bus_hi = s->bus_hi;
    }

  // Classify only widths whose source definitions have the proved structural
  // shape above. Other computed widths remain undetermined.
  if (spec->capture_provenance)
    for (int k = 0; k < 2; k++)
      for (uint32_t i = 0; i < sig_counts[k]; i++) {
        SignalDecl *s = &sig_lists[k][i];
        s->origin_is_encoded_bit = s->is_bus && s->bus_lo == 0 &&
                                   s->bus_hi_expr &&
                                   proves_bit_width(spec, s->bus_hi_expr);
      }

  // --- Phase 3: expand every formula. ---
  bool ok = true;
#define EXPAND_LIST(list)                                                      \
  do {                                                                         \
    for (uint32_t _i = 0; _i < (list).count; _i++) {                           \
      Node *expanded = expand_node(spec, (list).formulas[_i], env, &ok, 0);    \
      if (!ok || !expanded)                                                    \
        return -1;                                                             \
      (list).formulas[_i] = expanded;                                          \
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
  if (explode_signals(spec, false) != 0 || explode_signals(spec, true) != 0) {
    fprintf(tlsf_diagnostic_stream(), "expand: out of memory\n");
    return -1;
  }

  // Clear the GLOBAL section — it has been expanded away.
  spec->params = nullptr;
  spec->param_count = 0;
  spec->defs = nullptr;
  spec->def_count = 0;
  return arena_failed(spec->arena) ? -1 : 0;
}

int expand(TlsfSpec *spec, const ParamOverride *overrides, size_t n_overrides) {
  assert(spec);
  if (arena_failed(spec->arena))
    return -1;

  // Stage mutable arrays and publish once. Nodes are rebuilt by expand_node;
  // neither a later formula nor signal-allocation failure may expose a partial
  // expansion through an earlier slot.
  TlsfSpec next = *spec;
#define COPY_ARRAY(field, type, count)                                         \
  do {                                                                         \
    if (count) {                                                               \
      next.field = ARENA_ALLOC_N(spec->arena, type, count);                    \
      if (!next.field)                                                         \
        return -1;                                                             \
      memcpy(next.field, spec->field, count * sizeof *next.field);             \
    }                                                                          \
  } while (0)
  COPY_ARRAY(params, ParamDecl, spec->param_count);
  COPY_ARRAY(inputs, SignalDecl, spec->input_count);
  COPY_ARRAY(outputs, SignalDecl, spec->output_count);
  COPY_ARRAY(initially.formulas, Node *, spec->initially.capacity);
  COPY_ARRAY(require.formulas, Node *, spec->require.capacity);
  COPY_ARRAY(assume.formulas, Node *, spec->assume.capacity);
  COPY_ARRAY(preset.formulas, Node *, spec->preset.capacity);
  COPY_ARRAY(assert_.formulas, Node *, spec->assert_.capacity);
  COPY_ARRAY(guarantee.formulas, Node *, spec->guarantee.capacity);
#undef COPY_ARRAY
  ParamDecl *resolved_params = next.params;
  // Source nodes are shared with the caller. Undo only IDs assigned here if
  // expansion fails, including a failure while recording the assignments.
  SourceIds ids = {.arena = spec->arena, .next = 1};
  if (spec->capture_provenance)
    assign_source_ids(&next, &ids);
  if (arena_failed(spec->arena) ||
      expand_impl(&next, overrides, n_overrides) != 0) {
    for (SourceIdChange *change = ids.changes; change; change = change->next)
      change->node->source_id = 0;
    return -1;
  }
  // Provenance retains the original parameter array after GLOBAL is cleared.
  if (spec->param_count)
    memcpy(spec->params, resolved_params,
           spec->param_count * sizeof *resolved_params);
  *spec = next;
  return 0;
}
