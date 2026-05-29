#include "tlsf/expand.h"

#include <assert.h>
#include <stdio.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Forward declarations
// ---------------------------------------------------------------------------

static int resolve_parameters(TlsfSpec *spec,
                               const ParamOverride *overrides,
                               size_t n_overrides);
static int inline_definitions(TlsfSpec *spec);
static int unroll_buses(TlsfSpec *spec);
static int instantiate_patterns(TlsfSpec *spec);

// Helper: apply a visitor to every formula in the spec.
typedef Node *(*NodeTransform)(Node *n, void *ctx, Arena *a);
static void transform_all_formulas(TlsfSpec *spec, NodeTransform fn,
                                   void *ctx);

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

int expand(TlsfSpec *spec, const ParamOverride *overrides,
           size_t n_overrides) {
  assert(spec);

  if (resolve_parameters(spec, overrides, n_overrides) != 0)
    return -1;
  if (inline_definitions(spec) != 0)
    return -1;
  if (unroll_buses(spec) != 0)
    return -1;
  if (instantiate_patterns(spec) != 0)
    return -1;

  // Post-condition: no high-level nodes should remain.
#ifndef NDEBUG
  // TODO: add a debug assertion walk that checks node_kind_is_high_level()
  // returns false for every node in every formula list.
#endif

  // Clear the GLOBAL section — it's no longer meaningful.
  spec->params = nullptr;
  spec->param_count = 0;
  spec->defs = nullptr;
  spec->def_count = 0;

  return 0;
}

// ---------------------------------------------------------------------------
// Phase 1: Parameter resolution
//
// Walk spec->params, apply any overrides, evaluate default expressions.
// Builds a name→value table that subsequent phases consult.
// ---------------------------------------------------------------------------

static int resolve_parameters(TlsfSpec *spec,
                               const ParamOverride *overrides,
                               size_t n_overrides) {
  // Apply overrides first.
  for (size_t i = 0; i < n_overrides; i++) {
    const char *iname = intern(spec->intern, overrides[i].name);
    bool found = false;
    for (uint16_t j = 0; j < spec->param_count; j++) {
      if (spec->params[j].name == iname) {
        spec->params[j].value = overrides[i].value;
        found = true;
        break;
      }
    }
    if (!found) {
      fprintf(stderr, "expand: unknown parameter '%s'\n", overrides[i].name);
      return -1;
    }
  }

  // For parameters without an override, use the default value.
  // Integer expressions in defaults are evaluated here.
  for (uint16_t i = 0; i < spec->param_count; i++) {
    ParamDecl *p = &spec->params[i];
    // If no override was applied and spec has a default, use it.
    // TODO: evaluate default integer expression (currently stored raw).
    (void)p;
  }

  return 0;
}

// ---------------------------------------------------------------------------
// Phase 2: Definition inlining
//
// For each NODE_DEF_CALL node, substitute the callee's body with actual
// arguments bound to formal parameters, then recurse.  Cycle detection
// prevents infinite loops from mutually-recursive definitions.
// ---------------------------------------------------------------------------

// Inlining context threaded through the recursive transform.
typedef struct {
  TlsfSpec *spec;
  // TODO: add a "currently expanding" set (interned names) for cycle detect.
  // TODO: add a binding map for the current call's formal→actual params.
} InlineCtx;

static Node *inline_node(Node *n, void *ctx, Arena *a) {
  (void)a;
  InlineCtx *c = ctx;
  (void)c;

  if (!n)
    return nullptr;

  switch (n->kind) {
  case NODE_DEF_CALL:
    // TODO:
    //   1. Look up n->callee in spec->defs.
    //   2. Check for recursive call (cycle detection).
    //   3. Bind n->call_args[i] → formal params[i].
    //   4. Recursively transform the body under the new binding.
    //   5. Return the transformed body (fresh arena-copy).
    fprintf(stderr, "expand: definition inlining not yet implemented\n");
    return n;

  case NODE_INT_VAR:
    // TODO: look up parameter value and return NODE_INT.
    return n;

  default:
    return n; // structural recursion handled by transform_all_formulas
  }
}

static int inline_definitions(TlsfSpec *spec) {
  InlineCtx ctx = {.spec = spec};
  transform_all_formulas(spec, inline_node, &ctx);
  return 0;
}

// ---------------------------------------------------------------------------
// Phase 3: Bus unrolling
//
// Replace NODE_BUS_INDEX with the concrete scalar signal name (name_i).
// Replace quantified set expressions (NODE_FORALL/EXISTS over a range) with
// explicit conjunctions/disjunctions.
// ---------------------------------------------------------------------------

typedef struct {
  TlsfSpec *spec;
} BusCtx;

static Node *unroll_node(Node *n, void *ctx, Arena *a) {
  BusCtx *c = ctx;
  (void)a;

  if (!n)
    return nullptr;

  switch (n->kind) {
  case NODE_BUS_INDEX:
    // TODO:
    //   1. Evaluate n->bus_index (must be a ground integer after phase 1+2).
    //   2. Construct interned name "bus_name_<i>".
    //   3. Return NODE_AP with the constructed name.
    fprintf(stderr, "expand: bus unrolling not yet implemented\n");
    return n;

  case NODE_FORALL:
    // TODO: expand G[x:S] phi  →  phi[x:=s1] ∧ phi[x:=s2] ∧ ...
    return n;

  case NODE_EXISTS:
    // TODO: expand F[x:S] phi  →  phi[x:=s1] ∨ phi[x:=s2] ∨ ...
    return n;

  default:
    return n;
  }
  (void)c;
}

static int unroll_buses(TlsfSpec *spec) {
  BusCtx ctx = {.spec = spec};
  transform_all_formulas(spec, unroll_node, &ctx);
  return 0;
}

// ---------------------------------------------------------------------------
// Phase 4: Pattern instantiation
//
// TLSF v1.1 defines several named synthesis patterns (e.g. "or", "and",
// "mux", "delay", "counter", ...).  NODE_PATTERN nodes are replaced with
// their LTL expansions.
// ---------------------------------------------------------------------------

static Node *instantiate_node(Node *n, void *ctx, Arena *a) {
  (void)ctx;
  (void)a;

  if (!n || n->kind != NODE_PATTERN)
    return n;

  // TODO: dispatch on n->callee and produce the pattern's LTL body.
  fprintf(stderr, "expand: pattern '%s' not yet implemented\n", n->callee);
  return n;
}

static int instantiate_patterns(TlsfSpec *spec) {
  transform_all_formulas(spec, instantiate_node, nullptr);
  return 0;
}

// ---------------------------------------------------------------------------
// Helper: bottom-up structural transform over all formula lists.
//
// Applies `fn` to every node bottom-up.  fn may return a replacement node
// (possibly newly allocated from `a`); returning the same pointer is fine.
// ---------------------------------------------------------------------------

static Node *transform_node(Node *n, NodeTransform fn, void *ctx, Arena *a) {
  if (!n)
    return nullptr;

  // First recurse into children (bottom-up).
  switch (n->kind) {
  // Leaf nodes
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
  case NODE_INT:
  case NODE_INT_VAR:
    break;

  // Unary
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
    n->arg = transform_node(n->arg, fn, ctx, a);
    break;

  // Binary
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
    n->lhs = transform_node(n->lhs, fn, ctx, a);
    n->rhs = transform_node(n->rhs, fn, ctx, a);
    break;

  // Call nodes: recurse into arguments
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    for (uint16_t i = 0; i < n->call_argc; i++)
      n->call_args[i] = transform_node(n->call_args[i], fn, ctx, a);
    break;

  // Bus index: recurse into index expression
  case NODE_BUS_INDEX:
    n->bus_index = transform_node(n->bus_index, fn, ctx, a);
    break;

  // Set / quantifier children
  case NODE_SET:
  case NODE_SET_ENUM:
  case NODE_FORALL:
  case NODE_EXISTS:
    for (uint16_t i = 0; i < n->set_size; i++)
      n->set_elems[i] = transform_node(n->set_elems[i], fn, ctx, a);
    break;

  case NODE_KIND_COUNT:
    break;
  }

  // Then apply the transform function to this node.
  return fn(n, ctx, a);
}

// Apply a transform to every formula in every subsection.
#define TRANSFORM_LIST(list)                                                   \
  do {                                                                         \
    for (uint32_t _i = 0; _i < (list).count; _i++)                            \
      (list).formulas[_i] =                                                    \
          transform_node((list).formulas[_i], fn, ctx, spec->arena);          \
  } while (0)

static void transform_all_formulas(TlsfSpec *spec, NodeTransform fn,
                                   void *ctx) {
  TRANSFORM_LIST(spec->initially);
  TRANSFORM_LIST(spec->require);
  TRANSFORM_LIST(spec->assume);
  TRANSFORM_LIST(spec->preset);
  TRANSFORM_LIST(spec->assert_);
  TRANSFORM_LIST(spec->guarantee);
}

#undef TRANSFORM_LIST
