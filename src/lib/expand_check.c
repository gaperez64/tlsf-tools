#include "expand_check.h"
#include "diagnostic.h"
#include <string.h>

const char *expand_signal_name(const TlsfSpec *spec, const char *bus,
                               int64_t index) {
  int length = snprintf(nullptr, 0, "%s_%lld", bus, (long long)index);
  if (length < 0)
    return nullptr;
  char *name = ARENA_ALLOC_N(spec->arena, char, (size_t)length + 1);
  if (!name)
    return nullptr;
  snprintf(name, (size_t)length + 1, "%s_%lld", bus, (long long)index);
  return intern(spec->intern, name);
}

// TLSF v1.1 §§4.1–4.3, 4.6–4.7: resolve names in their declaration's
// lexical environment, before evaluating guards or enumerating domains.
// Function signatures are instantiated at each application (arguments have no
// declared types), including recursive applications (§4.6).
enum {
  T_NUM = 1,
  T_BOOL = 2,
  T_SIGNAL = 4,
  T_LTL = 8,
  T_BUS = 16,
  T_SET = 32,
  T_FORMULA = T_BOOL | T_SIGNAL | T_LTL,
  T_ANY = T_NUM | T_FORMULA | T_BUS | T_SET,
};

typedef struct Type {
  unsigned mask;
  struct Type *element, *link;
  struct Type *logical_left, *logical_right;
  bool checking_boolean, instance;
} Type;

typedef struct Scope {
  const char *name;
  Type *type;
  const struct Scope *parent;
} Scope;

typedef struct Signature {
  const DefDecl *def;
  Type **args, *result;
} Signature;

typedef struct Application {
  const Signature *signature;
  Type **args, *result;
  struct Application *next;
} Application;

typedef struct Check {
  const TlsfSpec *spec;
  Arena *arena;
  Signature *signatures;
  Application *applications;
  size_t revision;
  bool ok;
  bool resolved_widths;
} Check;

static Type *type_new(Check *c, unsigned mask) {
  if (!c->ok || arena_failed(c->arena))
    return nullptr;
  Type *t = ARENA_ALLOC(c->arena, Type);
  if (t)
    // §4.3: boolean expressions and signals can also be used as LTL. Keep
    // that embedding available in every independently instantiated call.
    // A boolean-only use still narrows this mask (and logical operands) in
    // need.
    t->mask = mask == T_BOOL || mask == T_SIGNAL ? mask | T_LTL : mask;
  else
    c->ok = false;
  return t;
}

static Type *root(Type *t) {
  while (t && t->link)
    t = t->link;
  return t;
}

static bool type_error(Check *c, const char *detail, const char *name) {
  fprintf(tlsf_diagnostic_stream(), "expand: typing: %s%s%s\n", detail,
          name ? ": " : "", name ? name : "");
  c->ok = false;
  return false;
}

static bool need(Check *c, Type *t, unsigned mask, const char *detail) {
  t = root(t);
  if (!c->ok || !t)
    return false;
  if (!(t->mask & mask))
    return type_error(c, detail, nullptr);
  if (t->mask != (t->mask & mask) && !t->instance)
    c->revision++;
  t->mask &= mask;
  if (t->mask == T_BOOL && !t->checking_boolean) {
    t->checking_boolean = true;
    if (t->logical_left && !need(c, t->logical_left, T_BOOL, detail))
      return false;
    if (t->logical_right && !need(c, t->logical_right, T_BOOL, detail))
      return false;
    t->checking_boolean = false;
  }
  return true;
}

// Once a copied constraint becomes part of a declaration/call, changes to it
// must participate in convergence. Logical dependencies may share/cycle.
static void retain(Type *t) {
  t = root(t);
  if (!t || !t->instance)
    return;
  t->instance = false;
  retain(t->element);
  retain(t->logical_left);
  retain(t->logical_right);
}

static bool unify(Check *c, Type *a, Type *b) {
  a = root(a);
  b = root(b);
  if (!c->ok || !a || !b)
    return false;
  if (a == b)
    return true;
  // Keep persistent roots stable when applying a fresh signature instance.
  if (a->instance && !b->instance) {
    Type *swap = a;
    a = b;
    b = swap;
  }
  unsigned mask = a->mask & b->mask;
  if (!mask)
    return type_error(c, "incompatible expression categories", nullptr);
  if (!a->instance &&
      (!b->instance || a->mask != mask || (!a->element && b->element) ||
       (!a->logical_left && !a->logical_right &&
        (b->logical_left || b->logical_right))))
    c->revision++;
  a->mask = mask;
  if (mask == T_BOOL && (!need(c, a, T_BOOL, "guard must be boolean") ||
                         !need(c, b, T_BOOL, "guard must be boolean")))
    return false;
  if (a->element && b->element && !unify(c, a->element, b->element))
    return false;
  if (!a->element)
    a->element = b->element;
  if (!a->logical_left && !a->logical_right) {
    a->logical_left = b->logical_left;
    a->logical_right = b->logical_right;
  }
  // Reject recursive set types, e.g. a function required to return both x
  // and {x}. All actual TLSF set types are finite (§4.3).
  for (Type *e = a->element; e; e = root(e)->element)
    if (root(e) == b || root(e) == a)
      return type_error(c, "recursive set type", nullptr);
  if (!a->instance) {
    retain(a->element);
    retain(a->logical_left);
    retain(a->logical_right);
  }
  b->link = a;
  return true;
}

static Type *element(Check *c, Type *set) {
  if (!need(c, set, T_SET, "expected a set"))
    return nullptr;
  set = root(set);
  if (!set->element)
    set->element = type_new(c, T_ANY);
  return set->element;
}

static Type *logical(Check *c, Type *a, Type *b) {
  a = root(a);
  b = root(b);
  if (!c->ok || !a)
    return nullptr;
  unsigned mask = !(a->mask & T_BOOL) || (b && !(b->mask & T_BOOL)) ? T_LTL
                  : a->mask == T_BOOL && (!b || b->mask == T_BOOL)
                      ? T_BOOL
                      : T_BOOL | T_LTL;
  Type *t = type_new(c, mask);
  if (t) {
    t->logical_left = a;
    t->logical_right = b;
  }
  return t;
}

// Boolean expressions and signals embed into LTL (§4.3). This join is for
// expression results (set elements/guard branches), not identifier rebinding.
static Type *join(Check *c, Type *a, Type *b) {
  a = root(a);
  b = root(b);
  if (!c->ok || !a || !b)
    return nullptr;
  if ((a->mask & ~T_FORMULA) == 0 && (b->mask & ~T_FORMULA) == 0)
    return logical(c, a, b);
  if (a->mask == T_SET && b->mask == T_SET) {
    Type *t = type_new(c, T_SET);
    Type *e = join(c, element(c, a), element(c, b));
    if (t)
      t->element = e;
    return t;
  }
  return unify(c, a, b) ? a : nullptr;
}

static const SignalDecl *signal(const TlsfSpec *s, const char *name) {
  for (uint32_t i = 0; i < s->input_count; i++)
    if (s->inputs[i].name == name)
      return &s->inputs[i];
  for (uint32_t i = 0; i < s->output_count; i++)
    if (s->outputs[i].name == name)
      return &s->outputs[i];
  return nullptr;
}

static bool declared(const TlsfSpec *s, const char *name) {
  if (signal(s, name) || spec_find_enum_label(s, name))
    return true;
  for (uint16_t i = 0; i < s->enum_type_count; i++)
    if (s->enum_types[i].name == name)
      return true;
  for (uint16_t i = 0; i < s->param_count; i++)
    if (s->params[i].name == name)
      return true;
  for (uint16_t i = 0; i < s->def_count; i++)
    if (s->defs[i].name == name)
      return true;
  return false;
}

static bool fresh(Check *c, const char *name) {
  return !declared(c->spec, name) ||
         type_error(c, "binding collides with a declared identifier", name);
}

static Type *local(const Scope *scope, const char *name) {
  for (; scope; scope = scope->parent)
    if (scope->name == name)
      return scope->type;
  return nullptr;
}

// Exact §4.4 value knowledge only: follow a nullary alias's lexical GLOBAL
// environment. Never derive widths from category unification, domains or a
// shadowed name. Computed/selected bus values are checked during expansion.
static const SignalDecl *static_bus(const Check *c, const Node *n,
                                    const Scope *scope, unsigned depth) {
  if (!n || n->kind != NODE_AP || local(scope, n->name) || depth > 2000)
    return nullptr;
  const SignalDecl *sig = signal(c->spec, n->name);
  if (sig)
    return sig->is_bus ? sig : nullptr;
  for (uint16_t i = 0; i < c->spec->def_count; i++) {
    const DefDecl *d = &c->spec->defs[i];
    if (d->name == n->name && !d->param_count)
      return static_bus(c, d->body, nullptr, depth + 1);
  }
  return nullptr;
}

static Type *infer(Check *, const Node *, const Scope *, unsigned);

// Calls constrain a fresh copy of the declaration's type graph. Never unify
// a recursive actual with the caller's formal: f(x) -> f({x}) need not imply
// type(x) = Set(type(x)). Result/argument sharing is preserved within a copy.
static Type *application(Check *c, const DefDecl *d, Type **args,
                         unsigned depth) {
  (void)depth;
  if (!c->ok)
    return nullptr;
  const Signature *signature = &c->signatures[d - c->spec->defs];
  if (!d->param_count)
    return signature->result;
  Application *call = ARENA_ALLOC(c->arena, Application);
  if (!call) {
    c->ok = false;
    return nullptr;
  }
  *call = (Application){signature, args, type_new(c, T_ANY), c->applications};
  c->applications = call;
  return call->result;
}

typedef struct TypeCopy {
  Type *source, *copy;
  struct TypeCopy *next;
} TypeCopy;

static Type *copy_type(Check *c, Type *source, TypeCopy **copies,
                       unsigned depth) {
  source = root(source);
  if (!source || !c->ok)
    return nullptr;
  if (depth > 2000) {
    type_error(c, "type inference recursion too deep", nullptr);
    return nullptr;
  }
  for (TypeCopy *copy = *copies; copy; copy = copy->next)
    if (copy->source == source)
      return copy->copy;
  TypeCopy *copy = ARENA_ALLOC(c->arena, TypeCopy);
  Type *t = type_new(c, source->mask);
  if (!copy || !t) {
    c->ok = false;
    return nullptr;
  }
  *copy = (TypeCopy){source, t, *copies};
  *copies = copy;
  t->instance = true;
  // type_new supplies embedding for literals; a scheme's narrowed mask must
  // be copied exactly (in particular a boolean-only guard constraint).
  t->mask = source->mask;
  t->element = copy_type(c, source->element, copies, depth + 1);
  t->logical_left = copy_type(c, source->logical_left, copies, depth + 1);
  t->logical_right = copy_type(c, source->logical_right, copies, depth + 1);
  return t;
}

static bool solve_applications(Check *c) {
  // Recursive schemes can acquire constraints through other calls/branches.
  // Reinstantiate until stable; match expansion's 2000-level termination
  // guard instead of assuming that arbitrary polymorphic recursion terminates.
  for (unsigned iteration = 0; iteration <= 2000 && c->ok; iteration++) {
    size_t before = c->revision;
    for (Application *call = c->applications; call && c->ok;
         call = call->next) {
      TypeCopy *copies = nullptr;
      const Signature *s = call->signature;
      // Copy the whole scheme before unifying: actuals may occur in a recursive
      // declaration's own graph, and must not affect this copy halfway through.
      Type **args = ARENA_ALLOC_N(c->arena, Type *, s->def->param_count);
      if (!args)
        return false;
      for (uint16_t i = 0; i < s->def->param_count; i++)
        args[i] = copy_type(c, s->args[i], &copies, 0);
      Type *result = copy_type(c, s->result, &copies, 0);
      for (uint16_t i = 0; i < s->def->param_count && c->ok; i++)
        unify(c, args[i], call->args[i]);
      unify(c, result, call->result);
    }
    if (before == c->revision)
      return c->ok;
  }
  return c->ok ? type_error(c, "type inference recursion too deep", nullptr)
               : false;
}

static Type *identifier(Check *c, const char *name, const Scope *scope,
                        unsigned depth) {
  Type *t = local(scope, name);
  if (t)
    return t;
  const TlsfSpec *s = c->spec;
  const SignalDecl *sig = signal(s, name);
  if (sig)
    return type_new(c, sig->is_bus ? T_BUS : T_SIGNAL);
  for (uint16_t i = 0; i < s->param_count; i++)
    if (s->params[i].name == name)
      return type_new(c, T_NUM);
  for (uint16_t i = 0; i < s->def_count; i++)
    if (s->defs[i].name == name && !s->defs[i].param_count)
      return application(c, &s->defs[i], nullptr, depth + 1);
  if (declared(s, name)) {
    type_error(c,
               "enum labels are only allowed in bus comparisons; "
               "types/functions are not values",
               name);
    return nullptr;
  }
  fprintf(tlsf_diagnostic_stream(),
          "expand: scoping: free identifier '%s' is not bound lexically\n",
          name);
  c->ok = false;
  return nullptr;
}

static bool pattern_scope(Check *c, const Node *n, const Scope **scope,
                          const Scope *outer) {
  if (!n || !c->ok)
    return false;
  if (n->kind == NODE_AP) {
    if (!strcmp(n->name, "_"))
      return true;
    if (!fresh(c, n->name))
      return false;
    if (local(outer, n->name))
      return type_error(c, "pattern identifier is not fresh", n->name);
    // Repeated pattern identifiers retain the existing syntactic match rule.
    if (local(*scope, n->name))
      return true;
    Scope *entry = ARENA_ALLOC(c->arena, Scope);
    if (!entry) {
      c->ok = false;
      return false;
    }
    *entry = (Scope){n->name, type_new(c, T_FORMULA), *scope};
    *scope = entry;
    return c->ok;
  }
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return pattern_scope(c, n->arg, scope, outer);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return pattern_scope(c, n->lhs, scope, outer) &&
           pattern_scope(c, n->rhs, scope, outer);
  default:
    return type_error(c, "invalid pattern or non-fresh pattern identifier",
                      nullptr);
  }
}

static Type *infer(Check *c, const Node *n, const Scope *scope,
                   unsigned depth) {
  if (!n || !c->ok)
    return nullptr;
  if (depth > 2000) {
    type_error(c, "type inference recursion too deep", nullptr);
    return nullptr;
  }
#define INFER(child) infer(c, n->child, scope, depth + 1)
#define REQUIRE(child, mask, message) need(c, INFER(child), mask, message)
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    return type_new(c, T_BOOL);
  case NODE_INT:
    return type_new(c, T_NUM);
  case NODE_AP:
  case NODE_INT_VAR:
    return identifier(c, n->name, scope, depth + 1);
  case NODE_SIZEOF:
    need(c, identifier(c, n->sizeof_name, scope, depth + 1), T_BUS,
         "SIZEOF requires a bus identifier");
    return type_new(c, T_NUM);
  case NODE_BUS_INDEX:
    need(c, identifier(c, n->bus_name, scope, depth + 1), T_BUS,
         "indexed identifier is not a bus");
    REQUIRE(bus_index, T_NUM, "bus index must be numeric");
    return type_new(c, T_SIGNAL);
  case NODE_DEF_CALL: {
    if (local(scope, n->callee)) {
      type_error(c, "local argument is not callable", n->callee);
      return nullptr;
    }
    const DefDecl *d = nullptr;
    for (uint16_t i = 0; i < c->spec->def_count; i++)
      if (c->spec->defs[i].name == n->callee &&
          c->spec->defs[i].param_count == n->call_argc)
        d = &c->spec->defs[i];
    if (!d) {
      type_error(c, "undefined function or wrong argument count", n->callee);
      return nullptr;
    }
    Type **args = ARENA_ALLOC_N(c->arena, Type *, n->call_argc);
    if (!args) {
      c->ok = false;
      return nullptr;
    }
    for (uint16_t i = 0; i < n->call_argc; i++)
      args[i] = infer(c, n->call_args[i], scope, depth + 1);
    return c->ok ? application(c, d, args, depth + 1) : nullptr;
  }
  case NODE_INT_NEG:
    REQUIRE(arg, T_NUM, "arithmetic requires numbers");
    return type_new(c, T_NUM);
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
    REQUIRE(lhs, T_NUM, "arithmetic requires numbers");
    REQUIRE(rhs, T_NUM, "arithmetic requires numbers");
    return type_new(c, T_NUM);
  case NODE_NOT: {
    Type *t = INFER(arg);
    need(c, t, T_FORMULA, "logical operator requires boolean/LTL expressions");
    return logical(c, t, nullptr);
  }
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    Type *a = INFER(lhs), *b = INFER(rhs);
    need(c, a, T_FORMULA, "logical operator requires boolean/LTL expressions");
    need(c, b, T_FORMULA, "logical operator requires boolean/LTL expressions");
    return logical(c, a, b);
  }
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    REQUIRE(arg, T_FORMULA, "temporal operator requires an LTL expression");
    return type_new(c, T_LTL);
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    REQUIRE(lhs, T_FORMULA, "temporal operator requires an LTL expression");
    REQUIRE(rhs, T_FORMULA, "temporal operator requires an LTL expression");
    return type_new(c, T_LTL);
  case NODE_CMP_EQ:
  case NODE_CMP_NE: {
    // §4.4: enum labels are not standalone expressions, only bus restrictions.
    const Node *bus = nullptr;
    const char *bits = nullptr;
    if (n->lhs->kind == NODE_AP && !local(scope, n->lhs->name) &&
        (bits = spec_find_enum_label(c->spec, n->lhs->name)))
      bus = n->rhs;
    if (!bus && n->rhs->kind == NODE_AP && !local(scope, n->rhs->name) &&
        (bits = spec_find_enum_label(c->spec, n->rhs->name)))
      bus = n->lhs;
    if (bus) {
      if (bus->kind != NODE_AP)
        type_error(c, "enum comparison requires a bus identifier", nullptr);
      else {
        Type *value = infer(c, bus, scope, depth + 1);
        if (need(c, value, T_BUS, "enum comparison requires a bus") &&
            c->resolved_widths) {
          // §4.4: direct declarations and lexical nullary alias chains are
          // exact even in unused definitions and unselected branches.
          // Type unification must not carry value widths across shadowing,
          // recursive actuals or set operations that may remove members.
          // Other comparisons check the actual bus during expansion.
          const SignalDecl *sig = static_bus(c, bus, scope, 0);
          if (sig &&
              (size_t)sig->bus_hi - sig->bus_lo + 1 != strcspn(bits, ","))
            type_error(c, "enum comparison width mismatch", bus->name);
        }
      }
      return type_new(c, T_LTL);
    }
    REQUIRE(lhs, T_NUM, "comparison requires numbers or a bus and enum label");
    REQUIRE(rhs, T_NUM, "comparison requires numbers or a bus and enum label");
    return type_new(c, T_BOOL);
  }
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE:
    REQUIRE(lhs, T_NUM, "ordered comparison requires numbers");
    REQUIRE(rhs, T_NUM, "ordered comparison requires numbers");
    return type_new(c, T_BOOL);
  case NODE_IN: {
    Type *a = INFER(lhs), *b = element(c, INFER(rhs));
    join(c, a, b);
    return type_new(c, T_BOOL);
  }
  case NODE_SET_SIZE:
    element(c, INFER(arg));
    return type_new(c, T_NUM);
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    need(c, element(c, INFER(arg)), T_NUM, "MIN/MAX require numeric sets");
    return type_new(c, T_NUM);
  case NODE_SET:
  case NODE_SET_ENUM: {
    Type *t = type_new(c, T_SET), *e = nullptr;
    for (uint16_t i = 0; i < n->set_size; i++) {
      Type *item = infer(c, n->set_elems[i], scope, depth + 1);
      e = e ? join(c, e, item) : item;
      if (n->kind == NODE_SET_ENUM)
        need(c, e, T_NUM, "set ranges require numbers");
    }
    if (t)
      t->element = e ? e : type_new(c, T_ANY);
    return t;
  }
  case NODE_SET_UNION:
  case NODE_SET_INTER:
  case NODE_SET_DIFF: {
    Type *a = INFER(lhs), *b = INFER(rhs);
    Type *e = join(c, element(c, a), element(c, b));
    Type *t = type_new(c, T_SET);
    if (t)
      t->element = e;
    return t;
  }
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER: {
    if (!fresh(c, n->qvar))
      return nullptr;
    Type *t;
    // §4.7: the domain is outside this binding. Parser nesting makes earlier
    // variables visible in later bound sets of the same big operator.
    if (n->qset)
      t = element(c, INFER(qset));
    else {
      REQUIRE(qlo, T_NUM, "numeric bound required");
      REQUIRE(qhi, T_NUM, "numeric bound required");
      t = type_new(c, T_NUM);
    }
    Scope child = {n->qvar, t, scope};
    Type *shadowed = local(scope, n->qvar);
    if (shadowed)
      unify(c, shadowed, t);
    Type *body = infer(c, n->qbody, &child, depth + 1);
    unsigned mask = n->kind == NODE_SUM || n->kind == NODE_PRODUCT ? T_NUM
                    : n->kind == NODE_FORALL || n->kind == NODE_EXISTS
                        ? T_FORMULA
                        : T_SET;
    need(c, body, mask, "big operator body has the wrong category");
    if (mask == T_FORMULA)
      return logical(c, body, nullptr);
    return body;
  }
  case NODE_NEXT_N:
    REQUIRE(lhs, T_NUM, "next count must be numeric");
    REQUIRE(rhs, T_FORMULA, "next body must be an LTL expression");
    return type_new(c, T_LTL);
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    REQUIRE(qlo, T_NUM, "temporal bound must be numeric");
    REQUIRE(qhi, T_NUM, "temporal bound must be numeric");
    REQUIRE(qbody, T_FORMULA, "temporal body must be an LTL expression");
    return type_new(c, T_LTL);
  case NODE_ITE: {
    const Scope *branch_scope = scope;
    if (n->if_cond->kind == NODE_MATCH) {
      need(c, infer(c, n->if_cond->lhs, scope, depth + 1), T_FORMULA,
           "pattern subject must be LTL");
      pattern_scope(c, n->if_cond->rhs, &branch_scope, scope);
    } else
      REQUIRE(if_cond, T_BOOL, "guard must be boolean (signals are LTL)");
    Type *a = infer(c, n->if_then, branch_scope, depth + 1);
    // tlsf.y encodes the end of a guard chain with a synthetic false node.
    // It is not a declared alternative whose type participates in §4.6's
    // same-type rule. Every actual guarded alternative is checked above.
    if (n->if_else->kind == NODE_FALSE)
      return a;
    Type *b = INFER(if_else);
    return join(c, a, b);
  }
  default:
    type_error(c, "invalid expression", nullptr);
    return nullptr;
  }
#undef INFER
#undef REQUIRE
}

// §4.5 signals must remain distinct after bus flattening in every printer and
// in core identity keys. Reject a declaration named <bus>_<index> rather than
// silently aliasing it to that bus bit. Bounds must already be resolved.
static bool signal_names(Check *c) {
  const SignalDecl *lists[] = {c->spec->inputs, c->spec->outputs};
  uint32_t counts[] = {c->spec->input_count, c->spec->output_count};
  for (unsigned k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++) {
      const char *name = lists[k][i].name;
      const char *suffix = strrchr(name, '_');
      if (!suffix || !suffix[1] || (suffix[1] == '0' && suffix[2]))
        continue;
      unsigned index = 0;
      const char *digit = suffix + 1;
      for (; *digit >= '0' && *digit <= '9'; digit++) {
        index = index * 10 + (unsigned)(*digit - '0');
        if (index > UINT16_MAX)
          break;
      }
      if (*digit)
        continue;
      for (unsigned b = 0; b < 2; b++)
        for (uint32_t j = 0; j < counts[b]; j++) {
          const SignalDecl *bus = &lists[b][j];
          if (bus->is_bus && strlen(bus->name) == (size_t)(suffix - name) &&
              !strncmp(bus->name, name, (size_t)(suffix - name)) &&
              index >= bus->bus_lo && index <= bus->bus_hi) {
            const char *flattened =
                expand_signal_name(c->spec, bus->name, index);
            if (!flattened)
              return false;
            if (flattened != name)
              continue;
            fprintf(tlsf_diagnostic_stream(),
                    "expand: typing: signal declaration '%s' collides with "
                    "flattened bus bit '%s[%u]'\n",
                    name, bus->name, index);
            c->ok = false;
            return false;
          }
        }
    }
  return true;
}

static bool check_spec_in_arena(const TlsfSpec *spec, bool resolved_widths,
                                Arena *arena) {
  Check c = {.spec = spec,
             .arena = arena,
             .ok = true,
             .resolved_widths = resolved_widths};
  if (resolved_widths && !signal_names(&c))
    return false;
  // Syntax and categories were checked before resolving bounds. Only enum
  // comparisons and flattened signal names depend on the resolved widths.
  if (resolved_widths && !spec->enum_label_count)
    return true;
  c.signatures = ARENA_ALLOC_N(arena, Signature, spec->def_count);
  if (!c.signatures)
    return false;
  // §4.3: an identifier has one category. Check the whole declaration space.
  Scope *names = nullptr;
  Type declaration_marker = {.mask = T_ANY};
#define DECLARE(name_)                                                         \
  do {                                                                         \
    const char *name = (name_);                                                \
    if (local(names, name))                                                    \
      return type_error(&c, "duplicate declaration", name);                    \
    Scope *entry = ARENA_ALLOC(arena, Scope);                                  \
    if (!entry)                                                                \
      return false;                                                            \
    *entry = (Scope){name, &declaration_marker, names};                        \
    names = entry;                                                             \
  } while (0)
  for (uint32_t i = 0; i < spec->input_count; i++)
    DECLARE(spec->inputs[i].name);
  for (uint32_t i = 0; i < spec->output_count; i++)
    DECLARE(spec->outputs[i].name);
  for (uint16_t i = 0; i < spec->param_count; i++)
    DECLARE(spec->params[i].name);
  for (uint16_t i = 0; i < spec->def_count; i++)
    DECLARE(spec->defs[i].name);
  for (uint16_t i = 0; i < spec->enum_label_count; i++)
    DECLARE(spec->enum_labels[i].name);
  for (uint16_t i = 0; i < spec->enum_type_count; i++)
    DECLARE(spec->enum_types[i].name);
#undef DECLARE
  for (uint16_t i = 0; i < spec->def_count && c.ok; i++) {
    const DefDecl *d = &spec->defs[i];
    Type **args = ARENA_ALLOC_N(arena, Type *, d->param_count);
    if (!args)
      return false;
    for (uint16_t j = 0; j < d->param_count; j++) {
      // §4.6 "fresh" is read lexically, compatibly with SYNTCOMP: arguments
      // may shadow any GLOBAL name; their category comes from the actual.
      for (uint16_t k = 0; k < j; k++)
        if (d->params[k] == d->params[j])
          return type_error(&c, "duplicate function argument", d->params[j]);
      args[j] = type_new(&c, T_ANY);
    }
    c.signatures[i] = (Signature){d, args, type_new(&c, T_ANY)};
  }
  for (uint16_t i = 0; i < spec->def_count && c.ok; i++) {
    const Signature *s = &c.signatures[i];
    Scope *scope = nullptr;
    for (uint16_t j = 0; j < s->def->param_count; j++) {
      Scope *entry = ARENA_ALLOC(arena, Scope);
      if (!entry)
        return false;
      *entry = (Scope){s->def->params[j], s->args[j], scope};
      scope = entry;
    }
    unify(&c, s->result, infer(&c, s->def->body, scope, 0));
  }
  const FormulaList *lists[] = {&spec->initially, &spec->preset,
                                &spec->require,   &spec->assert_,
                                &spec->assume,    &spec->guarantee};
  for (size_t k = 0; k < sizeof lists / sizeof *lists && c.ok; k++)
    for (uint32_t i = 0; i < lists[k]->count && c.ok; i++)
      need(&c, infer(&c, lists[k]->formulas[i], nullptr, 0), T_FORMULA,
           "specification requires an LTL expression");
  const SignalDecl *signals[] = {spec->inputs, spec->outputs};
  uint32_t counts[] = {spec->input_count, spec->output_count};
  for (unsigned k = 0; k < 2 && c.ok; k++)
    for (uint32_t i = 0; i < counts[k] && c.ok; i++) {
      if (signals[k][i].bus_lo_expr)
        need(&c, infer(&c, signals[k][i].bus_lo_expr, nullptr, 0), T_NUM,
             "bus bound must be numeric");
      if (signals[k][i].bus_hi_expr)
        need(&c, infer(&c, signals[k][i].bus_hi_expr, nullptr, 0), T_NUM,
             "bus bound must be numeric");
    }
  return c.ok && solve_applications(&c) && !arena_failed(arena);
}

// Type graphs and scope entries never escape a check. Release them before
// expansion rather than retaining both inference passes in the AST arena.
static bool check_spec(const TlsfSpec *spec, bool resolved_widths) {
  Arena *arena = arena_new(ARENA_DEFAULT_SLAB_SIZE);
  if (!arena) {
    arena_mark_failed(spec->arena);
    return false;
  }
  bool ok = check_spec_in_arena(spec, resolved_widths, arena);
  if (arena_failed(arena))
    arena_mark_failed(spec->arena);
  ok = ok && !arena_failed(spec->arena);
  arena_free(arena);
  return ok;
}

bool expand_check(const TlsfSpec *spec) { return check_spec(spec, false); }

bool expand_check_resolved(const TlsfSpec *spec) {
  return check_spec(spec, true);
}
