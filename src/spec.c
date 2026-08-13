#include "tlsf/spec.h"

#include "spec_internal.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FORMULA_LIST_INIT_CAP 8u

TlsfSpec *spec_new(void) {
  Arena *a = arena_new(ARENA_DEFAULT_SLAB_SIZE);
  if (!a)
    return nullptr;

  // Allocate the spec struct itself from the arena so teardown is one call.
  TlsfSpec *s = ARENA_ALLOC(a, TlsfSpec);
  if (!s) {
    arena_free(a);
    return nullptr;
  }
  s->arena = a;

  s->intern = intern_table_new(a);
  if (!s->intern) {
    arena_free(a);
    return nullptr;
  }

  return s;
}

void spec_free(TlsfSpec *s) {
  if (!s)
    return;
  intern_table_free(s->intern);
  // All formula nodes, strings, signal decls etc. live in s->arena.
  arena_free(s->arena);
}

static bool signal_name_in(const char *name, const SignalDecl *signals,
                           uint32_t count) {
  for (uint32_t i = 0; i < count; i++)
    if (signals[i].name == name)
      return true;
  return false;
}

static Node *wrap_signal_aps(Arena *arena, Node *node,
                             const SignalDecl *signals, uint32_t count) {
  switch (node->kind) {
  case NODE_AP:
    return signal_name_in(node->name, signals, count) ? node_x(arena, node)
                                                      : node;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    node->arg = wrap_signal_aps(arena, node->arg, signals, count);
    return node->arg ? node : nullptr;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    node->lhs = wrap_signal_aps(arena, node->lhs, signals, count);
    node->rhs = wrap_signal_aps(arena, node->rhs, signals, count);
    return node->lhs && node->rhs ? node : nullptr;
  default:
    return node;
  }
}

bool spec_adapt_target(TlsfSpec *s) {
  bool semantics_moore = semantics_is_moore(s->info.semantics);
  bool target_moore = s->info.target == TARGET_MOORE;
  if (semantics_moore == target_moore)
    return true;

  const SignalDecl *signals = semantics_moore ? s->inputs : s->outputs;
  uint32_t count = semantics_moore ? s->input_count : s->output_count;

#define WRAP_LIST(list)                                                        \
  do {                                                                         \
    for (uint32_t i = 0; i < (list).count; i++) {                              \
      (list).formulas[i] =                                                     \
          wrap_signal_aps(s->arena, (list).formulas[i], signals, count);       \
      if (!(list).formulas[i])                                                 \
        return false;                                                          \
    }                                                                          \
  } while (0)
  WRAP_LIST(s->initially);
  WRAP_LIST(s->require);
  WRAP_LIST(s->assume);
  WRAP_LIST(s->preset);
  WRAP_LIST(s->assert_);
  WRAP_LIST(s->guarantee);
#undef WRAP_LIST
  return true;
}

bool formula_list_push(TlsfSpec *s, FormulaList *list, Node *formula) {
  if (list->count == list->capacity) {
    uint32_t new_cap =
        list->capacity ? list->capacity * 2u : FORMULA_LIST_INIT_CAP;
    Node **new_arr = ARENA_ALLOC_N(s->arena, Node *, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (list->formulas)
      memcpy(new_arr, list->formulas, list->count * sizeof(Node *));
    list->formulas = new_arr;
    list->capacity = new_cap;
  }
  list->formulas[list->count++] = formula;
  return true;
}

static Node *fair_input_formula(TlsfSpec *spec, const SignalDecl *signal,
                                const char *index, bool negated) {
  Node *atom;
  if (signal->is_bus) {
    Node *index_node = ARENA_ALLOC(spec->arena, Node);
    atom = ARENA_ALLOC(spec->arena, Node);
    if (!index_node || !atom)
      return nullptr;
    index_node->kind = NODE_INT_VAR;
    index_node->name = index;
    atom->kind = NODE_BUS_INDEX;
    atom->bus_name = signal->name;
    atom->bus_index = index_node;
  } else {
    atom = node_ap(spec->arena, signal->name);
    if (!atom)
      return nullptr;
  }

  Node *value = negated ? node_not(spec->arena, atom) : atom;
  if (!value)
    return nullptr;
  Node *eventually = node_f(spec->arena, value);
  if (!eventually)
    return nullptr;
  Node *fair = node_g(spec->arena, eventually);
  if (!fair || !signal->is_bus)
    return fair;

  Node *lo = signal->bus_lo_expr;
  Node *hi = signal->bus_hi_expr;
  if (!lo)
    lo = node_int(spec->arena, signal->bus_lo);
  if (!hi)
    hi = node_int(spec->arena, signal->bus_hi);
  if (!lo || !hi)
    return nullptr;

  Node *quantified = ARENA_ALLOC(spec->arena, Node);
  if (!quantified)
    return nullptr;
  quantified->kind = NODE_FORALL;
  quantified->qvar = index;
  quantified->qlo = lo;
  quantified->qhi = hi;
  quantified->qbody = fair;
  return quantified;
}

bool spec_add_fair_environment(TlsfSpec *spec) {
  const char *index = nullptr;
  for (uint32_t i = 0; i < spec->input_count; i++) {
    const SignalDecl *signal = &spec->inputs[i];
    if (signal->is_bus && !index) {
      index = intern(spec->intern, "__tlsf_fair_i");
      if (!index)
        return false;
    }
    for (unsigned polarity = 0; polarity < 2; polarity++) {
      Node *fair = fair_input_formula(spec, signal, index, polarity != 0);
      if (!fair || !formula_list_push(spec, &spec->assume, fair))
        return false;
    }
  }
  return true;
}

#define LIST_INIT_CAP 8u

bool spec_add_signal(TlsfSpec *s, bool is_output, const char *name, bool is_bus,
                     Node *lo_expr, Node *hi_expr) {
  SignalDecl **list = is_output ? &s->outputs : &s->inputs;
  uint32_t *count = is_output ? &s->output_count : &s->input_count;
  uint32_t *cap = is_output ? &s->output_cap : &s->input_cap;

  if (*count == *cap) {
    uint32_t new_cap = *cap ? *cap * 2u : LIST_INIT_CAP;
    SignalDecl *new_arr = ARENA_ALLOC_N(s->arena, SignalDecl, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (*list)
      memcpy(new_arr, *list, *count * sizeof(SignalDecl));
    *list = new_arr;
    *cap = new_cap;
  }
  SignalDecl d = {.name = name,
                  .is_bus = is_bus,
                  .origin_name = name,
                  .origin_is_bus = is_bus,
                  .bus_lo_expr = lo_expr,
                  .bus_hi_expr = hi_expr};
  // Resolve literal bounds immediately so non-expanding consumers see them.
  if (lo_expr && lo_expr->kind == NODE_INT)
    d.bus_lo = (uint16_t)lo_expr->ival;
  if (hi_expr && hi_expr->kind == NODE_INT)
    d.bus_hi = (uint16_t)hi_expr->ival;
  d.origin_index = d.bus_lo;
  d.origin_bus_lo = d.bus_lo;
  d.origin_bus_hi = d.bus_hi;
  (*list)[*count] = d;
  (*count)++;
  return true;
}

bool spec_add_param(TlsfSpec *s, const char *name, bool has_default,
                    int64_t default_val) {
  if (s->param_count == s->param_cap) {
    uint16_t new_cap =
        s->param_cap ? (uint16_t)(s->param_cap * 2u) : (uint16_t)LIST_INIT_CAP;
    ParamDecl *new_arr = ARENA_ALLOC_N(s->arena, ParamDecl, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (s->params)
      memcpy(new_arr, s->params, s->param_count * sizeof(ParamDecl));
    s->params = new_arr;
    s->param_cap = new_cap;
  }
  s->params[s->param_count++] = (ParamDecl){.name = name,
                                            .value = default_val,
                                            .default_val = default_val,
                                            .has_default = has_default};
  return true;
}

bool spec_add_def(TlsfSpec *s, const char *name, const char **params,
                  uint16_t param_count, Node *body) {
  if (s->def_count == s->def_cap) {
    uint16_t new_cap =
        s->def_cap ? (uint16_t)(s->def_cap * 2u) : (uint16_t)LIST_INIT_CAP;
    DefDecl *new_arr = ARENA_ALLOC_N(s->arena, DefDecl, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (s->defs)
      memcpy(new_arr, s->defs, s->def_count * sizeof(DefDecl));
    s->defs = new_arr;
    s->def_cap = new_cap;
  }
  s->defs[s->def_count++] = (DefDecl){
      .name = name, .params = params, .param_count = param_count, .body = body};
  return true;
}

bool spec_add_enum_label(TlsfSpec *s, const char *name, const char *bits) {
  if (s->enum_label_count == s->enum_label_cap) {
    uint16_t new_cap = s->enum_label_cap ? (uint16_t)(s->enum_label_cap * 2u)
                                         : (uint16_t)LIST_INIT_CAP;
    EnumLabel *new_arr = ARENA_ALLOC_N(s->arena, EnumLabel, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (s->enum_labels)
      memcpy(new_arr, s->enum_labels, s->enum_label_count * sizeof(EnumLabel));
    s->enum_labels = new_arr;
    s->enum_label_cap = new_cap;
  }
  s->enum_labels[s->enum_label_count++] =
      (EnumLabel){.name = name, .bits = bits};
  return true;
}

const char *spec_find_enum_label(const TlsfSpec *s, const char *name) {
  for (uint16_t i = 0; i < s->enum_label_count; i++)
    if (s->enum_labels[i].name == name)
      return s->enum_labels[i].bits;
  return nullptr;
}

bool spec_add_enum_type(TlsfSpec *s, const char *name, uint32_t width,
                        uint16_t label_start, uint16_t label_count) {
  if (s->enum_type_count == s->enum_type_cap) {
    uint16_t new_cap = s->enum_type_cap ? (uint16_t)(s->enum_type_cap * 2u)
                                        : (uint16_t)LIST_INIT_CAP;
    EnumType *new_arr = ARENA_ALLOC_N(s->arena, EnumType, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (s->enum_types)
      memcpy(new_arr, s->enum_types, s->enum_type_count * sizeof(EnumType));
    s->enum_types = new_arr;
    s->enum_type_cap = new_cap;
  }
  s->enum_types[s->enum_type_count++] = (EnumType){.name = name,
                                                   .width = width,
                                                   .label_start = label_start,
                                                   .label_count = label_count};
  return true;
}

const EnumType *spec_find_enum_type(const TlsfSpec *s, const char *name) {
  for (uint16_t i = 0; i < s->enum_type_count; i++)
    if (s->enum_types[i].name == name)
      return &s->enum_types[i];
  return nullptr;
}

bool parse_semantics(const char *s, Semantics *out) {
  bool mealy = false, moore = false, strict = false, finite = false;
  char buf[64];
  size_t n = strlen(s);
  if (n >= sizeof buf)
    return false;
  memcpy(buf, s, n + 1);

  for (char *tok = strtok(buf, ","); tok; tok = strtok(nullptr, ",")) {
    while (*tok == ' ' || *tok == '\t')
      tok++;
    size_t len = strlen(tok);
    while (len > 0 && (tok[len - 1] == ' ' || tok[len - 1] == '\t'))
      tok[--len] = '\0';
    if (strcmp(tok, "Mealy") == 0)
      mealy = true;
    else if (strcmp(tok, "Moore") == 0)
      moore = true;
    else if (strcmp(tok, "Strict") == 0)
      strict = true;
    else if (strcmp(tok, "Finite") == 0)
      finite = true;
    else
      return false;
  }
  if (mealy == moore || (strict && finite))
    return false; // need exactly one base, at most one qualifier

  if (mealy)
    *out = strict ? SEM_MEALY_STRICT : finite ? SEM_MEALY_FINITE : SEM_MEALY;
  else
    *out = strict ? SEM_MOORE_STRICT : finite ? SEM_MOORE_FINITE : SEM_MOORE;
  return true;
}

bool parse_target(const char *s, Target *out) {
  if (strcmp(s, "Mealy") == 0) {
    *out = TARGET_MEALY;
    return true;
  }
  if (strcmp(s, "Moore") == 0) {
    *out = TARGET_MOORE;
    return true;
  }
  return false;
}

static bool node_has_strong_next(const Node *n) {
  if (!n)
    return false;
  switch (n->kind) {
  case NODE_X_STRONG:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    return node_has_strong_next(n->arg);
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
  case NODE_CMP_EQ:
  case NODE_CMP_NE:
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE:
  case NODE_NEXT_N:
  case NODE_SET_UNION:
  case NODE_SET_INTER:
  case NODE_SET_DIFF:
  case NODE_IN:
  case NODE_MATCH:
    return node_has_strong_next(n->lhs) || node_has_strong_next(n->rhs);
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    for (uint16_t i = 0; i < n->call_argc; i++)
      if (node_has_strong_next(n->call_args[i]))
        return true;
    return false;
  case NODE_BUS_INDEX:
    return node_has_strong_next(n->bus_index);
  case NODE_ITE:
    return node_has_strong_next(n->if_cond) ||
           node_has_strong_next(n->if_then) || node_has_strong_next(n->if_else);
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    return n->bounded.strong || node_has_strong_next(n->qlo) ||
           node_has_strong_next(n->qhi) || node_has_strong_next(n->qset) ||
           node_has_strong_next(n->qbody);
  case NODE_SET:
  case NODE_SET_ENUM:
    for (uint16_t i = 0; i < n->set_size; i++)
      if (node_has_strong_next(n->set_elems[i]))
        return true;
    return false;
  default:
    return false;
  }
}

static bool formula_list_has_strong_next(const FormulaList *list) {
  for (uint32_t i = 0; i < list->count; i++)
    if (node_has_strong_next(list->formulas[i]))
      return true;
  return false;
}

bool spec_validate_semantics(const TlsfSpec *s, const char *prog) {
  if (semantics_is_finite(s->info.semantics))
    return true;

  for (uint16_t i = 0; i < s->def_count; i++)
    if (node_has_strong_next(s->defs[i].body)) {
      fprintf(stderr, "%s: X[!] is only valid under finite semantics\n", prog);
      return false;
    }

  if (formula_list_has_strong_next(&s->initially) ||
      formula_list_has_strong_next(&s->require) ||
      formula_list_has_strong_next(&s->assume) ||
      formula_list_has_strong_next(&s->preset) ||
      formula_list_has_strong_next(&s->assert_) ||
      formula_list_has_strong_next(&s->guarantee)) {
    fprintf(stderr, "%s: X[!] is only valid under finite semantics\n", prog);
    return false;
  }

  return true;
}

static bool names_equal_ignoring_case(const char *lhs, const char *rhs) {
  while (*lhs && *rhs) {
    if (tolower((unsigned char)*lhs) != tolower((unsigned char)*rhs))
      return false;
    lhs++;
    rhs++;
  }
  return *lhs == *rhs;
}

bool spec_validate_lowercase_signals(const TlsfSpec *s, const char *prog) {
  const SignalDecl *lists[2] = {s->inputs, s->outputs};
  uint32_t counts[2] = {s->input_count, s->output_count};
  for (uint32_t left_list = 0; left_list < 2; left_list++)
    for (uint32_t left = 0; left < counts[left_list]; left++)
      for (uint32_t right_list = left_list; right_list < 2; right_list++) {
        uint32_t right_start = right_list == left_list ? left + 1 : 0;
        for (uint32_t right = right_start; right < counts[right_list];
             right++) {
          const char *lhs = lists[left_list][left].name;
          const char *rhs = lists[right_list][right].name;
          if (strcmp(lhs, rhs) != 0 && names_equal_ignoring_case(lhs, rhs)) {
            fprintf(stderr,
                    "%s: lowercasing would merge distinct signals '%s' and "
                    "'%s'\n",
                    prog, lhs, rhs);
            return false;
          }
        }
      }
  return true;
}

bool spec_add_tag(TlsfSpec *s, const char *tag) {
  if (s->info.tag_count == s->tag_cap) {
    uint16_t new_cap =
        s->tag_cap ? (uint16_t)(s->tag_cap * 2u) : (uint16_t)LIST_INIT_CAP;
    const char **new_arr =
        ARENA_ALLOC_N(s->arena, const char *, (size_t)new_cap);
    if (!new_arr)
      return false;
    if (s->info.tags)
      memcpy(new_arr, s->info.tags, s->info.tag_count * sizeof(const char *));
    s->info.tags = new_arr;
    s->tag_cap = new_cap;
  }
  s->info.tags[s->info.tag_count++] = tag;
  return true;
}
