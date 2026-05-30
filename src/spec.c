#include "tlsf/spec.h"

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
                  .bus_lo_expr = lo_expr,
                  .bus_hi_expr = hi_expr};
  // Resolve literal bounds immediately so non-expanding consumers see them.
  if (lo_expr && lo_expr->kind == NODE_INT)
    d.bus_lo = (uint16_t)lo_expr->ival;
  if (hi_expr && hi_expr->kind == NODE_INT)
    d.bus_hi = (uint16_t)hi_expr->ival;
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
