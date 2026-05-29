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
    Node **new_arr =
        ARENA_ALLOC_N(s->arena, Node *, (size_t)new_cap);
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
