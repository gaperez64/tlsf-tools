#define _GNU_SOURCE
#include "tlsf/obfuscate.h"
#include "tlsf/intern.h"
#include "tlsf/print_tlsf.h"
#include "tlsf/spec.h"

#include "diagnostic.h"

#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

// ===========================================================================
// Pointer maps: open addressing on pointer identity (interned names, nodes).
// ===========================================================================

typedef struct {
  const void **keys;
  uint32_t *values;
  size_t count, capacity; // capacity is zero or a power of two
} PtrMap;

static size_t ptr_hash(const void *p) {
  uint64_t x = (uint64_t)(uintptr_t)p;
  x ^= x >> 33;
  x *= 0xff51afd7ed558ccdu;
  x ^= x >> 33;
  return (size_t)x;
}

static void ptr_map_free(PtrMap *m) {
  free(m->keys);
  free(m->values);
  *m = (PtrMap){0};
}

static uint32_t *ptr_map_find(const PtrMap *m, const void *key) {
  if (m->capacity == 0)
    return nullptr;
  for (size_t i = ptr_hash(key) & (m->capacity - 1);;
       i = (i + 1) & (m->capacity - 1)) {
    if (!m->keys[i])
      return nullptr;
    if (m->keys[i] == key)
      return &m->values[i];
  }
}

static bool ptr_map_put(PtrMap *m, const void *key, uint32_t value) {
  assert(key);
  if (2 * (m->count + 1) > m->capacity) {
    size_t capacity = m->capacity ? 2 * m->capacity : 64;
    const void **keys = calloc(capacity, sizeof *keys);
    uint32_t *values = calloc(capacity, sizeof *values);
    if (!keys || !values) {
      free(keys);
      free(values);
      return false;
    }
    for (size_t i = 0; i < m->capacity; i++) {
      if (!m->keys[i])
        continue;
      size_t j = ptr_hash(m->keys[i]) & (capacity - 1);
      while (keys[j])
        j = (j + 1) & (capacity - 1);
      keys[j] = m->keys[i];
      values[j] = m->values[i];
    }
    free(m->keys);
    free(m->values);
    m->keys = keys;
    m->values = values;
    m->capacity = capacity;
  }
  size_t i = ptr_hash(key) & (m->capacity - 1);
  while (m->keys[i] && m->keys[i] != key)
    i = (i + 1) & (m->capacity - 1);
  if (!m->keys[i])
    m->count++;
  m->keys[i] = key;
  m->values[i] = value;
  return true;
}

// Mark `node` visited; false when it already was (or on OOM, see `failed`).
static bool first_visit(PtrMap *visited, const Node *node, bool *failed) {
  if (ptr_map_find(visited, node))
    return false;
  if (!ptr_map_put(visited, node, 1)) {
    *failed = true;
    return false;
  }
  return true;
}

// ===========================================================================
// Seeded randomness: splitmix64, one independent stream per purpose, so the
// names a seed gives do not depend on whether reordering also runs.
// ===========================================================================

typedef struct {
  uint64_t state;
} Rng;

static uint64_t rng_next(Rng *r) {
  uint64_t z = (r->state += 0x9e3779b97f4a7c15u);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9u;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebu;
  return z ^ (z >> 31);
}

static Rng rng_stream(uint64_t seed, uint64_t stream) {
  Rng r = {seed};
  r.state ^= rng_next(&(Rng){stream});
  return r;
}

static uint64_t rng_below(Rng *r, uint64_t n) {
  uint64_t limit = UINT64_MAX - UINT64_MAX % n;
  uint64_t x;
  do
    x = rng_next(r);
  while (x >= limit);
  return x % n;
}

static void shuffle(Rng *r, void *base, size_t count, size_t size) {
  unsigned char *bytes = base;
  for (size_t i = count; i > 1; i--) {
    unsigned char *a = bytes + (i - 1) * size;
    unsigned char *b = bytes + (size_t)rng_below(r, i) * size;
    for (size_t k = 0; a != b && k < size; k++) {
      unsigned char t = a[k];
      a[k] = b[k];
      b[k] = t;
    }
  }
}

enum {
  STREAM_NAMES = 1, // + kind
  STREAM_REORDER = STREAM_NAMES + TLSF_OBFUSCATE_FREE + 1,
};

// ===========================================================================
// Renaming: one bijection on spellings, applied to every identifier field.
// ===========================================================================

typedef struct {
  const char *original;
  TlsfObfuscateKind kind;
} NameUse;

typedef struct {
  TlsfSpec *spec;
  const char *wildcard; // `_`, a pattern wildcard; never renamed
  PtrMap slots;         // original name -> index into the arrays below
  const char **names;   // original spellings, first occurrence order
  const char **renamed;
  TlsfObfuscateKind *primary; // kind of the first occurrence; picks a letter
  unsigned *kinds;            // bit set of every kind seen
  uint32_t count, capacity;
  NameUse *uses; // (name, kind) pairs in discovery order
  uint32_t use_count, use_capacity;
  PtrMap visited;
  bool failed;
} Renamer;

static bool is_global_kind(TlsfObfuscateKind kind) {
  return kind <= TLSF_OBFUSCATE_DEFINITION;
}

static void note(Renamer *r, const char *name, TlsfObfuscateKind kind) {
  if (!name || name == r->wildcard || r->failed)
    return;
  uint32_t *slot = ptr_map_find(&r->slots, name);
  uint32_t index;
  if (slot) {
    index = *slot;
  } else {
    if (r->count == r->capacity) {
      uint32_t capacity = r->capacity ? 2 * r->capacity : 64;
      const char **names = realloc(r->names, capacity * sizeof *names);
      if (names)
        r->names = names;
      TlsfObfuscateKind *primary =
          realloc(r->primary, capacity * sizeof *primary);
      if (primary)
        r->primary = primary;
      unsigned *kinds = realloc(r->kinds, capacity * sizeof *kinds);
      if (kinds)
        r->kinds = kinds;
      if (!names || !primary || !kinds) {
        r->failed = true;
        return;
      }
      r->capacity = capacity;
    }
    index = r->count++;
    r->names[index] = name;
    r->primary[index] = kind;
    r->kinds[index] = 0;
    if (!ptr_map_put(&r->slots, name, index)) {
      r->failed = true;
      return;
    }
  }
  if (r->kinds[index] & (1u << kind))
    return;
  r->kinds[index] |= 1u << kind;
  if (r->use_count == r->use_capacity) {
    uint32_t capacity = r->use_capacity ? 2 * r->use_capacity : 64;
    NameUse *uses = realloc(r->uses, capacity * sizeof *uses);
    if (!uses) {
      r->failed = true;
      return;
    }
    r->uses = uses;
    r->use_capacity = capacity;
  }
  r->uses[r->use_count++] = (NameUse){name, kind};
}

typedef enum {
  COLLECT_BINDINGS, // declarations' binding sites: binders, pattern variables
  COLLECT_FREE,     // every identifier nothing declares
  APPLY,            // replace each spelling by its new one
} Phase;

static void rename_field(Renamer *r, const char **field) {
  if (!*field)
    return;
  uint32_t *slot = ptr_map_find(&r->slots, *field);
  if (slot)
    *field = r->renamed[*slot];
}

static void visit_name(Renamer *r, Phase phase, const char **field,
                       TlsfObfuscateKind kind) {
  switch (phase) {
  case COLLECT_BINDINGS:
    if (kind != TLSF_OBFUSCATE_FREE)
      note(r, *field, kind);
    return;
  case COLLECT_FREE:
    if (*field && !ptr_map_find(&r->slots, *field))
      note(r, *field, TLSF_OBFUSCATE_FREE);
    return;
  case APPLY:
    rename_field(r, field);
    return;
  }
}

// A pattern identifier binds unless it is a declared global name (which the
// expander rejects); arguments and binders may share its spelling.
static void visit_pattern_name(Renamer *r, Phase phase, const char **field) {
  if (phase != COLLECT_BINDINGS) {
    visit_name(r, phase, field, TLSF_OBFUSCATE_FREE);
    return;
  }
  if (!*field || *field == r->wildcard)
    return;
  uint32_t *slot = ptr_map_find(&r->slots, *field);
  for (unsigned k = 0; slot && k <= TLSF_OBFUSCATE_FREE; k++)
    if ((r->kinds[*slot] & (1u << k)) && is_global_kind(k))
      return;
  note(r, *field, TLSF_OBFUSCATE_PATTERN);
}

static void visit_node(Renamer *r, Phase phase, Node *n, bool in_pattern) {
  if (!n || r->failed || !first_visit(&r->visited, n, &r->failed))
    return;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
    return;
  case NODE_AP:
  case NODE_INT_VAR:
    if (in_pattern)
      visit_pattern_name(r, phase, &n->name);
    else
      visit_name(r, phase, &n->name, TLSF_OBFUSCATE_FREE);
    return;
  case NODE_SIZEOF:
    visit_name(r, phase, &n->sizeof_name, TLSF_OBFUSCATE_FREE);
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
    visit_node(r, phase, n->arg, in_pattern);
    return;
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    visit_name(r, phase, &n->callee, TLSF_OBFUSCATE_FREE);
    for (uint16_t i = 0; i < n->call_argc; i++)
      visit_node(r, phase, n->call_args[i], in_pattern);
    return;
  case NODE_BUS_INDEX:
    visit_name(r, phase, &n->bus_name, TLSF_OBFUSCATE_FREE);
    visit_node(r, phase, n->bus_index, in_pattern);
    return;
  case NODE_ITE:
    visit_node(r, phase, n->if_cond, in_pattern);
    visit_node(r, phase, n->if_then, in_pattern);
    visit_node(r, phase, n->if_else, in_pattern);
    return;
  case NODE_MATCH:
    visit_node(r, phase, n->lhs, in_pattern);
    visit_node(r, phase, n->rhs, true);
    return;
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    visit_node(r, phase, n->qlo, in_pattern);
    visit_node(r, phase, n->qhi, in_pattern);
    visit_node(r, phase, n->qbody, in_pattern);
    return;
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
    visit_name(r, phase, &n->qvar, TLSF_OBFUSCATE_BINDER);
    visit_node(r, phase, n->qlo, in_pattern);
    visit_node(r, phase, n->qhi, in_pattern);
    visit_node(r, phase, n->qset, in_pattern);
    visit_node(r, phase, n->qbody, in_pattern);
    return;
  case NODE_SET:
  case NODE_SET_ENUM:
    for (uint16_t i = 0; i < n->set_size; i++)
      visit_node(r, phase, n->set_elems[i], in_pattern);
    return;
  default:
    // Binary connectives, arithmetic, comparisons, set operators, IN, X[n].
    visit_node(r, phase, n->lhs, in_pattern);
    visit_node(r, phase, n->rhs, in_pattern);
    return;
  }
}

static FormulaList *section(TlsfSpec *s, unsigned k) {
  FormulaList *lists[] = {&s->initially, &s->preset, &s->require,
                          &s->assert_,   &s->assume, &s->guarantee};
  return lists[k];
}
enum { SECTION_COUNT = 6 };

static void visit_spec(Renamer *r, Phase phase) {
  TlsfSpec *s = r->spec;
  ptr_map_free(&r->visited);
  SignalDecl *signals[] = {s->inputs, s->outputs};
  uint32_t counts[] = {s->input_count, s->output_count};
  for (unsigned k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++) {
      SignalDecl *d = &signals[k][i];
      visit_node(r, phase, d->bus_lo_expr, false);
      visit_node(r, phase, d->bus_hi_expr, false);
      visit_node(r, phase, d->origin_width_expr, false);
    }
  for (uint16_t i = 0; i < s->def_count; i++)
    visit_node(r, phase, s->defs[i].body, false);
  for (unsigned k = 0; k < SECTION_COUNT; k++) {
    FormulaList *list = section(s, k);
    for (uint32_t i = 0; i < list->count; i++)
      visit_node(r, phase, list->formulas[i], false);
  }
}

static void collect_declarations(Renamer *r) {
  TlsfSpec *s = r->spec;
  for (uint32_t i = 0; i < s->input_count; i++)
    note(r, s->inputs[i].name, TLSF_OBFUSCATE_INPUT);
  for (uint32_t i = 0; i < s->output_count; i++)
    note(r, s->outputs[i].name, TLSF_OBFUSCATE_OUTPUT);
  for (uint16_t i = 0; i < s->param_count; i++)
    note(r, s->params[i].name, TLSF_OBFUSCATE_PARAMETER);
  for (uint16_t i = 0; i < s->enum_type_count; i++)
    note(r, s->enum_types[i].name, TLSF_OBFUSCATE_ENUM_TYPE);
  for (uint16_t i = 0; i < s->enum_label_count; i++)
    note(r, s->enum_labels[i].name, TLSF_OBFUSCATE_ENUM_LABEL);
  for (uint16_t i = 0; i < s->def_count; i++)
    note(r, s->defs[i].name, TLSF_OBFUSCATE_DEFINITION);
  for (uint16_t i = 0; i < s->def_count; i++)
    for (uint16_t j = 0; j < s->defs[i].param_count; j++)
      note(r, s->defs[i].params[j], TLSF_OBFUSCATE_ARGUMENT);
}

// Number each letter's names by a seeded permutation of first occurrence.
static bool assign_names(Renamer *r, uint64_t seed) {
  static const char letters[] = {
      [TLSF_OBFUSCATE_INPUT] = 'i',      [TLSF_OBFUSCATE_OUTPUT] = 'o',
      [TLSF_OBFUSCATE_PARAMETER] = 'p',  [TLSF_OBFUSCATE_ENUM_TYPE] = 't',
      [TLSF_OBFUSCATE_ENUM_LABEL] = 'e', [TLSF_OBFUSCATE_DEFINITION] = 'd',
      [TLSF_OBFUSCATE_ARGUMENT] = 'a',   [TLSF_OBFUSCATE_BINDER] = 'b',
      [TLSF_OBFUSCATE_PATTERN] = 'm',    [TLSF_OBFUSCATE_FREE] = 'f',
  };
  r->renamed = calloc(r->count ? r->count : 1, sizeof *r->renamed);
  uint32_t *members = malloc((r->count ? r->count : 1) * sizeof *members);
  uint32_t *numbers = malloc((r->count ? r->count : 1) * sizeof *numbers);
  if (!r->renamed || !members || !numbers) {
    free(members);
    free(numbers);
    return false;
  }
  for (unsigned kind = 0; kind <= TLSF_OBFUSCATE_FREE; kind++) {
    uint32_t n = 0;
    for (uint32_t i = 0; i < r->count; i++)
      if (r->primary[i] == kind)
        members[n++] = i;
    for (uint32_t i = 0; i < n; i++)
      numbers[i] = i;
    Rng rng = rng_stream(seed, STREAM_NAMES + kind);
    shuffle(&rng, numbers, n, sizeof *numbers);
    for (uint32_t i = 0; i < n; i++) {
      char name[16];
      snprintf(name, sizeof name, "%c%u", letters[kind], numbers[i]);
      r->renamed[members[i]] = intern(r->spec->intern, name);
      if (!r->renamed[members[i]]) {
        free(members);
        free(numbers);
        return false;
      }
    }
  }
  free(members);
  free(numbers);
  return true;
}

static void apply_renaming(Renamer *r) {
  TlsfSpec *s = r->spec;
  SignalDecl *signals[] = {s->inputs, s->outputs};
  uint32_t counts[] = {s->input_count, s->output_count};
  for (unsigned k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++) {
      rename_field(r, &signals[k][i].name);
      rename_field(r, &signals[k][i].origin_name);
      rename_field(r, &signals[k][i].enum_type);
    }
  for (uint16_t i = 0; i < s->param_count; i++)
    rename_field(r, &s->params[i].name);
  for (uint16_t i = 0; i < s->enum_type_count; i++)
    rename_field(r, &s->enum_types[i].name);
  for (uint16_t i = 0; i < s->enum_label_count; i++)
    rename_field(r, &s->enum_labels[i].name);
  for (uint16_t i = 0; i < s->def_count; i++) {
    rename_field(r, &s->defs[i].name);
    for (uint16_t j = 0; j < s->defs[i].param_count; j++)
      rename_field(r, (const char **)&s->defs[i].params[j]);
  }
  visit_spec(r, APPLY);
}

static void renamer_free(Renamer *r) {
  ptr_map_free(&r->slots);
  ptr_map_free(&r->visited);
  free(r->names);
  free(r->renamed);
  free(r->primary);
  free(r->kinds);
  free(r->uses);
}

static bool rename_spec(Renamer *r, uint64_t seed) {
  TlsfSpec *s = r->spec;
  r->wildcard = intern(s->intern, "_");
  if (!r->wildcard)
    return false;
  collect_declarations(r);
  visit_spec(r, COLLECT_BINDINGS);
  visit_spec(r, COLLECT_FREE);
  if (r->failed || !assign_names(r, seed))
    return false;
  apply_renaming(r);
  if (r->failed)
    return false;
  // Free text carries names, so only neutral text remains.
  s->info.title = intern(s->intern, "obfuscated");
  s->info.description = s->info.title;
  s->info.tag_count = 0;
  return s->info.title != nullptr;
}

// ===========================================================================
// Reordering
// ===========================================================================

static bool uses_match(const Node *n, PtrMap *visited, bool *failed) {
  if (!n || !first_visit(visited, n, failed))
    return false;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
  case NODE_AP:
  case NODE_INT_VAR:
  case NODE_SIZEOF:
    return false;
  case NODE_MATCH:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    return uses_match(n->arg, visited, failed);
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    for (uint16_t i = 0; i < n->call_argc; i++)
      if (uses_match(n->call_args[i], visited, failed))
        return true;
    return false;
  case NODE_BUS_INDEX:
    return uses_match(n->bus_index, visited, failed);
  case NODE_ITE:
    return uses_match(n->if_cond, visited, failed) ||
           uses_match(n->if_then, visited, failed) ||
           uses_match(n->if_else, visited, failed);
  case NODE_G_RANGE:
  case NODE_F_RANGE:
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
    return uses_match(n->qlo, visited, failed) ||
           uses_match(n->qhi, visited, failed) ||
           (n->kind != NODE_G_RANGE && n->kind != NODE_F_RANGE &&
            uses_match(n->qset, visited, failed)) ||
           uses_match(n->qbody, visited, failed);
  case NODE_SET:
  case NODE_SET_ENUM:
    for (uint16_t i = 0; i < n->set_size; i++)
      if (uses_match(n->set_elems[i], visited, failed))
        return true;
    return false;
  default:
    return uses_match(n->lhs, visited, failed) ||
           uses_match(n->rhs, visited, failed);
  }
}

// Swap `&&`/`||` operands in formula positions only. Pattern guards match on
// shape and formula-valued set elements are deduplicated by it, so stop at
// calls, sets, guards, comparisons and index or bound expressions.
static void swap_operands(Node *n, Rng *rng, PtrMap *visited, bool *failed) {
  if (!n || !first_visit(visited, n, failed))
    return;
  switch (n->kind) {
  case NODE_AND:
  case NODE_OR:
    if (rng_next(rng) & 1) {
      Node *lhs = n->lhs;
      n->lhs = n->rhs;
      n->rhs = lhs;
    }
    [[fallthrough]];
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    swap_operands(n->lhs, rng, visited, failed);
    swap_operands(n->rhs, rng, visited, failed);
    return;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    swap_operands(n->arg, rng, visited, failed);
    return;
  case NODE_NEXT_N:
    swap_operands(n->rhs, rng, visited, failed);
    return;
  case NODE_G_RANGE:
  case NODE_F_RANGE:
  case NODE_FORALL:
  case NODE_EXISTS:
    swap_operands(n->qbody, rng, visited, failed);
    return;
  default:
    return;
  }
}

static bool reorder_spec(TlsfSpec *s, uint64_t seed) {
  Rng rng = rng_stream(seed, STREAM_REORDER);
  shuffle(&rng, s->inputs, s->input_count, sizeof *s->inputs);
  shuffle(&rng, s->outputs, s->output_count, sizeof *s->outputs);
  shuffle(&rng, s->params, s->param_count, sizeof *s->params);
  shuffle(&rng, s->enum_types, s->enum_type_count, sizeof *s->enum_types);
  shuffle(&rng, s->defs, s->def_count, sizeof *s->defs);
  for (unsigned k = 0; k < SECTION_COUNT; k++) {
    FormulaList *list = section(s, k);
    shuffle(&rng, list->formulas, list->count, sizeof *list->formulas);
  }

  bool failed = false, matching = false;
  PtrMap visited = {0};
  for (uint16_t i = 0; i < s->def_count && !matching; i++)
    matching = uses_match(s->defs[i].body, &visited, &failed);
  for (unsigned k = 0; k < SECTION_COUNT && !matching; k++) {
    FormulaList *list = section(s, k);
    for (uint32_t i = 0; i < list->count && !matching; i++)
      matching = uses_match(list->formulas[i], &visited, &failed);
  }
  ptr_map_free(&visited);
  if (!matching)
    for (unsigned k = 0; k < SECTION_COUNT; k++) {
      FormulaList *list = section(s, k);
      for (uint32_t i = 0; i < list->count; i++)
        swap_operands(list->formulas[i], &rng, &visited, &failed);
    }
  ptr_map_free(&visited);
  return !failed;
}

// Test faults the self-check must reject: 1 exchanges the first input and
// output declarations, 2 negates the first formula of the first section, 3
// flips TARGET, 5 renames the first definition but not its calls. Fault 4
// truncates the printed text (see obfuscate()).
static bool inject_fault(TlsfSpec *s, unsigned fault) {
  if (fault == 3)
    s->info.target =
        s->info.target == TARGET_MEALY ? TARGET_MOORE : TARGET_MEALY;
  if (fault == 5 && s->def_count > 0) {
    s->defs[0].name = intern(s->intern, "fault");
    return s->defs[0].name != nullptr;
  }
  if (fault == 1 && s->input_count > 0 && s->output_count > 0) {
    SignalDecl input = s->inputs[0];
    s->inputs[0] = s->outputs[0];
    s->outputs[0] = input;
  }
  for (unsigned k = 0; fault == 2 && k < SECTION_COUNT; k++) {
    FormulaList *list = section(s, k);
    if (list->count == 0)
      continue;
    list->formulas[0] = node_not(s->arena, list->formulas[0]);
    return list->formulas[0] != nullptr;
  }
  return true;
}

// ===========================================================================
// Self-check: compare expansions up to renaming and AC of && / ||.
// ===========================================================================

typedef struct {
  NodeKind kind;
  bool resolved;
  const char *name; // canonical (checker-interned) spelling, AP only
  int64_t ival;
  BoundedTemporalOrigin origin;
  bool strong;
  int64_t lo, hi;
  uint32_t body; // canonical id of the bounded body, or UINT32_MAX
  uint32_t first_child, child_count;
  uint64_t hash;
} CanonKey;

typedef struct {
  Arena *arena;
  InternTable *intern;
  CanonKey *keys;
  uint32_t key_count, key_capacity;
  uint32_t *children;
  size_t child_count, child_capacity;
  uint32_t *table; // key index + 1; zero is empty
  size_t table_capacity;
  bool failed;
  char message[256];
} Canon;

typedef struct {
  Canon *canon;
  PtrMap memo;  // node -> canonical id
  PtrMap names; // spec-interned AP name -> index into `spellings`
  const char **spellings;
  uint32_t spelling_count, spelling_capacity;
  // Translates a spec name into the shared spelling (identity when null).
  const char *(*translate)(void *ctx, const char *name);
  void *ctx;
} CanonSide;

static void canon_fail(Canon *c, const char *fmt, ...) {
  if (c->failed)
    return;
  c->failed = true;
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(c->message, sizeof c->message, fmt, ap);
  va_end(ap);
}

static uint64_t mix(uint64_t h, uint64_t x) {
  h ^= x + 0x9e3779b97f4a7c15u + (h << 6) + (h >> 2);
  return h * 0x100000001b3u;
}

static uint64_t key_hash(const CanonKey *k, const uint32_t *children) {
  uint64_t h = mix(0xcbf29ce484222325u, (uint64_t)k->kind);
  h = mix(h, k->resolved);
  h = mix(h, (uint64_t)(uintptr_t)k->name);
  h = mix(h, (uint64_t)k->ival);
  h = mix(h, (uint64_t)k->origin);
  h = mix(h, k->strong);
  h = mix(h, (uint64_t)k->lo);
  h = mix(h, (uint64_t)k->hi);
  h = mix(h, k->body);
  for (uint32_t i = 0; i < k->child_count; i++)
    h = mix(h, children[i]);
  return h;
}

static bool key_equal(const Canon *c, const CanonKey *a, const CanonKey *b,
                      const uint32_t *b_children) {
  return a->hash == b->hash && a->kind == b->kind &&
         a->resolved == b->resolved && a->name == b->name &&
         a->ival == b->ival && a->origin == b->origin &&
         a->strong == b->strong && a->lo == b->lo && a->hi == b->hi &&
         a->body == b->body && a->child_count == b->child_count &&
         memcmp(c->children + a->first_child, b_children,
                a->child_count * sizeof *b_children) == 0;
}

static bool canon_grow_table(Canon *c) {
  size_t capacity = c->table_capacity ? 2 * c->table_capacity : 1024;
  uint32_t *table = calloc(capacity, sizeof *table);
  if (!table)
    return false;
  for (uint32_t i = 0; i < c->key_count; i++) {
    size_t j = (size_t)c->keys[i].hash & (capacity - 1);
    while (table[j])
      j = (j + 1) & (capacity - 1);
    table[j] = i + 1;
  }
  free(c->table);
  c->table = table;
  c->table_capacity = capacity;
  return true;
}

// Intern a key; `children` is a scratch array owned by the caller.
static uint32_t canon_intern(Canon *c, CanonKey key, const uint32_t *children) {
  key.hash = key_hash(&key, children);
  if (2 * ((size_t)c->key_count + 1) > c->table_capacity &&
      !canon_grow_table(c)) {
    canon_fail(c, "out of memory");
    return 0;
  }
  size_t j = (size_t)key.hash & (c->table_capacity - 1);
  for (; c->table[j]; j = (j + 1) & (c->table_capacity - 1))
    if (key_equal(c, &c->keys[c->table[j] - 1], &key, children))
      return c->table[j] - 1;
  if (c->key_count == c->key_capacity) {
    uint32_t capacity = c->key_capacity ? 2 * c->key_capacity : 1024;
    CanonKey *keys = realloc(c->keys, capacity * sizeof *keys);
    if (!keys) {
      canon_fail(c, "out of memory");
      return 0;
    }
    c->keys = keys;
    c->key_capacity = capacity;
  }
  if (c->child_count + key.child_count > c->child_capacity) {
    size_t capacity = c->child_capacity ? 2 * c->child_capacity : 4096;
    while (capacity < c->child_count + key.child_count)
      capacity *= 2;
    uint32_t *grown = realloc(c->children, capacity * sizeof *grown);
    if (!grown) {
      canon_fail(c, "out of memory");
      return 0;
    }
    c->children = grown;
    c->child_capacity = capacity;
  }
  key.first_child = (uint32_t)c->child_count;
  memcpy(c->children + c->child_count, children,
         key.child_count * sizeof *children);
  c->child_count += key.child_count;
  c->keys[c->key_count] = key;
  c->table[j] = c->key_count + 1;
  return c->key_count++;
}

static const char *side_spelling(CanonSide *side, const char *name) {
  uint32_t *slot = ptr_map_find(&side->names, name);
  if (slot)
    return side->spellings[*slot];
  const char *translated =
      side->translate ? side->translate(side->ctx, name) : name;
  const char *spelling =
      translated ? intern(side->canon->intern, translated) : nullptr;
  if (!spelling) {
    canon_fail(side->canon, "out of memory");
    return nullptr;
  }
  if (side->spelling_count == side->spelling_capacity) {
    uint32_t capacity =
        side->spelling_capacity ? 2 * side->spelling_capacity : 256;
    const char **grown =
        realloc(side->spellings, capacity * sizeof *side->spellings);
    if (!grown) {
      canon_fail(side->canon, "out of memory");
      return nullptr;
    }
    side->spellings = grown;
    side->spelling_capacity = capacity;
  }
  side->spellings[side->spelling_count] = spelling;
  if (!ptr_map_put(&side->names, name, side->spelling_count)) {
    canon_fail(side->canon, "out of memory");
    return nullptr;
  }
  side->spelling_count++;
  return spelling;
}

typedef struct {
  uint32_t *items;
  size_t count, capacity;
} IdVec;

static bool id_push(IdVec *v, uint32_t id) {
  if (v->count == v->capacity) {
    size_t capacity = v->capacity ? 2 * v->capacity : 16;
    uint32_t *grown = realloc(v->items, capacity * sizeof *grown);
    if (!grown)
      return false;
    v->items = grown;
    v->capacity = capacity;
  }
  v->items[v->count++] = id;
  return true;
}

static int id_compare(const void *a, const void *b) {
  uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
  return (x > y) - (x < y);
}

static uint32_t canon_node(CanonSide *side, const Node *n);

// Operands of a maximal &&/|| chain: descend through children of the same
// kind unless bounded-temporal metadata makes them observable on their own.
static bool flatten(CanonSide *side, const Node *n, IdVec *out) {
  const Node **stack = nullptr;
  size_t depth = 0, capacity = 0;
  bool ok = true;
  const Node *operands[2] = {n->lhs, n->rhs};
  for (int i = 1; i >= 0 && ok; i--) {
    if (depth == capacity) {
      capacity = capacity ? 2 * capacity : 16;
      const Node **grown = realloc(stack, capacity * sizeof *grown);
      if (!grown) {
        ok = false;
        break;
      }
      stack = grown;
    }
    stack[depth++] = operands[i];
  }
  while (ok && depth > 0) {
    const Node *m = stack[--depth];
    if (m->kind == n->kind && m->bounded.origin == BOUNDED_NONE) {
      if (depth + 2 > capacity) {
        capacity = 2 * capacity + 2;
        const Node **grown = realloc(stack, capacity * sizeof *grown);
        if (!grown) {
          ok = false;
          break;
        }
        stack = grown;
      }
      stack[depth++] = m->rhs;
      stack[depth++] = m->lhs;
      continue;
    }
    uint32_t id = canon_node(side, m);
    if (side->canon->failed || !id_push(out, id))
      ok = false;
  }
  free(stack);
  if (!ok)
    canon_fail(side->canon, "out of memory");
  return ok && !side->canon->failed;
}

static uint32_t canon_node(CanonSide *side, const Node *n) {
  Canon *c = side->canon;
  if (c->failed)
    return 0;
  uint32_t *memo = ptr_map_find(&side->memo, n);
  if (memo)
    return *memo;
  CanonKey key = {.kind = n->kind,
                  .resolved = n->resolved_signal,
                  .origin = n->bounded.origin,
                  .body = UINT32_MAX};
  if (n->bounded.origin != BOUNDED_NONE) {
    key.strong = n->bounded.strong;
    key.lo = n->bounded.lo;
    key.hi = n->bounded.hi;
    if (n->bounded.body)
      key.body = canon_node(side, n->bounded.body);
  }
  uint32_t pair[2];
  IdVec operands = {0};
  const uint32_t *children = pair;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    break;
  case NODE_AP:
    key.name = side_spelling(side, n->name);
    break;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    pair[0] = canon_node(side, n->arg);
    key.child_count = 1;
    break;
  case NODE_AND:
  case NODE_OR:
    if (!flatten(side, n, &operands))
      break;
    qsort(operands.items, operands.count, sizeof *operands.items, id_compare);
    children = operands.items;
    key.child_count = (uint32_t)operands.count;
    break;
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    pair[0] = canon_node(side, n->lhs);
    pair[1] = canon_node(side, n->rhs);
    key.child_count = 2;
    break;
  default:
    canon_fail(c, "unexpected node kind %d after expansion", (int)n->kind);
    break;
  }
  uint32_t id = c->failed ? 0 : canon_intern(c, key, children);
  free(operands.items);
  if (!c->failed && !ptr_map_put(&side->memo, n, id))
    canon_fail(c, "out of memory");
  return id;
}

static bool section_ids(CanonSide *side, const FormulaList *list, IdVec *out) {
  for (uint32_t i = 0; i < list->count; i++) {
    uint32_t id = canon_node(side, list->formulas[i]);
    if (side->canon->failed)
      return false;
    if (!id_push(out, id)) {
      canon_fail(side->canon, "out of memory");
      return false;
    }
  }
  qsort(out->items, out->count, sizeof *out->items, id_compare);
  return true;
}

// The reference side's translation into obfuscated spellings: expanded
// signals by their source declaration, every other atom by the renaming.
typedef struct {
  Renamer *renamer; // null when names are unchanged
  PtrMap signals;   // expanded reference signal name -> index in `expected`
  char **expected;
  uint32_t expected_count;
} Translation;

static const char *renamed_spelling(Renamer *r, const char *name) {
  if (!r)
    return name;
  const char *own = intern(r->spec->intern, name);
  if (!own)
    return nullptr;
  uint32_t *slot = ptr_map_find(&r->slots, own);
  return slot ? r->renamed[*slot] : name;
}

static const char *translate_reference(void *ctx, const char *name) {
  Translation *t = ctx;
  uint32_t *slot = ptr_map_find(&t->signals, name);
  if (slot)
    return t->expected[*slot];
  return renamed_spelling(t->renamer, name);
}

static void translation_free(Translation *t) {
  for (uint32_t i = 0; i < t->expected_count; i++)
    free(t->expected[i]);
  free(t->expected);
  ptr_map_free(&t->signals);
}

static bool translate_signals(Translation *t, const TlsfSpec *ref) {
  uint32_t total = ref->input_count + ref->output_count;
  t->expected = calloc(total ? total : 1, sizeof *t->expected);
  if (!t->expected)
    return false;
  const SignalDecl *signals[] = {ref->inputs, ref->outputs};
  uint32_t counts[] = {ref->input_count, ref->output_count};
  for (unsigned k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++) {
      const SignalDecl *d = &signals[k][i];
      const char *base = renamed_spelling(
          t->renamer, d->origin_name ? d->origin_name : d->name);
      if (!base)
        return false;
      char *spelling = nullptr;
      int length = d->origin_is_bus
                       ? asprintf(&spelling, "%s_%u", base, d->origin_index)
                       : asprintf(&spelling, "%s", base);
      if (length < 0)
        return false;
      t->expected[t->expected_count] = spelling;
      if (!ptr_map_put(&t->signals, d->name, t->expected_count++))
        return false;
    }
  return true;
}

typedef struct {
  TlsfObfuscateStatus status;
  char message[256];
} CheckOutcome;

static void check_fail(CheckOutcome *o, TlsfObfuscateStatus status,
                       const char *fmt, ...) {
  if (o->status != TLSF_OBFUSCATE_OK)
    return;
  o->status = status;
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(o->message, sizeof o->message, fmt, ap);
  va_end(ap);
}

// The obfuscated expansion must declare exactly the translated signals on
// the same side, and the translation must be injective.
static void compare_signals(CheckOutcome *o, CanonSide *ref, CanonSide *obf,
                            const TlsfSpec *r, const TlsfSpec *b) {
  if (r->input_count != b->input_count || r->output_count != b->output_count) {
    check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED,
               "signal counts differ (%u/%u inputs, %u/%u outputs)",
               r->input_count, b->input_count, r->output_count,
               b->output_count);
    return;
  }
  PtrMap sides = {0}; // canonical spelling -> 1 input, 2 output
  bool failed = false;
  for (uint32_t i = 0; i < b->input_count && !failed; i++)
    failed = !ptr_map_put(&sides, side_spelling(obf, b->inputs[i].name), 1);
  for (uint32_t i = 0; i < b->output_count && !failed; i++)
    failed = !ptr_map_put(&sides, side_spelling(obf, b->outputs[i].name), 2);
  if (failed || ref->canon->failed) {
    ptr_map_free(&sides);
    check_fail(o, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
    return;
  }
  if (sides.count != (size_t)b->input_count + b->output_count)
    check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED,
               "output declares a signal twice");
  const SignalDecl *signals[] = {r->inputs, r->outputs};
  uint32_t counts[] = {r->input_count, r->output_count};
  for (unsigned k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++) {
      const char *name = signals[k][i].name;
      uint32_t *side = ptr_map_find(&sides, side_spelling(ref, name));
      if (!side || *side != k + 1)
        check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED,
                   "%s '%s' is not an %s of the output", k ? "output" : "input",
                   name, k ? "output" : "input");
    }
  ptr_map_free(&sides);
}

static void check_injective(CheckOutcome *o, CanonSide *ref) {
  PtrMap seen = {0};
  for (uint32_t i = 0; i < ref->spelling_count; i++) {
    if (ptr_map_find(&seen, ref->spellings[i])) {
      check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED,
                 "renaming merges two atoms into '%s'", ref->spellings[i]);
      break;
    }
    if (!ptr_map_put(&seen, ref->spellings[i], 1)) {
      check_fail(o, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
      break;
    }
  }
  ptr_map_free(&seen);
}

static void compare_expansions(CheckOutcome *o, Renamer *renamer,
                               const TlsfSpec *r, const TlsfSpec *b) {
  if (r->info.semantics != b->info.semantics ||
      r->info.target != b->info.target) {
    check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED, "SEMANTICS or TARGET changed");
    return;
  }
  Canon canon = {0};
  Translation translation = {.renamer = renamer};
  canon.arena = arena_new(ARENA_DEFAULT_SLAB_SIZE / 16);
  canon.intern = canon.arena ? intern_table_new(canon.arena) : nullptr;
  CanonSide ref = {
      .canon = &canon, .translate = translate_reference, .ctx = &translation};
  CanonSide obf = {.canon = &canon};
  if (!canon.intern || !translate_signals(&translation, r)) {
    check_fail(o, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
    goto done;
  }
  compare_signals(o, &ref, &obf, r, b);
  static const char *names[] = {"INITIALLY", "PRESET", "REQUIRE",
                                "ASSERT",    "ASSUME", "GUARANTEE"};
  for (unsigned k = 0; k < SECTION_COUNT && o->status == TLSF_OBFUSCATE_OK;
       k++) {
    IdVec x = {0}, y = {0};
    bool ok = section_ids(&ref, section((TlsfSpec *)r, k), &x) &&
              section_ids(&obf, section((TlsfSpec *)b, k), &y);
    if (!ok)
      check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED, "%s: %s", names[k],
                 canon.message);
    else if (x.count != y.count ||
             memcmp(x.items, y.items, x.count * sizeof *x.items) != 0)
      check_fail(o, TLSF_OBFUSCATE_CHECK_FAILED,
                 "%s formulas differ after expansion", names[k]);
    free(x.items);
    free(y.items);
  }
  if (o->status == TLSF_OBFUSCATE_OK)
    check_injective(o, &ref);
done:
  ptr_map_free(&ref.memo);
  ptr_map_free(&ref.names);
  free(ref.spellings);
  ptr_map_free(&obf.memo);
  ptr_map_free(&obf.names);
  free(obf.spellings);
  translation_free(&translation);
  free(canon.keys);
  free(canon.children);
  free(canon.table);
  intern_table_free(canon.intern);
  arena_free(canon.arena);
}

// ===========================================================================
// Result
// ===========================================================================

static const char *store(Arena *a, const char *s) {
  size_t n = strlen(s) + 1;
  char *copy = ARENA_ALLOC_N(a, char, n);
  if (copy)
    memcpy(copy, s, n);
  return copy;
}

static bool record_map(TlsfObfuscateResult *result, Renamer *r,
                       const TlsfSpec *expanded_ref) {
  Arena *arena = arena_new(ARENA_DEFAULT_SLAB_SIZE / 16);
  if (!arena)
    return false;
  result->storage = arena;
  size_t total = r->use_count + (size_t)expanded_ref->input_count +
                 expanded_ref->output_count;
  result->entries = ARENA_ALLOC_N(arena, TlsfObfuscateEntry, total ? total : 1);
  if (!result->entries)
    return false;
  size_t n = 0;
  for (uint32_t i = 0; i < r->use_count; i++) {
    uint32_t *slot = ptr_map_find(&r->slots, r->uses[i].original);
    result->entries[n++] =
        (TlsfObfuscateEntry){store(arena, r->uses[i].original),
                             store(arena, r->renamed[*slot]), r->uses[i].kind};
  }
  // Expanded signals, named as the self-check verified them.
  Translation t = {.renamer = r};
  bool ok = translate_signals(&t, expanded_ref);
  for (uint32_t i = 0; ok && i < t.expected_count; i++) {
    bool input = i < expanded_ref->input_count;
    const SignalDecl *d =
        input ? &expanded_ref->inputs[i]
              : &expanded_ref->outputs[i - expanded_ref->input_count];
    result->entries[n++] = (TlsfObfuscateEntry){
        store(arena, d->name), store(arena, t.expected[i]),
        input ? TLSF_OBFUSCATE_INPUT_SIGNAL : TLSF_OBFUSCATE_OUTPUT_SIGNAL};
  }
  translation_free(&t);
  result->entry_count = n;
  for (size_t i = 0; ok && i < n; i++)
    ok = result->entries[i].original && result->entries[i].obfuscated;
  return ok && !arena_failed(arena);
}

// ===========================================================================
// Entry point
// ===========================================================================

static TlsfSpec *parse_bytes(const char *bytes, size_t size, const char *prog) {
  FILE *in = fmemopen((void *)bytes, size, "r");
  if (!in)
    return nullptr;
  TlsfSpec *spec = spec_parse(in, prog);
  fclose(in);
  return spec;
}

static TlsfObfuscateStatus fail(TlsfObfuscateResult *result,
                                TlsfObfuscateStatus status, const char *fmt,
                                ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(result->message, sizeof result->message, fmt, ap);
  va_end(ap);
  return status;
}

// The first line the parser or expander wrote, for the result's message.
static const char *first_line(const char *text, char *buffer, size_t size) {
  if (!text || !*text)
    return "";
  size_t n = strcspn(text, "\n");
  if (n >= size)
    n = size - 1;
  memcpy(buffer, text, n);
  buffer[n] = '\0';
  return buffer;
}

typedef struct {
  TlsfSpec *work, *reference, *output;
  ParamOverride *overrides;
  char *diagnostics;
  size_t diagnostics_size;
  FILE *capture, *previous;
  Renamer renamer;
} Job;

static TlsfObfuscateStatus obfuscate(Job *job, const char *source, size_t size,
                                     const TlsfObfuscateOptions *o,
                                     TlsfObfuscateResult *result) {
  char line[200];
  if (!source || !o || o->mode == 0 ||
      (o->mode & ~(unsigned)TLSF_OBFUSCATE_ALL) ||
      (o->n_overrides && !o->overrides))
    return fail(result, TLSF_OBFUSCATE_INVALID, "invalid options");
  if (!size || memchr(source, '\0', size))
    return fail(result, TLSF_OBFUSCATE_INVALID, "input is empty or binary");

  job->work = parse_bytes(source, size, "input");
  job->reference = job->work ? parse_bytes(source, size, "input") : nullptr;
  if (!job->work || !job->reference) {
    fflush(job->capture);
    return fail(result, TLSF_OBFUSCATE_INVALID, "input does not parse: %s",
                first_line(job->diagnostics, line, sizeof line));
  }
  TlsfSpec *w = job->work;

  // Overrides, last one winning as in tlsf2tlsf, become parameter values.
  size_t n_effective = 0;
  job->overrides =
      malloc((o->n_overrides ? o->n_overrides : 1) * sizeof *job->overrides);
  if (!job->overrides)
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  for (size_t i = 0; i < o->n_overrides; i++) {
    const char *name = intern(w->intern, o->overrides[i].name);
    uint16_t j = 0;
    while (j < w->param_count && w->params[j].name != name)
      j++;
    if (j == w->param_count)
      return fail(result, TLSF_OBFUSCATE_INVALID, "unknown parameter '%s'",
                  o->overrides[i].name);
    w->params[j].value = o->overrides[i].value;
    w->params[j].has_default = true;
    size_t k = 0;
    while (k < n_effective && strcmp(job->overrides[k].name, name) != 0)
      k++;
    if (k == n_effective)
      n_effective++;
    job->overrides[k] = (ParamOverride){name, o->overrides[i].value};
  }
  for (uint16_t j = 0; j < w->param_count; j++)
    if (!w->params[j].has_default)
      return fail(result, TLSF_OBFUSCATE_UNEXPANDABLE,
                  "parameter '%s' has no value; the self-check expands the "
                  "specification, so pass --param %s=VALUE",
                  w->params[j].name, w->params[j].name);

  job->renamer.spec = w;
  if (o->mode & TLSF_OBFUSCATE_RENAME) {
    if (!rename_spec(&job->renamer, o->seed))
      return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  }
  if ((o->mode & TLSF_OBFUSCATE_REORDER) && !reorder_spec(w, o->seed))
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  if (!inject_fault(w, o->test_fault))
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");

  char *text = nullptr;
  size_t text_size = 0;
  FILE *out = open_memstream(&text, &text_size);
  if (!out)
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  print_tlsf(out, w, /*include_global=*/true);
  if (fclose(out) != 0 || !text) {
    free(text);
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  }
  if (o->test_fault == 4)
    text[text_size /= 2] = '\0';
  result->text = text;
  result->size = text_size;

  // ---- Self-check ----
  job->output = parse_bytes(text, text_size, "output");
  if (!job->output) {
    fflush(job->capture);
    return fail(result, TLSF_OBFUSCATE_CHECK_FAILED,
                "self-check: output does not parse: %s",
                first_line(job->diagnostics, line, sizeof line));
  }
  if (expand(job->reference, job->overrides, n_effective) != 0) {
    fflush(job->capture);
    return fail(result, TLSF_OBFUSCATE_UNEXPANDABLE,
                "input does not expand: %s",
                first_line(job->diagnostics, line, sizeof line));
  }
  if (expand(job->output, nullptr, 0) != 0) {
    fflush(job->capture);
    return fail(result, TLSF_OBFUSCATE_CHECK_FAILED,
                "self-check: output does not expand: %s",
                first_line(job->diagnostics, line, sizeof line));
  }
  CheckOutcome outcome = {TLSF_OBFUSCATE_OK, ""};
  compare_expansions(
      &outcome, (o->mode & TLSF_OBFUSCATE_RENAME) ? &job->renamer : nullptr,
      job->reference, job->output);
  if (outcome.status != TLSF_OBFUSCATE_OK)
    return fail(result, outcome.status, "self-check: %s", outcome.message);

  if ((o->mode & TLSF_OBFUSCATE_RENAME) &&
      !record_map(result, &job->renamer, job->reference))
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  return TLSF_OBFUSCATE_OK;
}

TlsfObfuscateStatus tlsf_obfuscate(const char *source, size_t size,
                                   const TlsfObfuscateOptions *options,
                                   TlsfObfuscateResult *result) {
  if (!result)
    return TLSF_OBFUSCATE_INVALID;
  *result = (TlsfObfuscateResult){0};
  Job job = {0};
  job.capture = open_memstream(&job.diagnostics, &job.diagnostics_size);
  if (!job.capture)
    return fail(result, TLSF_OBFUSCATE_NO_MEMORY, "out of memory");
  job.previous = tlsf_diagnostic_swap(job.capture);
  TlsfObfuscateStatus status = obfuscate(&job, source, size, options, result);
  tlsf_diagnostic_swap(job.previous);
  fclose(job.capture);
  free(job.diagnostics);
  free(job.overrides);
  renamer_free(&job.renamer);
  spec_free(job.work);
  spec_free(job.reference);
  spec_free(job.output);
  if (status != TLSF_OBFUSCATE_OK) {
    char message[sizeof result->message];
    memcpy(message, result->message, sizeof message);
    tlsf_obfuscate_result_clear(result);
    memcpy(result->message, message, sizeof message);
  }
  return status;
}

void tlsf_obfuscate_result_clear(TlsfObfuscateResult *result) {
  if (!result)
    return;
  free(result->text);
  arena_free(result->storage);
  *result = (TlsfObfuscateResult){0};
}

const char *tlsf_obfuscate_kind_name(TlsfObfuscateKind kind) {
  static const char *names[] = {
      [TLSF_OBFUSCATE_INPUT] = "input",
      [TLSF_OBFUSCATE_OUTPUT] = "output",
      [TLSF_OBFUSCATE_PARAMETER] = "parameter",
      [TLSF_OBFUSCATE_ENUM_TYPE] = "enum-type",
      [TLSF_OBFUSCATE_ENUM_LABEL] = "enum-label",
      [TLSF_OBFUSCATE_DEFINITION] = "definition",
      [TLSF_OBFUSCATE_ARGUMENT] = "argument",
      [TLSF_OBFUSCATE_BINDER] = "binder",
      [TLSF_OBFUSCATE_PATTERN] = "pattern",
      [TLSF_OBFUSCATE_FREE] = "free",
      [TLSF_OBFUSCATE_INPUT_SIGNAL] = "input-signal",
      [TLSF_OBFUSCATE_OUTPUT_SIGNAL] = "output-signal",
  };
  return (unsigned)kind < sizeof names / sizeof *names ? names[kind] : "?";
}

const char *tlsf_obfuscate_lookup(const TlsfObfuscateResult *result,
                                  const char *original,
                                  TlsfObfuscateKind kind) {
  for (size_t i = 0; result && original && i < result->entry_count; i++)
    if (result->entries[i].kind == kind &&
        strcmp(result->entries[i].original, original) == 0)
      return result->entries[i].obfuscated;
  return nullptr;
}

bool tlsf_obfuscate_write_map(FILE *out, const TlsfObfuscateResult *result) {
  fprintf(out, "original\tobfuscated\tkind\n");
  for (size_t i = 0; i < result->entry_count; i++)
    fprintf(out, "%s\t%s\t%s\n", result->entries[i].original,
            result->entries[i].obfuscated,
            tlsf_obfuscate_kind_name(result->entries[i].kind));
  return !ferror(out);
}
