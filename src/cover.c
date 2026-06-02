#include "tlsf/cover.h"

#include "tlsf/classify.h"
#include "tlsf/nnf.h"
#include "tlsf/rewrite.h"

#include <assert.h>

const char *role_name(Role r) {
  switch (r) {
  case TLSF_ROLE_INITIALLY:
    return "INITIALLY";
  case TLSF_ROLE_PRESET:
    return "PRESET";
  case TLSF_ROLE_REQUIRE:
    return "REQUIRE";
  case TLSF_ROLE_ASSERT:
    return "ASSERT";
  case TLSF_ROLE_ASSUME:
    return "ASSUME";
  case TLSF_ROLE_GUARANTEE:
    return "GUARANTEE";
  }
  return "?";
}

// ---------------------------------------------------------------------------
// AST walks
// ---------------------------------------------------------------------------

// Intern every atomic proposition occurring in `n` (no flag change).
static void intern_aps(ApTable *t, const Node *n) {
  switch (n->kind) {
  case NODE_AP:
    (void)ap_table_intern(t, n->name, 0);
    return;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    intern_aps(t, n->arg);
    return;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    intern_aps(t, n->lhs);
    intern_aps(t, n->rhs);
    return;
  default:
    return; // true / false
  }
}

// Fill a constraint's support sets.  `neg` tracks occurrence polarity (NNF puts
// negations only at leaves) and `nxt` tracks whether we are under an X.
static void collect(Constraint *c, const ApTable *t, const Node *n, bool neg,
                    bool nxt) {
  switch (n->kind) {
  case NODE_AP: {
    int32_t idx = ap_table_find(t, n->name);
    if (idx < 0)
      return;
    uint8_t f = ap_table_flags(t, (uint32_t)idx);
    if (f & AP_FLAG_INPUT)
      apset_set(&c->inputs, (uint32_t)idx);
    if (f & AP_FLAG_OUTPUT) {
      apset_set(&c->outputs, (uint32_t)idx);
      apset_set(neg ? &c->neg_outputs : &c->pos_outputs, (uint32_t)idx);
      apset_set(nxt ? &c->next_outputs : &c->cur_outputs, (uint32_t)idx);
    }
    return;
  }
  case NODE_NOT:
    collect(c, t, n->arg, !neg, nxt);
    return;
  case NODE_X:
  case NODE_X_STRONG:
    collect(c, t, n->arg, neg, true);
    return;
  case NODE_F:
  case NODE_G:
    collect(c, t, n->arg, neg, nxt);
    return;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    collect(c, t, n->lhs, neg, nxt);
    collect(c, t, n->rhs, neg, nxt);
    return;
  default:
    return;
  }
}

// ---------------------------------------------------------------------------
// Cover construction
// ---------------------------------------------------------------------------

typedef struct {
  Role role;
  bool assumption;
  bool invariant;
  FormulaList *list;
} SectionDesc;

void constraint_add_candidate(ConstraintCover *cov, Constraint *c,
                              const char *name) {
  if (c->candidate_count == c->candidate_cap) {
    uint16_t nc = c->candidate_cap ? (uint16_t)(c->candidate_cap * 2u) : 4u;
    const char **arr = ARENA_ALLOC_N(cov->arena, const char *, nc);
    for (uint16_t i = 0; i < c->candidate_count; i++)
      arr[i] = c->candidates[i];
    c->candidates = arr;
    c->candidate_cap = nc;
  }
  c->candidates[c->candidate_count++] = name;
}

// Append one constraint (formula already grounded); grows cov->items.
static bool add_constraint(ConstraintCover *cov, const SectionDesc *d,
                           Node *formula) {
  Arena *a = cov->arena;
  if (cov->count == cov->cap) {
    uint32_t nc = cov->cap ? cov->cap * 2 : 16;
    Constraint *arr = ARENA_ALLOC_N(a, Constraint, nc);
    for (uint32_t i = 0; i < cov->count; i++)
      arr[i] = cov->items[i];
    cov->items = arr;
    cov->cap = nc;
  }
  Constraint *c = &cov->items[cov->count];
  *c = (Constraint){0};
  c->id = cov->count;
  c->role = d->role;
  c->assumption_side = d->assumption;
  c->guarantee_side = !d->assumption;
  c->invariant_wrapped = d->invariant;
  c->formula = formula;
  c->nnf = to_nnf(a, formula, true);
  if (!c->nnf)
    return false;
  c->is_safety = classify_formula(c->nnf) == FCLASS_SAFETY;
  c->resp_guard = c->resp_target = c->def_output = c->rec_output = -1;
  intern_aps(&cov->aps, c->nnf);
  cov->count++;
  return true;
}

ConstraintCover *cover_build(TlsfSpec *spec, bool split) {
  Arena *a = spec->arena;
  ConstraintCover *cov = ARENA_ALLOC(a, ConstraintCover);
  if (!cov)
    return nullptr;
  cov->arena = a;
  cov->spec = spec;
  ap_table_init(&cov->aps, a);

  // Seed the AP table with scalar signals so input/output flags are known.
  // (Buses are exploded into scalar elements during expand().)
  for (uint32_t i = 0; i < spec->input_count; i++)
    if (!spec->inputs[i].is_bus)
      (void)ap_table_intern(&cov->aps, spec->inputs[i].name, AP_FLAG_INPUT);
  for (uint32_t i = 0; i < spec->output_count; i++)
    if (!spec->outputs[i].is_bus)
      (void)ap_table_intern(&cov->aps, spec->outputs[i].name, AP_FLAG_OUTPUT);

  SectionDesc secs[] = {
      {TLSF_ROLE_INITIALLY, true, false, &spec->initially},
      {TLSF_ROLE_REQUIRE, true, true, &spec->require},
      {TLSF_ROLE_ASSUME, true, false, &spec->assume},
      {TLSF_ROLE_PRESET, false, false, &spec->preset},
      {TLSF_ROLE_ASSERT, false, true, &spec->assert_},
      {TLSF_ROLE_GUARANTEE, false, false, &spec->guarantee},
  };
  uint32_t nsec = sizeof secs / sizeof secs[0];

  cov->items = nullptr;
  cov->count = 0;
  cov->cap = 0;

  // First sweep: one constraint per section formula (or per conjunct when
  // `split`); roles, NNF, classification, intern all APs.
  for (uint32_t s = 0; s < nsec; s++) {
    SectionDesc *d = &secs[s];
    for (uint32_t i = 0; i < d->list->count; i++) {
      Node *f = d->list->formulas[i];
      if (split) {
        Node **parts;
        uint32_t np = rewrite_decompose(a, f, &parts);
        for (uint32_t p = 0; p < np; p++)
          if (!add_constraint(cov, d, parts[p]))
            return nullptr;
      } else if (!add_constraint(cov, d, f)) {
        return nullptr;
      }
    }
  }

  // Second sweep: now the AP table is final, size and fill the support sets.
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *c = &cov->items[i];
    uint32_t n = cov->aps.count;
    apset_init(&c->inputs, a, n);
    apset_init(&c->outputs, a, n);
    apset_init(&c->pos_outputs, a, n);
    apset_init(&c->neg_outputs, a, n);
    apset_init(&c->cur_outputs, a, n);
    apset_init(&c->next_outputs, a, n);
    apset_init(&c->mutex_members, a, n);
    collect(c, &cov->aps, c->nnf, false, false);
  }

  cov->blocks = nullptr;
  cov->block_count = 0;
  return cov;
}
