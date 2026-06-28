#include "tlsf/section_pattern.h"

#include "tlsf/gr.h"
#include "tlsf/nnf.h"

void section_pattern_init(SectionPatternView *v, Arena *a,
                          const TlsfSpec *spec) {
  *v = (SectionPatternView){
      .arena = a,
      .spec = spec,
  };
}

bool section_pattern_add(SectionPatternView *v, Role role, Node *formula,
                         FormulaClass cls) {
  if (v->count == v->cap) {
    uint32_t nc = v->cap ? v->cap * 2u : 16u;
    SectionPatternEntry *arr = ARENA_ALLOC_N(v->arena, SectionPatternEntry, nc);
    if (!arr)
      return false;
    for (uint32_t i = 0; i < v->count; i++)
      arr[i] = v->entries[i];
    v->entries = arr;
    v->cap = nc;
  }
  v->entries[v->count++] = (SectionPatternEntry){
      .role = role,
      .formula = formula,
      .cls = cls,
  };
  return true;
}

bool section_pattern_add_classified(SectionPatternView *v, Role role,
                                    Node *formula) {
  FormulaClass cls = FCLASS_SAFETY;
  if (role == TLSF_ROLE_ASSERT || role == TLSF_ROLE_GUARANTEE) {
    Node *nnf = to_nnf(v->arena, formula, true);
    if (!nnf)
      return false;
    cls = classify_formula(nnf);
  }
  return section_pattern_add(v, role, formula, cls);
}

bool section_pattern_from_classified(SectionPatternView *v,
                                     const TlsfSpec *spec,
                                     const ClassifiedSpec *cs) {
  section_pattern_init(v, spec->arena, spec);
  for (uint32_t i = 0; i < cs->initially_count; i++)
    if (!section_pattern_add(v, TLSF_ROLE_INITIALLY, cs->initially[i],
                             FCLASS_SAFETY))
      return false;
  for (uint32_t i = 0; i < cs->preset_count; i++)
    if (!section_pattern_add(v, TLSF_ROLE_PRESET, cs->preset[i], FCLASS_SAFETY))
      return false;
  for (uint32_t i = 0; i < cs->require_count; i++)
    if (!section_pattern_add(v, TLSF_ROLE_REQUIRE, cs->require[i],
                             FCLASS_SAFETY))
      return false;
  for (uint32_t i = 0; i < cs->assume_count; i++)
    if (!section_pattern_add(v, TLSF_ROLE_ASSUME, cs->assume[i],
                             FCLASS_LIVENESS))
      return false;
  for (uint32_t i = 0; i < cs->assert_count; i++)
    if (!section_pattern_add(v, TLSF_ROLE_ASSERT, cs->asserts[i].formula,
                             cs->asserts[i].cls))
      return false;
  for (uint32_t i = 0; i < cs->guarantee_count; i++)
    if (!section_pattern_add(v, TLSF_ROLE_GUARANTEE, cs->guarantees[i].formula,
                             cs->guarantees[i].cls))
      return false;
  return true;
}

static Node *and_opt(Arena *a, Node *x, Node *y) {
  if (!x)
    return y;
  if (!y)
    return x;
  return node_and(a, x, y);
}

static Node *conj_entries(const SectionPatternView *v, Role role,
                          bool use_class, bool safety, bool liveness) {
  Node *acc = nullptr;
  for (uint32_t i = 0; i < v->count; i++) {
    const SectionPatternEntry *e = &v->entries[i];
    if (e->role != role)
      continue;
    if (use_class && !((e->cls == FCLASS_SAFETY && safety) ||
                       (e->cls == FCLASS_LIVENESS && liveness)))
      continue;
    acc = and_opt(v->arena, acc, e->formula);
  }
  return acc;
}

Node *section_pattern_conj(const SectionPatternView *v, Role role) {
  return conj_entries(v, role, false, true, true);
}

Node *section_pattern_guarantees(const SectionPatternView *v, bool safety,
                                 bool liveness) {
  return conj_entries(v, TLSF_ROLE_GUARANTEE, true, safety, liveness);
}

bool section_pattern_role_empty(const SectionPatternView *v, Role role) {
  for (uint32_t i = 0; i < v->count; i++)
    if (v->entries[i].role == role)
      return false;
  return true;
}

static FormulaList *tmp_role_list(TlsfSpec *spec, Role role) {
  switch (role) {
  case TLSF_ROLE_INITIALLY:
    return &spec->initially;
  case TLSF_ROLE_PRESET:
    return &spec->preset;
  case TLSF_ROLE_REQUIRE:
    return &spec->require;
  case TLSF_ROLE_ASSERT:
    return &spec->assert_;
  case TLSF_ROLE_ASSUME:
    return &spec->assume;
  case TLSF_ROLE_GUARANTEE:
  default:
    return &spec->guarantee;
  }
}

int section_pattern_gr_level(const SectionPatternView *v) {
  TlsfSpec tmp = *v->spec;
  tmp.initially = (FormulaList){0};
  tmp.require = (FormulaList){0};
  tmp.assume = (FormulaList){0};
  tmp.preset = (FormulaList){0};
  tmp.assert_ = (FormulaList){0};
  tmp.guarantee = (FormulaList){0};

  for (uint32_t role = TLSF_ROLE_INITIALLY; role <= TLSF_ROLE_GUARANTEE;
       role++) {
    uint32_t n = 0;
    for (uint32_t i = 0; i < v->count; i++)
      n += v->entries[i].role == (Role)role;
    if (n == 0)
      continue;
    FormulaList *list = tmp_role_list(&tmp, (Role)role);
    list->formulas = ARENA_ALLOC_N(v->arena, Node *, n);
    if (!list->formulas)
      return -1;
    list->capacity = n;
  }

  for (uint32_t i = 0; i < v->count; i++) {
    FormulaList *list = tmp_role_list(&tmp, v->entries[i].role);
    list->formulas[list->count++] = v->entries[i].formula;
  }
  return gr_level(&tmp);
}

static Node *g_conj(Arena *a, Node *x) { return x ? node_g(a, x) : nullptr; }

Node *section_pattern_to_ltl(const SectionPatternView *v, bool want_safety,
                             bool want_liveness) {
  Arena *a = v->arena;
  bool strict = semantics_is_strict(v->spec->info.semantics);

  Node *e_init = section_pattern_conj(v, TLSF_ROLE_INITIALLY);
  Node *req_raw = section_pattern_conj(v, TLSF_ROLE_REQUIRE);
  Node *e_req = g_conj(a, req_raw);
  Node *a_live = section_pattern_conj(v, TLSF_ROLE_ASSUME);
  Node *s_pre = section_pattern_conj(v, TLSF_ROLE_PRESET);

  if (strict) {
    Node *assert_raw =
        want_safety ? section_pattern_conj(v, TLSF_ROLE_ASSERT) : nullptr;
    Node *safety_part = nullptr;
    if (assert_raw)
      safety_part = req_raw ? node_w(a, assert_raw, node_not(a, req_raw))
                            : node_g(a, assert_raw);

    Node *env = and_opt(a, e_req, a_live);
    Node *g_gua = section_pattern_guarantees(v, want_safety, want_liveness);
    Node *gua_part = g_gua ? (env ? node_impl(a, env, g_gua) : g_gua) : nullptr;
    Node *sys_safety = and_opt(a, want_safety ? s_pre : nullptr, safety_part);
    Node *body = and_opt(a, sys_safety, gua_part);
    if (!body)
      return node_true(a);
    return e_init ? node_impl(a, e_init, body) : body;
  }

  Node *env = and_opt(a, e_req, a_live);
  Node *g_assert = want_safety
                       ? g_conj(a, section_pattern_conj(v, TLSF_ROLE_ASSERT))
                       : nullptr;
  Node *g_gua = section_pattern_guarantees(v, want_safety, want_liveness);
  Node *sys = and_opt(a, g_assert, g_gua);
  Node *inner = sys ? (env ? node_impl(a, env, sys) : sys) : nullptr;
  Node *body = and_opt(a, want_safety ? s_pre : nullptr, inner);
  if (e_init)
    return body ? node_impl(a, e_init, body) : node_true(a);
  return body ? body : node_true(a);
}
