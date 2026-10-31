#include "env_witness.h"

#include <assert.h>
#include <stdio.h>

static unsigned checked;

static SectionPatternView environment(SectionPatternEntry *entries,
                                      unsigned count) {
  return (SectionPatternView){.entries = entries, .count = count};
}

static bool at(const EnvLasso *w, unsigned time, unsigned ap) {
  unsigned pos = time < w->length
                     ? time
                     : w->loop + (time - w->loop) % (w->length - w->loop);
  return (w->letters[pos] >> ap) & 1u;
}

// Independent bounded traversal: every reachable position is visited within
// length steps, also when starting after the prefix. Until needs a finite
// right-hand witness; W/R allow an infinite left/right continuation.
static bool until(const EnvLasso *w, unsigned time, bool dual) {
  for (unsigned i = 0; i < w->length; ++i) {
    if (at(w, time + i, 1) != dual)
      return true;
    if (at(w, time + i, 0) == dual)
      return false;
  }
  return false;
}

static bool expected(NodeKind kind, const EnvLasso *w, unsigned time) {
  bool a = at(w, time, 0), b = at(w, time, 1);
  bool all = true, any = false;
  for (unsigned i = 0; i < w->length; ++i) {
    all &= at(w, time + i, 0);
    any |= at(w, time + i, 0);
  }
  switch (kind) {
  case NODE_TRUE:
    return true;
  case NODE_FALSE:
    return false;
  case NODE_AP:
    return a;
  case NODE_NOT:
    return !a;
  case NODE_AND:
    return a && b;
  case NODE_OR:
    return a || b;
  case NODE_IMPL:
    return !a || b;
  case NODE_EQUIV:
    return a == b;
  case NODE_X:
  case NODE_X_STRONG:
    return at(w, time + 1, 0);
  case NODE_F:
    return any;
  case NODE_G:
    return all;
  case NODE_U:
    return until(w, time, false);
  case NODE_R:
    return !until(w, time, true);
  case NODE_W:
    return until(w, time, false) || all;
  case NODE_M:
    return !until(w, time, true) && any;
  default:
    assert(false);
    return false;
  }
}

static void check_word(Node *formula, const EnvLasso *w, bool truth) {
  SectionPatternEntry e = {.role = TLSF_ROLE_ASSUME, .formula = formula};
  SectionPatternView d = environment(&e, 1);
  EnvWitnessResult result = env_lasso_check(&d, w, ENV_WITNESS_WORK_BUDGET);
  assert(result == (truth ? ENV_WITNESS_SATISFIABLE : ENV_WITNESS_UNKNOWN));
  ++checked;
}

static void evaluator(Arena *arena) {
  Node *a = node_ap(arena, "a"), *b = node_ap(arena, "b");
  Node *forms[] = {
      node_true(arena),        node_false(arena),       a,
      node_not(arena, a),      node_and(arena, a, b),   node_or(arena, a, b),
      node_impl(arena, a, b),  node_equiv(arena, a, b), node_x(arena, a),
      node_x_strong(arena, a), node_f(arena, a),        node_g(arena, a),
      node_u(arena, a, b),     node_r(arena, a, b),     node_w(arena, a, b),
      node_m(arena, a, b),
  };
  const char *aps[] = {"a", "b"};
  uint8_t letters[ENV_WITNESS_MAX_LENGTH];
  EnvLasso w = {.aps = aps, .letters = letters, .ap_count = 2};
  for (unsigned f = 0; f < sizeof forms / sizeof *forms; ++f) {
    Node *shifted[7] = {forms[f]};
    for (unsigned t = 1; t < 7; ++t)
      shifted[t] = node_x(arena, shifted[t - 1]);
    for (w.length = 1; w.length <= ENV_WITNESS_MAX_LENGTH; ++w.length)
      for (w.loop = 0; w.loop < w.length; ++w.loop)
        for (unsigned bits = 0; bits < (1u << (2 * w.length)); ++bits) {
          for (unsigned j = 0; j < w.length; ++j)
            letters[j] = (uint8_t)((bits >> (2 * j)) & 3u);
          for (unsigned t = 0; t < 7; ++t)
            check_word(shifted[t], &w, expected(forms[f]->kind, &w, t));
        }
  }
  // Nested temporal formulas must ignore a transient prefix for recurrence
  // and persistence, and distinguish finite satisfaction from infinite ones.
  Node *gf = node_g(arena, node_f(arena, a));
  Node *fg = node_f(arena, node_g(arena, a));
  for (w.length = 1; w.length <= ENV_WITNESS_MAX_LENGTH; ++w.length)
    for (w.loop = 0; w.loop < w.length; ++w.loop)
      for (unsigned bits = 0; bits < (1u << w.length); ++bits) {
        bool loop_any = false, loop_all = true;
        for (unsigned j = 0; j < w.length; ++j) {
          letters[j] = (uint8_t)((bits >> j) & 1u);
          if (j >= w.loop) {
            loop_any |= letters[j] != 0;
            loop_all &= letters[j] != 0;
          }
        }
        check_word(gf, &w, loop_any);
        check_word(fg, &w, loop_all);
      }
}

static void search(Arena *arena) {
  Node *q = node_ap(arena, "q"), *nq = node_not(arena, q);
  SectionPatternEntry entries[] = {
      {.role = TLSF_ROLE_INITIALLY, .formula = q},
      {.role = TLSF_ROLE_REQUIRE, .formula = node_x(arena, nq)},
      {.role = TLSF_ROLE_ASSUME, .formula = node_f(arena, nq)},
  };
  SectionPatternView d = environment(entries, 3);
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_SATISFIABLE); // Needs a prefix, then an all-false loop.
  assert(env_witness_search(&d, 0) == ENV_WITNESS_UNKNOWN);
  assert(env_witness_search(&d, 1) == ENV_WITNESS_UNKNOWN);
  entries[1].formula = nq; // INITIALLY q contradicts G !q.
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  entries[0].formula = node_true(arena);
  entries[2].formula = node_f(arena, q); // G !q contradicts F q.
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  entries[1].formula = node_equiv(arena, q, node_x(arena, nq));
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_SATISFIABLE); // Alternating loop, no constant witness.
  entries[1].formula = node_g(arena, node_f(arena, q));
  entries[2].formula = node_f(arena, node_g(arena, nq));
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);

  // Satisfiable, but every lasso needs at least five distinct positions.
  Node *late = node_f(arena, q), *early = nq;
  for (unsigned i = 0; i < 4; ++i) {
    late = node_and(arena, late, early);
    early = node_x(arena, early);
  }
  entries[0].formula = late;
  d.count = 1;
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  Node *deep = q;
  for (unsigned i = 0; i < 130; ++i)
    deep = node_x(arena, deep);
  entries[0].formula = deep;
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  entries[0].formula = node_int(arena, 1);
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  entries[0].formula = q;
  entries[0].role = TLSF_ROLE_GUARANTEE;
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  entries[0].role = TLSF_ROLE_ASSUME;
  const char *names[] = {"a", "b", "c", "d", "e", "f", "g", "h", "i"};
  for (unsigned i = 0; i < 9; ++i)
    entries[0].formula =
        node_and(arena, entries[0].formula, node_ap(arena, names[i]));
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_UNKNOWN);
  d.count = 0;
  assert(env_witness_search(&d, ENV_WITNESS_WORK_BUDGET) ==
         ENV_WITNESS_SATISFIABLE);
}

static void guards(Arena *arena) {
  const char *aps[] = {"q", "q"};
  uint8_t letters[] = {1, 0};
  EnvLasso w = {
      .aps = aps, .letters = letters, .ap_count = 1, .length = 2, .loop = 0};
  Node *q = node_ap(arena, "q");
  SectionPatternEntry e = {.role = TLSF_ROLE_REQUIRE, .formula = q};
  SectionPatternView d = environment(&e, 1);
  assert(env_lasso_check(&d, &w, 100) == ENV_WITNESS_UNKNOWN); // G wrapping.
  e.role = TLSF_ROLE_INITIALLY;
  assert(env_lasso_check(&d, &w, 100) == ENV_WITNESS_SATISFIABLE);
  assert(env_lasso_check(&d, &w, 0) == ENV_WITNESS_UNKNOWN);
  e.formula = node_g(arena, node_not(arena, q));
  assert(env_lasso_check(&d, &w, 3) == ENV_WITNESS_UNKNOWN); // Mid-fixpoint.
  w.ap_count = 2;
  assert(env_lasso_check(&d, &w, 100) == ENV_WITNESS_UNKNOWN); // Duplicate AP.
  w.ap_count = 0;
  e.formula = node_not(arena, q); // Unlisted APs are false.
  assert(env_lasso_check(&d, &w, 100) == ENV_WITNESS_SATISFIABLE);
  w.length = 0;
  assert(env_lasso_check(&d, &w, 100) == ENV_WITNESS_UNKNOWN);
  w.length = 1;
  w.loop = 1;
  assert(env_lasso_check(&d, &w, 100) == ENV_WITNESS_UNKNOWN);
  assert(env_witness_search(nullptr, 100) == ENV_WITNESS_UNKNOWN);
}

int main(void) {
  Arena *arena = arena_new(4096);
  assert(arena);
  evaluator(arena);
  search(arena);
  guards(arena);
  assert(!arena_failed(arena));
  arena_free(arena);
  printf("%u lasso evaluations; joint witness, budget and admission checks "
         "passed\n",
         checked);
  return 0;
}
