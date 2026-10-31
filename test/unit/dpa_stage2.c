#include "dpa_internal.h"
#include "tlsf/ast.h"
#include <assert.h>
#include <stdio.h>

static bool truth(unsigned table, unsigned set) { return (table >> set) & 1; }
static unsigned recurring(TlsfDpa *c, uint64_t a, uint64_t b) {
  int seen[2048];
  uint32_t priorities[2048];
  for (unsigned i = 0; i < 2048; ++i)
    seen[i] = -1;
  uint32_t leaf = c->leftmost, step = 0;
  unsigned key = 2 * leaf;
  while (seen[key] < 0) {
    assert(step < 2048);
    seen[key] = (int)step;
    uint64_t mark = step % 2 ? b : a;
    priorities[step++] = dpa_tree_step(c, &leaf, &mark);
    key = 2 * leaf + step % 2;
    assert(key < 2048);
  }
  unsigned maximum = 0;
  for (unsigned i = (unsigned)seen[key]; i < step; ++i)
    if (priorities[i] > maximum)
      maximum = priorities[i];
  return maximum % 2;
}

static void trees(Arena *arena) {
  // Every Boolean acceptance on three colours: all maximal children, and
  // every two-letter periodic mark sequence (including empty marks).
  for (unsigned table = 0; table < 256; ++table) {
    TlsfDpa *c;
    assert(tlsf_dpa_create((TlsfAstNode *)node_true(arena), nullptr, 0, nullptr,
                           0, nullptr, &c)
               .code == TLSF_DPA_OK);
    uint32_t literals[3];
    for (unsigned i = 0; i < 3; ++i) {
      literals[i] = dpa_atom(c, TLSF_AST_KIND_COUNT, i, 0);
      DpaComponent *p = dpa_alloc(c, 1, sizeof *p);
      p->colour = literals[i];
      assert(dpa_insert(c, &c->components, p));
    }
    uint32_t f = 0;
    for (unsigned set = 0; set < 8; ++set) {
      if (!truth(table, set))
        continue;
      uint32_t cube = 1;
      for (unsigned i = 0; i < 3; ++i) {
        uint32_t literal =
            (set & (1u << i))
                ? literals[i]
                : dpa_class(c, oxidd_bdd_not(dpa_cls(c, literals[i])->bdd));
        cube = dpa_boolean(c, true, cube, literal);
      }
      f = dpa_boolean(c, false, f, cube);
    }
    c->acceptance = f;
    c->colour_words = 1;
    c->max_priority = 5;
    c->trees = (DpaTable){0};
    c->paths = (DpaTable){0};
    dpa_tree_init(c);
    assert(tlsf_dpa_status(c).code == TLSF_DPA_OK);
    for (unsigned i = 0; i < c->trees.n; ++i) {
      DpaTreeNode *t = c->trees.items[i];
      unsigned colours = (unsigned)t->colours[0], expected = 0;
      for (unsigned subset = 0; subset < 8; ++subset) {
        if ((subset & ~colours) ||
            truth(table, subset) == truth(table, colours))
          continue;
        bool maximal = true;
        for (unsigned superset = 0; superset < 8; ++superset)
          if (subset != superset && !(subset & ~superset) &&
              !(superset & ~colours) &&
              truth(table, subset) == truth(table, superset))
            maximal = false;
        if (!maximal)
          continue;
        ++expected;
        unsigned matches = 0;
        for (unsigned j = 0; j < t->count; ++j) {
          DpaTreeNode *child = c->trees.items[t->children[j]];
          matches += child->colours[0] == subset;
        }
        assert(matches == 1);
      }
      assert(expected == t->count);
    }
    for (unsigned a = 0; a < 8; ++a)
      for (unsigned b = 0; b < 8; ++b)
        assert(recurring(c, a, b) == truth(table, a | b));
    tlsf_dpa_free(c);
  }
  puts("256 acceptance functions, 16384 periodic mark sequences passed");
}
static void wide(Arena *arena) {
  const char *names[70];
  char storage[70][16];
  Node *f = node_true(arena);
  for (unsigned i = 0; i < 70; ++i) {
    snprintf(storage[i], sizeof storage[i], "p%u", i);
    names[i] = storage[i];
    Node *p = node_ap(arena, names[i]);
    Node *term = i % 2 ? node_f(arena, node_g(arena, p))
                       : node_g(arena, node_f(arena, p));
    f = node_and(arena, f, term);
  }
  TlsfDpa *c;
  assert(tlsf_dpa_create((TlsfAstNode *)f, names, 70, nullptr, 0, nullptr, &c)
             .code == TLSF_DPA_OK);
  assert(c->components.n == 70 && c->colour_words == 2);
  assert(c->trees.n == 0);
  dpa_tree_init(c);
  uint64_t none[2] = {0}, all[2] = {UINT64_MAX, 63};
  uint32_t leaf = c->leftmost;
  assert(dpa_tree_step(c, &leaf, all) % 2 == 0); // all Fin literals false
  (void)dpa_tree_step(c, &leaf, none);
  tlsf_dpa_free(c);
}
static void sharing(Arena *arena) {
  Node *p = node_ap(arena, "a");
  Node *pi = node_g(arena, node_f(arena, p));
  const char *names[] = {"a"};
  for (unsigned conjunction = 0; conjunction < 2; ++conjunction) {
    Node *f = conjunction ? node_and(arena, pi, node_not(arena, pi))
                          : node_or(arena, pi, node_not(arena, pi));
    TlsfDpa *c;
    assert(tlsf_dpa_create((TlsfAstNode *)f, names, 1, nullptr, 0, nullptr, &c)
               .code == TLSF_DPA_OK);
    assert(c->components.n == 1 && c->acceptance == !conjunction);
    assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
    tlsf_dpa_free(c);
  }
}
static void admission(Arena *a) {
  Node *p = node_ap(a, "a"), *q = node_ap(a, "b");
  Node *window = node_and(a, p, node_x(a, q));
  Node *gf = node_g(a, node_f(a, window));
  Node *fg = node_f(a, node_g(a, window));
  Node *response = node_g(a, node_impl(a, p, node_f(a, q)));
  Node *absorbed =
      node_g(a, node_or(a, p, node_and(a, p, node_f(a, node_g(a, q)))));
  Node *absorbed_dual =
      node_f(a, node_and(a, p, node_or(a, p, node_g(a, node_f(a, q)))));
  Node *initial = node_and(a, p, node_g(a, node_f(a, q)));
  Node *mixed = node_and(a, node_g(a, node_f(a, p)), node_f(a, node_g(a, q)));
  Node *group_absorbed = node_or(
      a, initial, node_and(a, initial, node_x(a, node_g(a, node_f(a, q)))));
  Node *group_nested = node_or(
      a, mixed,
      node_and(a, mixed, node_g(a, node_f(a, node_g(a, node_f(a, q))))));
  Node *proved[] = {node_g(a, window),
                    node_f(a, window),
                    gf,
                    fg,
                    response,
                    node_not(a, response),
                    node_f(a, node_and(a, node_g(a, p), node_g(a, q))),
                    node_g(a, node_or(a, node_f(a, p), node_f(a, q))),
                    node_g(a, node_and(a, node_or(a, window, node_f(a, p)),
                                       node_or(a, q, node_f(a, window)))),
                    node_and(a, gf, fg),
                    node_equiv(a, gf, fg),
                    node_or(a, node_g(a, p), node_f(a, q)),
                    node_g(a, node_or(a, p, node_and(a, p, response))),
                    group_absorbed,
                    node_not(a, group_absorbed),
                    group_nested,
                    node_not(a, group_nested)};
  Node *unproved[] = {node_g(a, node_f(a, node_u(a, p, q))),
                      node_g(a, node_impl(a, p, node_f(a, node_u(a, p, q)))),
                      node_x(a, gf), node_g(a, node_f(a, node_f(a, p))),
                      node_g(a, node_or(a, node_f(a, p), node_g(a, q))),
                      node_f(a, node_and(a, node_g(a, p), node_f(a, q))),
                      // Factoring could expose a proved Boolean product, but
                      // admission is checked before G/F distribution.
                      node_g(a, node_and(a, node_g(a, p), node_f(a, q))),
                      node_f(a, node_or(a, node_f(a, p), node_g(a, q)))};
  // Canonical operand absorption is still available to default admission.
  // Research components require structural tags of the frozen NNF atoms.
  Node *canonical_only[] = {
      absorbed, absorbed_dual,
      node_g(a, node_or(a, node_f(a, p),
                        node_and(a, node_f(a, p), node_f(a, node_g(a, q)))))};
  const char *names[] = {"a", "b"};
  for (unsigned mode = 0; mode < 3; ++mode) {
    TlsfDpaBudget budget = {.allow_unproved = mode == 2};
    for (unsigned group = 0; group < 2; ++group) {
      Node **formulas = group ? unproved : proved;
      size_t count = group ? sizeof unproved / sizeof *unproved
                           : sizeof proved / sizeof *proved;
      for (size_t i = 0; i < count; ++i) {
        TlsfDpa *c = (void *)1;
        TlsfDpaStatus status =
            tlsf_dpa_create((TlsfAstNode *)formulas[i], names, 2, nullptr, 0,
                            mode ? &budget : nullptr, &c);
        if (!group || budget.allow_unproved) {
          assert(status.code == TLSF_DPA_OK && c);
          assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
        } else
          assert(status.code == TLSF_DPA_DECLINED &&
                 status.reason == TLSF_DPA_UNSUPPORTED && !c);
        tlsf_dpa_free(c);
      }
    }
    for (size_t i = 0; i < sizeof canonical_only / sizeof *canonical_only; ++i)
      for (unsigned neg = 0; neg < 2; ++neg) {
        Node *f = neg ? node_not(a, canonical_only[i]) : canonical_only[i];
        TlsfDpa *c = (void *)1;
        TlsfDpaStatus status =
            tlsf_dpa_create((TlsfAstNode *)f, names, 2, nullptr, 0,
                            mode ? &budget : nullptr, &c);
        if (budget.allow_unproved)
          assert(status.code == TLSF_DPA_DECLINED &&
                 status.reason == TLSF_DPA_UNSUPPORTED && !c);
        else {
          assert(status.code == TLSF_DPA_OK && c);
          assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
        }
        tlsf_dpa_free(c);
      }
  }
}

static void syntactic_protection(Arena *a) {
  Node *p = node_ap(a, "a"), *q = node_ap(a, "b");
  Node *x = node_x(a, node_f(a, q));
  Node *hidden = node_or(a, p, node_and(a, p, x));
  Node *protectors[] = {node_f(a, hidden),    node_u(a, hidden, q),
                        node_u(a, q, hidden), node_m(a, hidden, q),
                        node_m(a, q, hidden), node_u(a, hidden, p)};
  const char *names[] = {"a", "b"};
  TlsfDpaBudget budget = {
      .bdd_nodes = 1u << 14, .bdd_cache = 1u << 12, .allow_unproved = true};
  for (size_t i = 0; i < sizeof protectors / sizeof *protectors; ++i) {
    // First case is G(F(a | (a & X F b)) | X F b), the review example.
    Node *body = node_or(a, protectors[i], x);
    Node *root = node_g(a, body);
    TlsfDpa *c;
    if (i == 0) {
      TlsfDpaStatus status = tlsf_dpa_create((TlsfAstNode *)root, names, 2,
                                             nullptr, 0, nullptr, &c);
      assert(status.code == TLSF_DPA_DECLINED &&
             status.reason == TLSF_DPA_UNSUPPORTED && !c);
    }
    assert(
        tlsf_dpa_create((TlsfAstNode *)root, names, 2, nullptr, 0, &budget, &c)
            .code == TLSF_DPA_OK);
    assert(c->components.n == 1);
    const TlsfDpaEdge *edges;
    size_t count;
    assert(tlsf_dpa_successors(c, tlsf_dpa_initial(c), &edges, &count).code ==
           TLSF_DPA_OK);
    DpaState *state = c->states.items[c->initial];
    DpaTuple *tuple = c->tuples.items[state->tuple];
    DpaPair *pair = c->pairs.items[tuple->values[0]];
    // In the last case unfolding absorbs the U protector itself. Retry must
    // recompute protection from that support and remove the now unprotected X.
    uint32_t expected =
        i == 5 ? 1
               : dpa_unfold(c, dpa_formula(c, (TlsfAstNode *)body, false, 0));
    assert(pair->rejecting == expected);
    if (i < 5)
      assert(pair->rejecting != 1);
    assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
    tlsf_dpa_free(c);
  }
}
int main(void) {
  Arena *a = arena_new(4096);
  syntactic_protection(a);
  admission(a);
  trees(a);
  wide(a);
  sharing(a);
  Node *p = node_ap(a, "a"), *f = p;
  for (unsigned i = 0; i < 400; ++i)
    f = node_and(a, f, p);
  const char *names[] = {"a"};
  TlsfDpa *c;
  assert(tlsf_dpa_create((TlsfAstNode *)f, names, 1, nullptr, 0, nullptr, &c)
             .code == TLSF_DPA_OK);
  assert(tlsf_dpa_expand(c).code == TLSF_DPA_OK);
  tlsf_dpa_free(c);
  arena_free(a);
  puts("Boolean product passed");
}
