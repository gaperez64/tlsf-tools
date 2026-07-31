#include "tlsf/ast_api.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

static void *encoded(uintptr_t value) { return (void *)value; }
static uintptr_t decoded(void *value) { return (uintptr_t)value; }

static void *visit_leaf(void *ctx) {
  (*(uint32_t *)ctx)++;
  return encoded(1);
}

static void *visit_default(void *ctx, const TlsfAstNode *node) {
  assert(node);
  return visit_leaf(ctx);
}

static void *visit_ap(void *ctx, const char *name) {
  assert(name && *name);
  return visit_leaf(ctx);
}

static void *visit_unary(void *ctx, void *arg) {
  (*(uint32_t *)ctx)++;
  return encoded(decoded(arg) + 1);
}

static void *visit_binary(void *ctx, void *lhs, void *rhs) {
  (*(uint32_t *)ctx)++;
  return encoded(decoded(lhs) + decoded(rhs) + 1);
}

static uint32_t manual_count(const TlsfAstNode *node) {
  uint32_t count = 1;
  for (uint32_t i = 0; i < tlsf_ast_node_child_count(node); i++)
    count += manual_count(tlsf_ast_node_child(node, i));
  return count;
}

static bool contains_kind(const TlsfAstNode *node, TlsfAstKind kind) {
  if (tlsf_ast_node_kind(node) == kind)
    return true;
  for (uint32_t i = 0; i < tlsf_ast_node_child_count(node); i++) {
    if (contains_kind(tlsf_ast_node_child(node, i), kind))
      return true;
  }
  return false;
}

static bool ast_contains_kind(const TlsfAst *ast, TlsfAstKind kind) {
  if (contains_kind(tlsf_ast_root(ast), kind))
    return true;
  for (uint32_t i = 0; i < tlsf_ast_cluster_count(ast); i++) {
    if (contains_kind(tlsf_ast_cluster_root(ast, i), kind))
      return true;
  }
  return false;
}

int main(void) {
  TlsfAstVisitor empty_visitor = {0};
  tlsf_ast_free(nullptr);
  assert(tlsf_ast_from_file(nullptr, nullptr) == nullptr);
  assert(tlsf_ast_from_file_ex(nullptr, nullptr, nullptr) == nullptr);
  assert(tlsf_ast_from_string(nullptr, nullptr) == nullptr);
  assert(tlsf_ast_from_string_ex(nullptr, nullptr, nullptr) == nullptr);
  assert(tlsf_ast_root(nullptr) == nullptr);
  assert(tlsf_ast_cluster_count(nullptr) == 0);
  assert(tlsf_ast_cluster_root(nullptr, 0) == nullptr);
  assert(tlsf_ast_result(nullptr) == nullptr);
  assert(tlsf_ast_node_kind(nullptr) == TLSF_AST_KIND_COUNT);
  assert(tlsf_ast_node_ap_name(nullptr) == nullptr);
  assert(tlsf_ast_node_child_count(nullptr) == 0);
  assert(tlsf_ast_node_child(nullptr, 0) == nullptr);
  assert(tlsf_ast_accept(nullptr, &empty_visitor, nullptr) == nullptr);

  const char *text =
      "INFO { TITLE: \"ast\" SEMANTICS: Finite,Mealy TARGET: Mealy }\n"
      "MAIN { INPUTS { a; b; } OUTPUTS { x; y; }\n"
      "GUARANTEE { G (x <-> X a); F (y && (a U b));\n"
      "X[!] x; a R b; !x; } }\n";
  TlsfDecomposeOptions options = {.split = true};
  TlsfAst *ast = tlsf_ast_from_string(text, &options);
  assert(ast);

  const TlsfDecomposeResult *result = tlsf_ast_result(ast);
  assert(result);
  assert(result->n_inputs == 2);
  assert(result->n_outputs == 2);
  assert(result->n_clusters == tlsf_ast_cluster_count(ast));
  assert(tlsf_ast_root(ast));
  assert(ast_contains_kind(ast, TLSF_AST_NOT));
  assert(ast_contains_kind(ast, TLSF_AST_X_STRONG));
  assert(ast_contains_kind(ast, TLSF_AST_R));
  for (uint32_t i = 0; i < tlsf_ast_cluster_count(ast); i++)
    assert(tlsf_ast_cluster_root(ast, i));
  assert(tlsf_ast_cluster_root(ast, tlsf_ast_cluster_count(ast)) == nullptr);

  TlsfAstVisitor visitor = {
      .visit_true = visit_leaf,
      .visit_false = visit_leaf,
      .visit_ap = visit_ap,
      .visit_not = visit_unary,
      .visit_x = visit_unary,
      .visit_x_strong = visit_unary,
      .visit_f = visit_unary,
      .visit_g = visit_unary,
      .visit_and = visit_binary,
      .visit_or = visit_binary,
      .visit_impl = visit_binary,
      .visit_equiv = visit_binary,
      .visit_u = visit_binary,
      .visit_r = visit_binary,
      .visit_w = visit_binary,
      .visit_m = visit_binary,
  };
  uint32_t callbacks = 0;
  void *visited = tlsf_ast_accept(tlsf_ast_root(ast), &visitor, &callbacks);
  assert(visited);
  assert(decoded(visited) == manual_count(tlsf_ast_root(ast)));
  assert(callbacks == decoded(visited));

  const TlsfAstNode *root = tlsf_ast_root(ast);
  assert(tlsf_ast_accept(root, nullptr, nullptr) == nullptr);
  assert(tlsf_ast_node_kind(root) < TLSF_AST_KIND_COUNT);
  assert(tlsf_ast_node_child(root, tlsf_ast_node_child_count(root)) == nullptr);
  assert(tlsf_ast_node_ap_name(root) == nullptr ||
         strlen(tlsf_ast_node_ap_name(root)) > 0);

  TlsfAstVisitor default_visitor = {.visit_default = visit_default};
  callbacks = 0;
  visited = tlsf_ast_accept(root, &default_visitor, &callbacks);
  assert(visited);
  assert(callbacks == manual_count(root));
  TlsfAstVisitor aborting_visitor = {0};
  assert(tlsf_ast_accept(root, &aborting_visitor, nullptr) == nullptr);

  tlsf_ast_free(ast);

  const char *strong_release_text =
      "INFO { TITLE: \"lower M\" SEMANTICS: Mealy TARGET: Mealy }\n"
      "MAIN { INPUTS { a; b; } OUTPUTS { x; }\n"
      "GUARANTEE { !(a W b); } }\n";
  ast = tlsf_ast_from_string(strong_release_text, &options);
  assert(ast);
  assert(ast_contains_kind(ast, TLSF_AST_W));
  tlsf_ast_free(ast);

  TlsfAstOptions ast_options = {.lower_strong_release = true};
  ast = tlsf_ast_from_string_ex(strong_release_text, &options, &ast_options);
  assert(ast);
  assert(!ast_contains_kind(ast, TLSF_AST_M));
  tlsf_ast_free(ast);
  return 0;
}
