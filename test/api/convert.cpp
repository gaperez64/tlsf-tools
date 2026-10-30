#include "tlsf/convert.hpp"

#include <cassert>
#include <cstring>

int main() {
  TlsfConversionResult *owned;
  std::shared_ptr<TlsfAst> retained;
  {
    const std::string source = R"(
INFO { TITLE: "conversion ownership" SEMANTICS: Moore,Strict TARGET: Moore }
MAIN { INPUTS { A; unused_i; } OUTPUTS { B; unused_o; }
       GUARANTEE { G (A -> B); } })";
    owned = tlsf_convert(source.c_str(), "Mealy");
    assert(owned);
    auto result = tlsf::convert(source, "Mealy");
    assert(result.semantics == "Strict,Moore");
    assert(result.original_target == "Moore" &&
           result.effective_target == "Mealy");
    assert(result.preprocessed_ltl == "G (X a -> b)");
    assert(result.inputs == std::vector<std::string>({"unused_i", "a"}));
    assert(result.outputs == std::vector<std::string>({"unused_o", "b"}));
    assert(result.indexed_families.empty() && !result.has_indexed_conjunction);
    assert(result.gr_level == 0);
    assert(result.ast && tlsf_ast_root(result.ast.get()));
    assert(!tlsf_ast_result(result.ast.get()) &&
           tlsf_ast_cluster_count(result.ast.get()) == 0);
    auto copy = result;
    assert(copy.ast == result.ast);
    retained = copy.ast;
    auto unchanged = tlsf::convert(source, nullptr);
    assert(unchanged.original_target == "Moore" &&
           unchanged.effective_target == "Moore");
    assert(unchanged.preprocessed_ltl == "G (a -> b)");
    assert(!tlsf_convert(source.c_str(), "invalid"));
  }
  // The parser and source string are gone; all returned storage is independent.
  assert(std::strcmp(owned->semantics, "Strict,Moore") == 0);
  assert(std::strcmp(owned->preprocessed_ltl, "G (X a -> b)") == 0);
  assert(std::strcmp(owned->inputs[0], "unused_i") == 0);
  const auto *root = tlsf_ast_root(owned->ast);
  assert(tlsf_ast_node_kind(root) == TLSF_AST_G);
  const auto *implication = tlsf_ast_node_child(root, 0);
  assert(tlsf_ast_node_kind(implication) == TLSF_AST_IMPL);
  const auto *next = tlsf_ast_node_child(implication, 0);
  assert(tlsf_ast_node_kind(next) == TLSF_AST_X);
  assert(std::strcmp(tlsf_ast_node_ap_name(tlsf_ast_node_child(next, 0)),
                     "a") == 0);
  assert(std::strcmp(tlsf_ast_node_ap_name(tlsf_ast_node_child(implication, 1)),
                     "b") == 0);
  tlsf_conversion_result_free(owned);
  assert(tlsf_ast_node_kind(tlsf_ast_root(retained.get())) == TLSF_AST_G);
  tlsf_conversion_result_free(nullptr);
  assert(!tlsf_convert(nullptr, "Mealy"));
}
