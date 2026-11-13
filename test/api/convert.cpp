#include "tlsf/convert.hpp"

#include "../check.h"
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
    CHECK(owned);
    auto result = tlsf::convert(source, "Mealy");
    CHECK(result.semantics == "Strict,Moore");
    CHECK(result.original_target == "Moore" &&
          result.effective_target == "Mealy");
    CHECK(result.preprocessed_ltl == "G (X a -> b)");
    CHECK(result.inputs == std::vector<std::string>({"unused_i", "a"}));
    CHECK(result.outputs == std::vector<std::string>({"unused_o", "b"}));
    CHECK(result.indexed_families.empty() && !result.has_indexed_conjunction);
    CHECK(result.gr_level == 0);
    CHECK(result.ast && tlsf_ast_root(result.ast.get()));
    CHECK(!tlsf_ast_result(result.ast.get()) &&
          tlsf_ast_cluster_count(result.ast.get()) == 0);
    auto copy = result;
    CHECK(copy.ast == result.ast);
    retained = copy.ast;
    auto unchanged = tlsf::convert(source, nullptr);
    CHECK(unchanged.original_target == "Moore" &&
          unchanged.effective_target == "Moore");
    CHECK(unchanged.preprocessed_ltl == "G (a -> b)");
    CHECK(!tlsf_convert(source.c_str(), "invalid"));
  }
  // The parser and source string are gone; all returned storage is independent.
  CHECK(std::strcmp(owned->semantics, "Strict,Moore") == 0);
  CHECK(std::strcmp(owned->preprocessed_ltl, "G (X a -> b)") == 0);
  CHECK(std::strcmp(owned->inputs[0], "unused_i") == 0);
  const auto *root = tlsf_ast_root(owned->ast);
  CHECK(tlsf_ast_node_kind(root) == TLSF_AST_G);
  const auto *implication = tlsf_ast_node_child(root, 0);
  CHECK(tlsf_ast_node_kind(implication) == TLSF_AST_IMPL);
  const auto *next = tlsf_ast_node_child(implication, 0);
  CHECK(tlsf_ast_node_kind(next) == TLSF_AST_X);
  CHECK(std::strcmp(tlsf_ast_node_ap_name(tlsf_ast_node_child(next, 0)), "a") ==
        0);
  CHECK(std::strcmp(tlsf_ast_node_ap_name(tlsf_ast_node_child(implication, 1)),
                    "b") == 0);
  tlsf_conversion_result_free(owned);
  CHECK(tlsf_ast_node_kind(tlsf_ast_root(retained.get())) == TLSF_AST_G);
  tlsf_conversion_result_free(nullptr);
  CHECK(!tlsf_convert(nullptr, "Mealy"));
  // Free names are rejected (§§4.1–4.3), and declared names must not merge
  // when tlsf_convert lowercases the returned AST.
  for (const char *semantics :
       {"Mealy", "Moore", "Mealy,Strict", "Moore,Strict"})
    for (const char *declaration :
         {"", "INPUTS { q; }", "OUTPUTS { q; }", "INPUTS { q; Q; }",
          "INPUTS { q; } OUTPUTS { Q; }"})
      for (const char *role : {"INITIALLY", "PRESET", "REQUIRE", "ASSERT",
                               "ASSUMPTIONS", "GUARANTEES"}) {
        const std::string source =
            "INFO { SEMANTICS: " + std::string(semantics) +
            " TARGET: Mealy } MAIN { " + declaration + " " + role +
            " { q <-> Q; } }";
        CHECK(!tlsf_convert(source.c_str(), "Mealy"));
      }
  for (const char *semantics : {"Moore", "Moore,Strict"}) {
    const std::string source =
        "INFO { SEMANTICS: " + std::string(semantics) +
        " TARGET: Mealy } MAIN { OUTPUTS { p; } GUARANTEES { G(p <-> u); } }";
    CHECK(!tlsf_convert(source.c_str(), "Mealy"));
    std::string declared = source;
    declared.insert(declared.find("OUTPUTS"), "INPUTS { u; } ");
    const auto adapted = tlsf::convert(declared, "Mealy");
    CHECK(adapted.inputs == std::vector<std::string>({"u"}));
    CHECK(adapted.outputs == std::vector<std::string>({"p"}));
    CHECK(adapted.preprocessed_ltl == "G (p <-> X u)");
  }
}
