#include "tlsf/convert.hpp"

#include "../check.h"
#include <cstring>

static void same_conversion(const tlsf::Conversion &a,
                            const tlsf::Conversion &b) {
  CHECK(a.preprocessed_ltl == b.preprocessed_ltl && a.inputs == b.inputs &&
        a.outputs == b.outputs && a.semantics == b.semantics &&
        a.original_target == b.original_target &&
        a.effective_target == b.effective_target && a.gr_level == b.gr_level &&
        a.has_indexed_conjunction == b.has_indexed_conjunction &&
        a.indexed_families.size() == b.indexed_families.size());
  for (size_t i = 0; i < a.indexed_families.size(); i++) {
    const auto &x = a.indexed_families[i], &y = b.indexed_families[i];
    CHECK(x.origin_name == y.origin_name && x.members == y.members &&
          x.lo == y.lo && x.hi == y.hi && x.is_output == y.is_output &&
          x.is_enum == y.is_enum);
  }
}

static void value_origins() {
  std::shared_ptr<const TlsfValueOrigins> retained;
  {
    const std::string source = R"(
INFO { SEMANTICS: Moore TARGET: Moore }
GLOBAL {
  PARAMETERS { scale = 3; extra = 1; }
  DEFINITIONS {
    depth(x) = x <= 1 : 0 otherwise : 1 + depth(x / 2);
    width(x) = x == 0 : 0 otherwise : 1 + depth(x - 1);
    term(bus, j) = bus[j];
  }
}
MAIN { INPUTS { Flag; A[width(scale)]; } OUTPUTS { B[width(scale+extra)]; }
       GUARANTEES { &&[0 <= k < width(scale)] G(term(A,k) -> F term(B,k)); } }
)";
    const auto plain = tlsf::convert(source, "Mealy");
    CHECK(!plain.value_origins);
    const auto found = tlsf::convert(source, "Mealy", true);
    same_conversion(plain, found);
    retained = found.value_origins;
    CHECK(retained && retained->complete);
  }
  const auto *input = retained->buses;
  CHECK(input && !input->is_output && input->declaration_id == 2 &&
        input->proved_bit_width && input->dependencies_complete &&
        input->bit_count == 2 && std::strcmp(input->bits[1], "A_1") == 0 &&
        input->parameter_count == 1 && input->parameter_ids[0] == 1);
  const auto *output = input->next;
  CHECK(output && output->is_output && output->declaration_id == 1 &&
        output->proved_bit_width && output->dependencies_complete &&
        output->parameter_count == 2 && output->parameter_ids[0] == 1 &&
        output->parameter_ids[1] == 2 && !output->next);
  const auto *domain = retained->domains;
  CHECK(domain && !domain->next && domain->binder_id && domain->count == 2 &&
        domain->coordinates[0] == 0 && domain->coordinates[1] == 1 &&
        domain->parameter_count == 1 && domain->parameter_ids[0] == 1);
  unsigned seen = 0;
  for (auto *row = retained->instances; row; row = row->next)
    if (row->bindings && tlsf_ast_node_kind(row->expanded) == TLSF_AST_IMPL) {
      CHECK(row->bindings->domain == domain && !row->bindings->outer &&
            row->source_formula_id == domain->source_formula_id &&
            row->source_node_id && row->section == TLSF_VALUE_GUARANTEE);
      const auto *antecedent = tlsf_ast_node_child(row->expanded, 0);
      CHECK(tlsf_ast_node_kind(antecedent) == TLSF_AST_X);
      const auto *ap = tlsf_ast_node_child(antecedent, 0);
      const auto coordinate = row->bindings->coordinate;
      CHECK(coordinate >= 0 && coordinate < domain->count);
      CHECK(std::strcmp(tlsf_ast_node_ap_name(ap), input->bits[coordinate]) ==
            0);
      seen |= 1u << coordinate;
    }
  CHECK(seen == 3);
}

static void exhausted_value_origins() {
  std::string tree = "true";
  for (int depth = 0; depth < 17; ++depth)
    tree = "(" + tree + " && " + tree + ")";
  const std::string source = "INFO { SEMANTICS: Mealy TARGET: Mealy } "
                             "GLOBAL { DEFINITIONS { unused = " +
                             tree +
                             "; } } "
                             "MAIN { OUTPUTS { p; } GUARANTEE { G p; } }";
  const auto plain = tlsf::convert(source, "Mealy");
  const auto exhausted = tlsf::convert(source, "Mealy", true);
  CHECK(!exhausted.value_origins);
  same_conversion(plain, exhausted);
}

static void closed_domain_origins() {
  const std::string source = R"(
INFO { SEMANTICS: Mealy TARGET: Mealy }
GLOBAL { PARAMETERS { scale = 3; }
         DEFINITIONS { terms(limit) = &&[0 <= k < limit] G p[k]; } }
MAIN { OUTPUTS { p[scale]; } GUARANTEE { terms(scale); } }
)";
  const auto captured = tlsf::convert(source, "Mealy", true);
  CHECK(captured.value_origins && !captured.value_origins->complete);
  CHECK(captured.value_origins->domains &&
        captured.value_origins->domains->count == 3);
  same_conversion(tlsf::convert(source, "Mealy"), captured);
}

int main() {
  value_origins();
  exhausted_value_origins();
  closed_domain_origins();
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
