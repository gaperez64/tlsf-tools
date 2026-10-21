#include "tlsf/convert.hpp"

#include <cassert>
#include <cstring>

int main() {
  TlsfConversionResult *owned;
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
  tlsf_conversion_result_free(owned);
  tlsf_conversion_result_free(nullptr);
  assert(!tlsf_convert(nullptr, "Mealy"));
}
