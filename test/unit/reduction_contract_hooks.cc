// Linked only into fault-test executables, ahead of the installed library.
#include <tlsf/gr1_reduction.h>
#include <tlsf/gr1_oxidd.h>
#include <tlsf/spec.h>
#include "yyjson_cpp.hh"
#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

// Run the actual validator's null rejection without replacing its checks.
#define tlsf_gr1_validate_game contract_original_validate_game
#include "../../src/lib/gr1_service.c"
#undef tlsf_gr1_validate_game

static bool mode(const char *value) {
  const char *selected = std::getenv("ACACIA_NATIVE_TEST_CONTRACT");
  return selected && std::strcmp(selected, value) == 0;
}
extern "C" bool tlsf_gr1_validate_game(const Aig *game, char *why,
                                       size_t size) {
  static bool rejected = false;
  if (mode("seed-null") && !rejected) {
    rejected = true;
    return contract_original_validate_game(nullptr, why, size);
  }
  return contract_original_validate_game(game, why, size);
}
void reduction_test_source(const TlsfSpec *spec) {
  if (mode("source-duplicate") && spec->input_count > 1)
    spec->inputs[1].name = spec->inputs[0].name;
}
char reduction_test_class(char klass, TlsfGr1ReductionSemantics semantics) {
  if (mode("unsupported-class") ||
      (mode("provenance-retry") && semantics == TLSF_GR1_STRICT))
    return 'X';
  return klass;
}
void reduction_test_rejecting(std::vector<bool> &rejecting) {
  if (mode("monitor-sticky") && rejecting.size() > 1) {
    std::fill(rejecting.begin(), rejecting.end(), false);
    rejecting[0] = true;
  }
}
void reduction_test_provenance(TlsfGr1Reduction *out,
                               TlsfGr1ReductionSemantics semantics) {
  if (!mode("provenance-duplicate") && !mode("provenance-retry") &&
      !(mode("provenance-recover") && semantics == TLSF_GR1_EXACT))
    return;
  auto json = tlsf_json::parse(
      std::string_view(out->provenance_json, out->provenance_size));
  auto &inputs = json.as_object().at("inputs").as_array();
  if (inputs.size() < 2)
    std::abort();
  inputs[1].as_object()["name"] = inputs[0].as_object().at("name");
  auto text = tlsf_json::serialize(json);
  std::free(out->provenance_json);
  out->provenance_json = ::strdup(text.c_str());
  out->provenance_size = text.size();
}
