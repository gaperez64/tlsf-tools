// Linked only into fault-test executables, ahead of the installed library.
#include <tlsf/gr1_reduction.h>
#include <tlsf/gr1_oxidd.h>
#include <tlsf/spec.h>
#include "yyjson_cpp.hh"
#include <spot/twa/twagraph.hh>
#include <spot/tl/formula.hh>
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
void reduction_test_monitor(const char *stage, spot::twa_graph_ptr &aut) {
  if (!std::strcmp(stage, "complete")) {
    if (mode("monitor-incomplete"))
      aut->kill_state(0);
    if (mode("monitor-nondeterministic")) {
      aut->new_edge(0, 0, bddtrue);
      aut->new_edge(0, aut->num_states() - 1, bddtrue);
    }
  } else {
    if (mode("monitor-empty"))
      aut->kill_state(0);
    if (mode("monitor-acceptance")) {
      for (unsigned state = 0; state < aut->num_states(); ++state) {
        unsigned count = 0;
        for (auto &edge : aut->out(state))
          edge.acc =
              count++ ? spot::acc_cond::mark_t{} : spot::acc_cond::mark_t{0};
        if (count > 1)
          break;
      }
    }
  }
}
void reduction_test_rejecting(std::vector<bool> &rejecting) {
  if (mode("monitor-sticky") && rejecting.size() > 1) {
    std::fill(rejecting.begin(), rejecting.end(), false);
    rejecting[0] = true;
  }
}
void reduction_test_formula(const char *stage, spot::formula &formula) {
  if ((!std::strcmp(stage, "source") && mode("formula-ap")) ||
      (!std::strcmp(stage, "transition") && mode("transition-ap")))
    formula = spot::formula::ap("undeclared_contract_ap");
  if ((!std::strcmp(stage, "transition") && mode("transition-temporal")) ||
      (!std::strcmp(stage, "symmetric-body") && mode("provenance-boolean")))
    formula = spot::formula::X(spot::formula::ap("contract_temporal_ap"));
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
