#include "tlsf/decompose.hpp"

#include <iostream>

int main() {
  const std::string spec = R"TLSF(
INFO { TITLE: "normalization" SEMANTICS: Mealy TARGET: Mealy }
MAIN { INPUTS { i; } OUTPUTS { o; } GUARANTEE { G (!i || F o); } }
)TLSF";
  const auto original = tlsf::decompose(spec);
  tlsf::Options options;
  options.normalization_schedule = "match-safe:1";
  options.normalization_phase = TLSF_NORM_PHASE_MATCH;
  const auto normalized = tlsf::decompose(spec, options);
  if (original.preprocessed_ltl == normalized.preprocessed_ltl ||
      !normalized.normalization_changed ||
      normalized.normalization_schedule != "weak,bool-canon,or-to-impl-pattern,"
                                           "equiv-output-side,mutex-demorgan" ||
      !normalized.normalization_nodes_before ||
      !normalized.normalization_nodes_after ||
      normalized.normalization_bounds_rejected ||
      original.clusters.size() != normalized.clusters.size())
    return 1;
  for (size_t i = 0; i < original.clusters.size(); ++i)
    if (original.clusters[i].ltl != normalized.clusters[i].ltl)
      return 1;
  options.normalization_max_nodes = 1;
  const auto bounded = tlsf::decompose(spec, options);
  if (!bounded.normalization_bounds_rejected || bounded.normalization_changed ||
      bounded.preprocessed_ltl != original.preprocessed_ltl)
    return 1;
  for (const char *bad : {"invalid-schedule", "pre-safe"}) {
    options.normalization_schedule = bad;
    try {
      (void)tlsf::decompose(spec, options);
      std::cerr << "accepted invalid normalization: " << bad << '\n';
      return 1;
    } catch (const std::runtime_error &) {
    }
  }
  options.overwrite_semantics = "Finite,Mealy";
  options.normalization_schedule = "sickert-stage2";
  try {
    (void)tlsf::decompose(spec, options);
    std::cerr << "accepted infinite-only normalization on finite semantics\n";
    return 1;
  } catch (const std::runtime_error &) {
  }
  options.overwrite_semantics.clear();
  options.normalization_schedule.clear();
  const auto unchanged = tlsf::decompose(spec, options);
  if (unchanged.preprocessed_ltl != original.preprocessed_ltl ||
      !unchanged.normalization_schedule.empty() ||
      unchanged.normalization_nodes_before || unchanged.normalization_time_ns)
    return 1;
  return 0;
}
