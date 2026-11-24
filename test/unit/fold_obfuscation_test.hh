#pragma once

#include "tlsf/gr1_lift.h"
#include "tlsf/obfuscate.h"
#include "yyjson_cpp.hh"
#include <array>
#include <cctype>
#include <map>
#include <sstream>
#include <string>
#include <vector>

namespace fold_test {
struct Obfuscated {
  std::string bytes;
  std::map<std::string, std::string> names;
};

static Obfuscated obfuscate(const std::string &source, uint64_t seed = 11) {
  TlsfObfuscateOptions options{};
  options.mode = TLSF_OBFUSCATE_RENAME | TLSF_OBFUSCATE_REORDER;
  options.seed = seed;
  TlsfObfuscateResult result{};
  const auto status =
      tlsf_obfuscate(source.data(), source.size(), &options, &result);
  if (status != TLSF_OBFUSCATE_OK)
    std::fprintf(stderr, "tlsf_obfuscate: %s\n", result.message);
  CHECK(status == TLSF_OBFUSCATE_OK);
  Obfuscated out{std::string(result.text, result.size), {}};
  for (size_t i = 0; i < result.entry_count; ++i) {
    const auto &entry = result.entries[i];
    if (entry.kind == TLSF_OBFUSCATE_INPUT_SIGNAL ||
        entry.kind == TLSF_OBFUSCATE_OUTPUT_SIGNAL)
      continue;
    const auto *name =
        tlsf_obfuscate_lookup(&result, entry.original, entry.kind);
    CHECK(name);
    out.names.emplace(entry.original, name);
  }
  tlsf_obfuscate_result_clear(&result);
  return out;
}

static void obfuscator_check() {
  // Seed 326 reverses declarations and clauses, including the merged aliases.
  const auto out =
      obfuscate("INFO { TITLE: \"load balancer\" DESCRIPTION: \"arbiter\" }"
                "/* outer /* idle */ grant */ // elevator\n"
                "GLOBAL { PARAMETERS { n=2; } DEFINITIONS {"
                " a(bus,i,j)=a'(bus,i,j); a'(bus,i,j)=bus[i]; } }"
                "MAIN { INPUTS { a0; a1[n]; } OUTPUTS { b0; b1; }"
                " ASSUMPTIONS { a0; a1[0]; } ASSERT { b0; b1; }"
                " GUARANTEES { a0; a1[0]; } INVARIANTS { b0; b1; } }",
                326);
  CHECK(out.names.size() == 10);
  CHECK(out.names.at("a") != out.names.at("a'"));
  const auto a0 = out.names.at("a0"), a1 = out.names.at("a1");
  const auto b0 = out.names.at("b0"), b1 = out.names.at("b1");
  auto compact = out.bytes;
  std::erase_if(compact, [](unsigned char c) { return std::isspace(c); });
  CHECK(compact.find("INPUTS{" + a1 + "[0..(" + out.names.at("n") + "-1)];" +
                     a0 + ";}") != std::string::npos);
  CHECK(compact.find("OUTPUTS{" + b1 + ";" + b0 + ";}") != std::string::npos);
  // The printer combines ASSERT and its INVARIANTS alias into one section.
  CHECK(compact.find("ASSERT{" + b1 + ";" + b0 + ";" + b1 + ";" + b0 + ";}") !=
        std::string::npos);
  for (const char *section : {"ASSUME", "GUARANTEE"})
    CHECK(compact.find(std::string(section) + "{" + a1 + "[0];" + a0 + ";}") !=
          std::string::npos);
  CHECK(out.bytes.find("load") == std::string::npos);
  CHECK(out.bytes.find("arbiter") == std::string::npos);
  CHECK(out.bytes.find("//") == std::string::npos);
  CHECK(out.bytes.find("/*") == std::string::npos);
}

struct Observation {
  TlsfGr1LiftStatus status;
  TlsfGr1CheckVerdict verdict;
  TlsfGr1BothRoute route;
  std::string generator, order;
  std::vector<int64_t> seeds;
  std::vector<uint64_t> counts;
  uint64_t seed_solves = 0;
  std::array<uint64_t, 4> game;
  bool operator==(const Observation &) const = default;
};

static Observation observe(const std::string &bytes, bool both,
                           const std::string &axis = "n",
                           uint64_t max_probes = 0) {
  // Match native_gr1_lift_arm.cc: default R/U routing, capacities and arity.
  TlsfGr1LiftStats stats{};
  TlsfGr1LiftOptions o{};
  o.deadline_mono_ns = deadline(50);
  o.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  o.env_candidate_ns = 12000000000ull;
  o.budget.max_formula_nodes = 4096;
  o.budget.max_ap_count = 2048;
  o.budget.max_conjuncts = o.budget.max_conjunct_nodes = 1024;
  o.budget.max_temporal_depth = 16;
  o.budget.max_predicted_monitor_states = 1u << 24;
  o.budget.max_total_states = 10000;
  o.budget.max_total_edges = 150000;
  o.budget.max_rss_bytes = uint64_t(5) << 29;
  o.env_budget.max_rss_bytes = o.budget.max_rss_bytes;
  o.stats = &stats;
  o.phase_budget.max_seed_probes = max_probes;
  auto prepare = o;
  prepare.max_artifact_bytes = 64u << 20;
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError e{};
  // The byte API has no pathname: the transformed source has only neutral text.
  CHECK(tlsf_gr1_lift_target_prepare_exact_v1((const uint8_t *)bytes.data(),
                                              bytes.size(), &prepare, &target,
                                              &e, nullptr) == TLSF_GR1_LIFT_OK);
  TlsfGr1LiftResult solo{};
  TlsfGr1BothResult combined{};
  const TlsfGr1BothOptionsV2 routing{&o, nullptr, 0};
  Observation seen{};
  seen.status =
      both ? tlsf_gr1_both_from_target_v2(target, &routing, &combined, &e)
           : tlsf_gr1_lift_from_target(target, &o, &solo, &e);
  auto &r = both ? combined.proof : solo;
  if (seen.status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "obfuscated (%d): %s: %s; %s\n", both, e.stage,
                 e.message,
                 both ? combined.decline_detail : solo.decline_detail);
  CHECK(seen.status == TLSF_GR1_LIFT_OK);
  seen.verdict = r.verdict;
  CHECK(seen.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  CHECK(r.method == TLSF_GR1_CHECK_REGION);
  CHECK(tlsf_gr1_lift_target_matches(target, &r));
  const auto evidence =
      tlsf_json::parse(std::string_view(r.evidence_json, r.evidence_size))
          .as_object();
  const auto &fold = evidence.at("fold").as_object();
  seen.generator = fold.at("generator").as_string();
  seen.order = evidence.at("checker_order").as_string();
  tlsf_json::object fixed;
  for (const auto &seed : fold.at("seeds").as_array()) {
    const auto &row = seed.as_object();
    CHECK(row.at("exact_predicates").as_bool());
    const auto &parameters = row.at("parameters").as_object();
    seen.seeds.push_back(parameters.at(axis).as_int64());
    auto remaining = parameters;
    std::erase_if(remaining,
                  [&](const auto &entry) { return entry.first == axis; });
    if (seen.seeds.size() == 1)
      fixed = remaining;
    CHECK(tlsf_json::serialize(remaining) == tlsf_json::serialize(fixed));
  }
  if (!both) {
    CHECK(evidence.at("axis").as_string().size());
    const auto &values = evidence.at("seed_values").as_array();
    CHECK(values.size() == seen.seeds.size());
    for (size_t i = 0; i < values.size(); ++i)
      CHECK(values[i].as_int64() == seen.seeds[i]);
  }
  seen.route = both ? combined.route : TLSF_GR1_BOTH_REAL_LIFT;
  CHECK(seen.route == TLSF_GR1_BOTH_REAL_LIFT);
  seen.seed_solves = both ? combined.seed_solves : stats.seed_solves;
  seen.counts = {uint64_t(fold.at("discovery_probes").as_int64()),
                 stats.seed_probes,
                 stats.seeds_selected,
                 stats.seed_solves,
                 stats.seed_latches,
                 stats.seed_ands,
                 stats.target_latches,
                 stats.target_ands,
                 stats.internal_checks};
  if (both) {
    CHECK(evidence.at("route").as_string() == "R");
    seen.counts.insert(seen.counts.end(),
                       {combined.seed_probes, combined.seed_reductions,
                        combined.seed_solves, combined.seed_checks,
                        combined.seed_cache_hits, combined.target_reductions,
                        combined.target_checks});
  }
  // Declaration/clause permutations change AAG numbering and monitor order;
  // compare I/L/A/O counts plus REGION_VERIFIED, rather than serialized bytes.
  std::istringstream header(std::string(r.game_aag, r.game_size));
  std::string magic;
  uint64_t maximum = 0;
  header >> magic >> maximum >> seen.game[0] >> seen.game[1] >> seen.game[3] >>
      seen.game[2];
  CHECK(header.good() && magic == "aag");
  tlsf_gr1_lift_result_clear(&solo);
  tlsf_gr1_both_result_clear(&combined);
  tlsf_gr1_lift_target_free(target);
  return seen;
}

static void obfuscation_regression(const std::string &bytes, bool both,
                                   const char *generator,
                                   const std::string &axis = "n") {
  obfuscator_check();
  const auto transformed = obfuscate(bytes);
  CHECK(transformed.bytes == obfuscate(bytes).bytes);
  const auto original = observe(bytes, both, axis);
  CHECK(original.generator == generator);
  CHECK(original ==
        observe(transformed.bytes, both, transformed.names.at(axis)));
}
static std::string rename_identifier(std::string bytes, const std::string &from,
                                     const std::string &to) {
  // shortcut: tlsf_obfuscate cannot choose literal a/z names or insert the
  // ambiguous-axis expression; keep token replacement only for those fixtures.
  auto identifier = [](unsigned char c) {
    return std::isalnum(c) || c == '_' || c == '@' || c == '\'';
  };
  for (size_t p = 0; (p = bytes.find(from, p)) != std::string::npos;) {
    if ((!p || !identifier(bytes[p - 1])) &&
        (p + from.size() == bytes.size() ||
         !identifier(bytes[p + from.size()]))) {
      bytes.replace(p, from.size(), to);
      p += to.size();
    } else
      p += from.size();
  }
  return bytes;
}

static void axis_regressions(const std::string &source, bool both,
                             const char *generator) {
  const bool parametric =
      std::string(generator) == "parametric-support-fold-v1";
  auto add = [&](const char *parameters) {
    auto bytes = source;
    bytes.insert(bytes.find("PARAMETERS {") + strlen("PARAMETERS {"),
                 parameters);
    return bytes;
  };
  // Nbjorner's stress case uses the smaller route B fixture: repeating the
  // larger encoded target would spend its arm deadline.
  if (parametric) {
    const auto four = add(" a0=7; a1=7; a2=7; a3=7;");
    const auto original = observe(four, both);
    CHECK(original.generator == generator);
    CHECK(original.seeds == std::vector<int64_t>({3, 4, 5}));
    CHECK(original.counts.front() == 5);
    CHECK(original == observe(rename_identifier(four, "n", "a"), both, "a"));
    obfuscation_regression(four, both, generator);
  }
  // Barbosa: one irrelevant probe formerly changed 7 to 10 total probes,
  // preventing route B from reaching 3/4/5 with a limit of eight.
  const auto early = add(" a=2;");
  const auto late = rename_identifier(early, "a", "z");
  const auto original = observe(early, both, "n", 8);
  CHECK(original.generator == generator);
  CHECK(original.seeds == (parametric ? std::vector<int64_t>{3, 4, 5}
                                      : std::vector<int64_t>{5, 6, 7}));
  CHECK(original.counts.front() == 5);
  CHECK(original == observe(late, both, "n", 8));
  const auto reordered = obfuscate(early);
  CHECK(original == observe(reordered.bytes, both, reordered.names.at("n"), 8));
}
} // namespace fold_test
