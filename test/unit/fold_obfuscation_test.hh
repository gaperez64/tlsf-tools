#pragma once

#include "tlsf/gr1_lift.h"
#include "yyjson_cpp.hh"
#include <algorithm>
#include <array>
#include <cctype>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace fold_test {
struct Obfuscated {
  std::string bytes;
  std::map<std::string, std::string> names;
};

static Obfuscated obfuscate(const std::string &source) {
  // Keep TLSF keywords, operators and numbers; every other word is a user name.
  const std::set<std::string> keywords = {
      "INFO",       "GLOBAL",     "MAIN",    "TITLE",      "DESCRIPTION",
      "SEMANTICS",  "TARGET",     "TAGS",    "PARAMETERS", "DEFINITIONS",
      "enum",       "INPUTS",     "OUTPUTS", "INITIALLY",  "PRESET",
      "REQUIRE",    "ASSERT",     "ASSUME",  "GUARANTEE",  "ASSUMPTIONS",
      "GUARANTEES", "INVARIANTS", "Strict",  "Finite",     "Mealy",
      "Moore",      "true",       "false",   "SIZEOF",     "SIZE",
      "MIN",        "MAX",        "SUM",     "PROD",       "CUP",
      "CAP",        "SETMINUS",   "FORALL",  "EXISTS",     "IN",
      "ELEM",       "otherwise",  "X",       "F",          "G",
      "U",          "R",          "W",       "NOT",        "AND",
      "OR",         "IMPLIES",    "EQUIV",   "PLUS",       "MINUS",
      "MUL",        "DIV",        "MOD",     "EQ",         "NEQ",
      "LEQ",        "GEQ",        "GEG",     "LE",         "GE"};
  const std::set<std::string> reorder = {
      "PARAMETERS", "INPUTS",     "OUTPUTS",   "ASSUME",    "ASSUMPTIONS",
      "ASSERT",     "INVARIANTS", "GUARANTEE", "GUARANTEES"};
  Obfuscated out;
  std::vector<std::string> tokens;
  unsigned metadata = 0;
  std::string word;
  for (size_t i = 0; i < source.size();) {
    const size_t begin = i;
    if (source.compare(i, 2, "//") == 0) {
      i = source.find('\n', i);
      if (i == std::string::npos)
        i = source.size();
      tokens.emplace_back("\n");
    } else if (source.compare(i, 2, "/*") == 0) {
      i += 2;
      unsigned depth = 1;
      while (depth) {
        CHECK(i < source.size());
        if (source.compare(i, 2, "/*") == 0) {
          ++depth;
          i += 2;
        } else if (source.compare(i, 2, "*/") == 0) {
          --depth;
          i += 2;
        } else
          ++i;
      }
      tokens.emplace_back("\n");
    } else if (source[i] == '"') {
      // shortcut: these fixtures only quote INFO text; extend for quoted TAGS.
      CHECK(word == "TITLE" || word == "DESCRIPTION");
      ++i;
      while (i < source.size() && source[i] != '"') {
        if (source[i] == '\\')
          ++i;
        ++i;
      }
      CHECK(i < source.size());
      ++i;
      ++metadata;
      tokens.emplace_back("\"neutral\"");
    } else if (std::isalpha(static_cast<unsigned char>(source[i])) ||
               source[i] == '_' || source[i] == '@') {
      while (++i < source.size() &&
             (std::isalnum(static_cast<unsigned char>(source[i])) ||
              source[i] == '_' || source[i] == '@' || source[i] == '\'')) {
      }
      word = source.substr(begin, i - begin);
      if (keywords.count(word))
        tokens.push_back(word);
      else {
        const auto entry =
            out.names.emplace(word, "v" + std::to_string(out.names.size()))
                .first;
        CHECK(entry->second != word);
        tokens.push_back(entry->second);
      }
    } else
      tokens.emplace_back(1, source[i++]);
  }
  CHECK(metadata == 2);
  for (size_t i = 0; i < tokens.size(); ++i) {
    out.bytes += tokens[i];
    if (!reorder.count(tokens[i]))
      continue;
    while (++i < tokens.size() && tokens[i] != "{")
      out.bytes += tokens[i];
    CHECK(i < tokens.size());
    out.bytes += "{";
    std::vector<std::string> clauses;
    std::string clause;
    unsigned depth = 0;
    while (++i < tokens.size()) {
      const auto &token = tokens[i];
      if (token == "}" && !depth)
        break;
      if (token == "{" || token == "[" || token == "(")
        ++depth;
      if (token == "}" || token == "]" || token == ")") {
        CHECK(depth);
        --depth;
      }
      clause += token;
      if (token == ";" && !depth) {
        clauses.push_back(clause);
        clause.clear();
      }
    }
    CHECK(i < tokens.size());
    CHECK(std::all_of(clause.begin(), clause.end(),
                      [](unsigned char c) { return std::isspace(c); }));
    // Reversal is fixed; leave binder domains, bus bits and helper cases
    // intact. Parameter fixtures use independent literal values.
    std::reverse(clauses.begin(), clauses.end());
    for (const auto &part : clauses)
      out.bytes += part;
    out.bytes += clause + "}";
  }
  return out;
}

static void obfuscator_check() {
  const auto out =
      obfuscate("INFO { TITLE: \"load balancer\" DESCRIPTION: \"arbiter\" }"
                "/* outer /* idle */ grant */ // elevator\n"
                "GLOBAL { PARAMETERS { n=2; } DEFINITIONS {"
                " a(bus,i,j)=a'(bus,i,j); a'(bus,i,j)=bus[i]; } }"
                "MAIN { INPUTS { a0; a1[n]; } OUTPUTS { b0; b1; }"
                " ASSUMPTIONS { a0; a1[0]; } ASSERT { b0; b1; }"
                " GUARANTEES { a0; a1[0]; } INVARIANTS { b0; b1; } }");
  CHECK(out.names.size() == 10);
  CHECK(out.names.at("a") != out.names.at("a'"));
  const auto a0 = out.names.at("a0"), a1 = out.names.at("a1");
  const auto b0 = out.names.at("b0"), b1 = out.names.at("b1");
  CHECK(out.bytes.find("INPUTS { " + a1 + "[" + out.names.at("n") + "]; " + a0 +
                       "; }") != std::string::npos);
  for (const char *section : {"OUTPUTS", "ASSERT", "INVARIANTS"})
    CHECK(out.bytes.find(std::string(section) + " { " + b1 + "; " + b0 +
                         "; }") != std::string::npos);
  for (const char *section : {"ASSUMPTIONS", "GUARANTEES"})
    CHECK(out.bytes.find(std::string(section) + " { " + a1 + "[0]; " + a0 +
                         "; }") != std::string::npos);
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
  bool multi = false;
  tlsf_json::object fixed;
  for (const auto &seed : fold.at("seeds").as_array()) {
    const auto &row = seed.as_object();
    CHECK(row.at("exact_predicates").as_bool());
    const auto &parameters = row.at("parameters").as_object();
    multi = parameters.size() > 1;
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
  // Legacy discovery intentionally retains main's name-ordered work. On
  // multi-parameter inputs compare the separately budgeted fallback counters.
  seen.counts = {multi ? uint64_t(fold.at("discovery_probes").as_int64())
                       : stats.seed_probes,
                 stats.seeds_selected,
                 stats.seed_solves,
                 stats.seed_latches,
                 stats.seed_ands,
                 stats.target_latches,
                 stats.target_ands,
                 stats.internal_checks};
  if (both) {
    CHECK(evidence.at("route").as_string() == "R");
    seen.counts.insert(
        seen.counts.end(),
        {multi ? uint64_t(fold.at("discovery_probes").as_int64())
               : combined.seed_probes,
         multi ? uint64_t(fold.at("discovery_reductions").as_int64())
               : combined.seed_reductions,
         combined.seed_solves, combined.seed_checks,
         multi ? 0 : combined.seed_cache_hits, combined.target_reductions,
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
  auto add = [&](const char *parameters) {
    auto bytes = source;
    bytes.insert(bytes.find("PARAMETERS {") + strlen("PARAMETERS {"),
                 parameters);
    return bytes;
  };
  // Nbjorner's stress case uses the smaller route B fixture: repeating the
  // larger encoded target in legacy probes would spend its arm deadline.
  if (std::string(generator) == "parametric-support-fold-v1") {
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
  CHECK(original.seeds ==
        (std::string(generator) == "parametric-support-fold-v1"
             ? std::vector<int64_t>{3, 4, 5}
             : std::vector<int64_t>{5, 6, 7}));
  CHECK(original.counts.front() == 5);
  CHECK(original == observe(late, both, "n", 8));
  const auto reordered = obfuscate(early);
  CHECK(original == observe(reordered.bytes, both, reordered.names.at("n"), 8));
}
} // namespace fold_test
