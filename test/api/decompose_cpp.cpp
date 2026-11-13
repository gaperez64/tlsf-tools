#include "tlsf/decompose.hpp"
#include "tlsf/ast_api.hpp"

#include "../check.h"
#include <stdexcept>
#include <string>

static bool contains(const std::vector<std::string> &xs, const char *needle) {
  for (const std::string &x : xs)
    if (x == needle)
      return true;
  return false;
}

int main() {
  const std::string trivial = R"TLSF(
INFO { TITLE: "precheck" SEMANTICS: Mealy TARGET: Mealy }
MAIN { INPUTS { i; } OUTPUTS { o; } GUARANTEE { G o; } }
)TLSF";
  // Conversion is independent of the availability of the optional verdict.
  auto conversion = tlsf::decompose(trivial);
  CHECK(conversion.verdict == tlsf::Verdict::Unknown);
  CHECK(conversion.verdict_trust == tlsf::Trust::None);
  tlsf::Options checked;
  checked.precheck = true;
  auto prechecked = tlsf::decompose(trivial, checked);
  CHECK(prechecked.verdict == tlsf::Verdict::Realizable);
  CHECK(prechecked.verdict_trust == tlsf::Trust::Under);
  CHECK(conversion.preprocessed_ltl == prechecked.preprocessed_ltl);
  tlsf::ast::Ast converted_ast(trivial);
  CHECK(converted_ast.result().verdict == tlsf::Verdict::Unknown);
  tlsf::ast::Ast checked_ast(trivial, checked);
  CHECK(checked_ast.result().verdict == tlsf::Verdict::Realizable);

  const std::string spec = R"TLSF(
INFO {
  TITLE: "decompose_cpp"
  SEMANTICS: Mealy
  TARGET: Mealy
}
MAIN {
  INPUTS { a; b; }
  OUTPUTS { x; y; }
  GUARANTEE {
    G (x <-> X a);
    G (y <-> X b);
  }
}
)TLSF";

  tlsf::Options options;
  options.split = true;
  tlsf::Result result = tlsf::decompose(spec, options);

  CHECK(result.clusters.size() == 2);
  CHECK(result.inputs.size() == 2);
  CHECK(result.outputs.size() == 2);
  CHECK(contains(result.inputs, "a"));
  CHECK(contains(result.inputs, "b"));
  CHECK(contains(result.outputs, "x"));
  CHECK(contains(result.outputs, "y"));
  CHECK(result.verdict == tlsf::Verdict::Unknown);
  CHECK(result.residual_trust == tlsf::Trust::Exact);
  CHECK(result.semantics == "Mealy");
  CHECK(result.target == "Mealy");

  for (const tlsf::Cluster &cluster : result.clusters) {
    CHECK(cluster.outputs.size() == 1);
    CHECK(!cluster.ltl.empty());
  }

  const std::string converted = R"TLSF(
INFO {
  TITLE: "decompose_cpp_target_adaptation"
  SEMANTICS: Mealy
  TARGET: Moore
}
MAIN {
  INPUTS { req; }
  OUTPUTS { grant; }
  GUARANTEE { G (req -> grant); }
}
)TLSF";
  options.split = false;
  options.format = tlsf::Format::Ltl;
  result = tlsf::decompose(converted, options);
  CHECK(result.semantics == "Mealy");
  CHECK(result.target == "Moore");
  CHECK(result.preprocessed_ltl == "G (req -> X grant)");

  for (const char *semantics : {"Moore", "Moore,Strict"}) {
    const std::string implicit =
        "INFO { SEMANTICS: " + std::string(semantics) +
        " TARGET: Mealy } MAIN { OUTPUTS { p; } GUARANTEE { G(p <-> u); } }";
    bool rejected_free = false;
    try {
      (void)tlsf::decompose(implicit);
    } catch (const std::runtime_error &) {
      rejected_free = true;
    }
    CHECK(rejected_free); // TLSF v1.1 §§4.1–4.3: u needs a declaration.
    std::string declared = implicit;
    declared.insert(declared.find("OUTPUTS"), "INPUTS { u; } ");
    auto adapted = tlsf::decompose(declared);
    CHECK(adapted.preprocessed_ltl == "G (p <-> X u)");
    CHECK(adapted.residual_trust == tlsf::Trust::Exact);
    CHECK(adapted.clusters.size() == 1);
    CHECK(adapted.clusters[0].ltl == "G (p <-> X u)");
    CHECK(adapted.clusters[0].inputs == std::vector<std::string>({"u"}));
    CHECK(adapted.clusters[0].outputs == std::vector<std::string>({"p"}));
  }

  const std::string case_sensitive = R"TLSF(
INFO { TITLE: "case" SEMANTICS: Mealy TARGET: Mealy }
MAIN {
  INPUTS { Foo; foo; GATE; }
  OUTPUTS { Grant; }
  GUARANTEE { G (GATE -> (Foo <-> foo)); }
}
)TLSF";
  options.lowercase = false;
  result = tlsf::decompose(case_sensitive, options);
  CHECK(contains(result.inputs, "Foo"));
  CHECK(contains(result.inputs, "foo"));
  CHECK(contains(result.inputs, "GATE"));

  options.lowercase = true;
  bool rejected_collision = false;
  try {
    (void)tlsf::decompose(case_sensitive, options);
  } catch (const std::runtime_error &) {
    rejected_collision = true;
  }
  CHECK(rejected_collision);

  for (const char *semantics :
       {"Mealy", "Moore", "Mealy,Strict", "Moore,Strict", "Mealy,Finite",
        "Moore,Finite"}) {
    const std::string target =
        std::string(semantics).starts_with("Moore") ? "Moore" : "Mealy";
    const std::string header = "INFO { SEMANTICS: " + std::string(semantics) +
                               " TARGET: " + target + " } MAIN { ";
    const std::string implicit =
        header + "INPUTS { q; Q; } OUTPUTS { p; } "
                 "ASSUMPTIONS { G(q <-> !Q); } GUARANTEES { false; } }";
    options.lowercase = false;
    result = tlsf::decompose(implicit, options);
    CHECK(result.preprocessed_ltl == "G (q <-> !Q) -> false");
    CHECK(result.residual_trust == tlsf::Trust::Exact);
    CHECK(contains(result.inputs, "q") && contains(result.inputs, "Q"));
    CHECK(result.clusters.size() == 1);
    CHECK(result.clusters[0].ltl == "G (q <-> !Q) -> false");
    options.lowercase = true;
    TlsfDecomposeOptions c_options = {};
    c_options.lowercase = true;
    for (const char *declaration :
         {"", "INPUTS { q; }", "OUTPUTS { q; }", "INPUTS { q; Q; }",
          "INPUTS { q; } OUTPUTS { Q; }"})
      for (const char *role : {"INITIALLY", "PRESET", "REQUIRE", "ASSERT",
                               "ASSUMPTIONS", "GUARANTEES"}) {
        const std::string source =
            header + declaration + " " + role + " { q <-> Q; } }";
        CHECK(!tlsf_decompose_string(source.c_str(), &c_options));
        CHECK(!tlsf_ast_from_string(source.c_str(), &c_options));
        rejected_collision = false;
        try {
          (void)tlsf::decompose(source, options);
        } catch (const std::runtime_error &) {
          rejected_collision = true;
        }
        CHECK(rejected_collision);
      }
  }

  // ltl2ba and ltl3ba silently truncate a formula at ' or @.
  const std::string primed = R"TLSF(
INFO { TITLE: "primed" SEMANTICS: Mealy TARGET: Mealy }
MAIN {
  INPUTS { req'; }
  OUTPUTS { grant@1; }
  GUARANTEE { G (req' -> grant@1); }
}
)TLSF";
  options.lowercase = false;
  options.format = tlsf::Format::Ltlxba;
  bool rejected_ltlxba = false;
  try {
    (void)tlsf::decompose(primed, options);
  } catch (const std::runtime_error &) {
    rejected_ltlxba = true;
  }
  CHECK(rejected_ltlxba);
  options.format = tlsf::Format::Ltl;
  result = tlsf::decompose(primed, options);
  CHECK(result.preprocessed_ltl == "G (req' -> grant@1)");

  const std::string indexed = R"TLSF(
INFO { TITLE: "indexed" SEMANTICS: Mealy TARGET: Mealy }
GLOBAL { PARAMETERS { n = 3; } }
MAIN {
  INPUTS { Req[n]; }
  OUTPUTS { Grant[n]; }
  GUARANTEE { &&[0 <= i < n] G (Req[i] -> Grant[i]); }
}
)TLSF";
  options.lowercase = false;
  result = tlsf::decompose(indexed, options);
  CHECK(result.indexed_families.size() == 2);
  CHECK(result.indexed_families[0].origin_name == "Req");
  CHECK(result.indexed_families[0].members ==
        std::vector<std::string>({"Req_0", "Req_1", "Req_2"}));
  CHECK(result.indexed_families[0].lo == 0);
  CHECK(result.indexed_families[0].hi == 2);
  CHECK(!result.indexed_families[0].is_output);
  CHECK(!result.indexed_families[0].is_enum);
  CHECK(result.indexed_families[1].origin_name == "Grant");
  CHECK(result.indexed_families[1].members ==
        std::vector<std::string>({"Grant_0", "Grant_1", "Grant_2"}));
  CHECK(result.indexed_families[1].is_output);
  CHECK(!result.indexed_families[1].is_enum);

  const std::string enum_typed = R"TLSF(
INFO { TITLE: "enum" SEMANTICS: Mealy TARGET: Mealy }
GLOBAL {
  DEFINITIONS { enum Mode = Idle: 00 Active: 01 Done: 10; }
}
MAIN {
  INPUTS { Mode State; }
  OUTPUTS { ok; }
  GUARANTEE { G ok; }
}
)TLSF";
  options.lowercase = true;
  result = tlsf::decompose(enum_typed, options);
  CHECK(result.indexed_families.size() == 1);
  CHECK(result.indexed_families[0].origin_name == "state");
  CHECK(result.indexed_families[0].is_enum);
  CHECK(result.preprocessed_ltl.find(
            "G (!state_0 && !state_1 || !state_0 && state_1 || state_0 && "
            "!state_1)") != std::string::npos);

  const std::string enum_wildcards = R"TLSF(
INFO { TITLE: "enum wildcards" SEMANTICS: Strict,Mealy TARGET: Mealy }
GLOBAL {
  DEFINITIONS { enum Mode = Low: 00,01 High: 1*; }
}
MAIN {
  INPUTS { Mode request; }
  OUTPUTS { Mode response; }
  REQUIRE { request == Low; }
  ASSERT { response == High; }
  GUARANTEE { G (request == Low -> response == High); }
}
)TLSF";
  result = tlsf::decompose(enum_wildcards, options);
  CHECK(result.semantics == "Strict,Mealy");
  CHECK(result.preprocessed_ltl.find("request_0") != std::string::npos);
  CHECK(result.preprocessed_ltl.find("response_0") != std::string::npos);
  CHECK(result.preprocessed_ltl.find(" W ") != std::string::npos);
  return 0;
}
