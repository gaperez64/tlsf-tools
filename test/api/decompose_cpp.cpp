#include "tlsf/decompose.hpp"
#include "tlsf/ast_api.hpp"

#include <cassert>
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
  assert(conversion.verdict == tlsf::Verdict::Unknown);
  assert(conversion.verdict_trust == tlsf::Trust::None);
  tlsf::Options checked;
  checked.precheck = true;
  auto prechecked = tlsf::decompose(trivial, checked);
  assert(prechecked.verdict == tlsf::Verdict::Realizable);
  assert(prechecked.verdict_trust == tlsf::Trust::Under);
  assert(conversion.preprocessed_ltl == prechecked.preprocessed_ltl);
  tlsf::ast::Ast converted_ast(trivial);
  assert(converted_ast.result().verdict == tlsf::Verdict::Unknown);
  tlsf::ast::Ast checked_ast(trivial, checked);
  assert(checked_ast.result().verdict == tlsf::Verdict::Realizable);

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

  assert(result.clusters.size() == 2);
  assert(result.inputs.size() == 2);
  assert(result.outputs.size() == 2);
  assert(contains(result.inputs, "a"));
  assert(contains(result.inputs, "b"));
  assert(contains(result.outputs, "x"));
  assert(contains(result.outputs, "y"));
  assert(result.verdict == tlsf::Verdict::Unknown);
  assert(result.residual_trust == tlsf::Trust::Exact);
  assert(result.semantics == "Mealy");
  assert(result.target == "Mealy");

  for (const tlsf::Cluster &cluster : result.clusters) {
    assert(cluster.outputs.size() == 1);
    assert(!cluster.ltl.empty());
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
  assert(result.semantics == "Mealy");
  assert(result.target == "Moore");
  assert(result.preprocessed_ltl == "G (req -> X grant)");

  for (const char *semantics : {"Moore", "Moore,Strict"}) {
    const std::string implicit =
        "INFO { SEMANTICS: " + std::string(semantics) +
        " TARGET: Mealy } MAIN { OUTPUTS { p; } GUARANTEE { G(p <-> u); } }";
    auto adapted = tlsf::decompose(implicit);
    assert(adapted.preprocessed_ltl == "G (p <-> X u)");
    assert(adapted.residual_trust == tlsf::Trust::Exact);
    assert(adapted.clusters.size() == 1);
    assert(adapted.clusters[0].ltl == "G (p <-> X u)");
    assert(adapted.clusters[0].inputs == std::vector<std::string>({"u"}));
    assert(adapted.clusters[0].outputs == std::vector<std::string>({"p"}));
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
  assert(contains(result.inputs, "Foo"));
  assert(contains(result.inputs, "foo"));
  assert(contains(result.inputs, "GATE"));

  options.lowercase = true;
  bool rejected_collision = false;
  try {
    (void)tlsf::decompose(case_sensitive, options);
  } catch (const std::runtime_error &) {
    rejected_collision = true;
  }
  assert(rejected_collision);

  for (const char *semantics :
       {"Mealy", "Moore", "Mealy,Strict", "Moore,Strict", "Mealy,Finite",
        "Moore,Finite"}) {
    const std::string target =
        std::string(semantics).starts_with("Moore") ? "Moore" : "Mealy";
    const std::string header = "INFO { SEMANTICS: " + std::string(semantics) +
                               " TARGET: " + target + " } MAIN { ";
    const std::string implicit =
        header + "OUTPUTS { p; } "
                 "ASSUMPTIONS { G(q <-> !Q); } GUARANTEES { false; } }";
    options.lowercase = false;
    result = tlsf::decompose(implicit, options);
    assert(result.preprocessed_ltl == "G (q <-> !Q) -> false");
    assert(result.residual_trust == tlsf::Trust::Exact);
    assert(contains(result.inputs, "q") && contains(result.inputs, "Q"));
    assert(result.clusters.size() == 1);
    assert(result.clusters[0].ltl == "G (q <-> !Q) -> false");
    options.lowercase = true;
    TlsfDecomposeOptions c_options = {};
    c_options.lowercase = true;
    for (const char *declaration : {"", "INPUTS { q; }", "OUTPUTS { q; }"})
      for (const char *role : {"INITIALLY", "PRESET", "REQUIRE", "ASSERT",
                               "ASSUMPTIONS", "GUARANTEES"}) {
        const std::string source =
            header + declaration + " " + role + " { q <-> Q; } }";
        assert(!tlsf_decompose_string(source.c_str(), &c_options));
        assert(!tlsf_ast_from_string(source.c_str(), &c_options));
        rejected_collision = false;
        try {
          (void)tlsf::decompose(source, options);
        } catch (const std::runtime_error &) {
          rejected_collision = true;
        }
        assert(rejected_collision);
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
  assert(rejected_ltlxba);
  options.format = tlsf::Format::Ltl;
  result = tlsf::decompose(primed, options);
  assert(result.preprocessed_ltl == "G (req' -> grant@1)");

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
  assert(result.indexed_families.size() == 2);
  assert(result.indexed_families[0].origin_name == "Req");
  assert(result.indexed_families[0].members ==
         std::vector<std::string>({"Req_0", "Req_1", "Req_2"}));
  assert(result.indexed_families[0].lo == 0);
  assert(result.indexed_families[0].hi == 2);
  assert(!result.indexed_families[0].is_output);
  assert(!result.indexed_families[0].is_enum);
  assert(result.indexed_families[1].origin_name == "Grant");
  assert(result.indexed_families[1].members ==
         std::vector<std::string>({"Grant_0", "Grant_1", "Grant_2"}));
  assert(result.indexed_families[1].is_output);
  assert(!result.indexed_families[1].is_enum);

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
  assert(result.indexed_families.size() == 1);
  assert(result.indexed_families[0].origin_name == "state");
  assert(result.indexed_families[0].is_enum);
  assert(result.preprocessed_ltl.find(
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
  assert(result.semantics == "Strict,Mealy");
  assert(result.preprocessed_ltl.find("request_0") != std::string::npos);
  assert(result.preprocessed_ltl.find("response_0") != std::string::npos);
  assert(result.preprocessed_ltl.find(" W ") != std::string::npos);
  return 0;
}
