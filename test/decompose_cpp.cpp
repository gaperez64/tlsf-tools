#include "tlsf/decompose.hpp"

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
  return 0;
}
