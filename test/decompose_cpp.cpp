#include "tlsf/decompose.hpp"

#include <cassert>
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
  return 0;
}
