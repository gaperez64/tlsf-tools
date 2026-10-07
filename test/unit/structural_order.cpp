#include <tlsf/gr1_check.h>
#include <tlsf/gr1_oxidd.h>
#include <tlsf/gr1_reduction.h>
#include <tlsf/pipeline.h>
#include <tlsf/structural_order.h>
#include "yyjson_cpp.hh"

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <numeric>
#include <set>
#include <string>
#include <vector>

namespace j = tlsf_json;
using AigPtr = std::unique_ptr<Aig, decltype(&aig_free)>;

AigPtr parse(const char *bytes, size_t size) {
  auto stream = fmemopen(const_cast<char *>(bytes), size, "r");
  assert(stream);
  AigPtr result(aig_read_aag(stream), aig_free);
  fclose(stream);
  assert(result);
  return result;
}
struct Proof {
  std::array<char *, 4> bytes{};
  std::array<size_t, 4> sizes{};
  int unreal = -1;
  ~Proof() {
    for (auto b : bytes)
      free(b);
  }
};
void solve(const TlsfGr1Reduction &game, TlsfStructuralOrder order,
           Proof &proof, bool old_api = false) {
  auto copy = parse(game.aag, game.aag_size);
  Gr1CertificateOptions cert{};
  cert.semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
  cert.aag_bytes = &proof.bytes[0];
  cert.json_bytes = &proof.bytes[1];
  cert.policy_aag_bytes = &proof.bytes[2];
  cert.policy_json_bytes = &proof.bytes[3];
  cert.aag_size = &proof.sizes[0];
  cert.json_size = &proof.sizes[1];
  cert.policy_aag_size = &proof.sizes[2];
  cert.policy_json_size = &proof.sizes[3];
  Gr1SolveOptions options{};
  options.oxidd = oxidd_solve_options_default();
  options.oxidd.node_cap = 200000;
  options.oxidd.cache_cap = 20000;
  options.certificate = &cert;
  OxiddFailure failure{};
  options.oxidd.failure = &failure;
  const TlsfGr1OrderV1 descriptor{order, game.provenance_json};
  AigPtr strategy(
      old_api ? solve_gr1_oxidd(copy.release(), &proof.unreal, &options)
              : solve_gr1_oxidd_ordered_v1(copy.release(), &proof.unreal,
                                           &options, &descriptor),
      aig_free);
  assert(failure.kind == OXIDD_FAILURE_NONE && !cert.failed);
  assert(strategy || proof.unreal == 1);
  for (size_t i = 0; i < 4; ++i)
    assert(proof.bytes[i] && proof.sizes[i]);

  TlsfGr1CheckInput input{};
  input.game_aag = {reinterpret_cast<const uint8_t *>(game.aag), game.aag_size};
  const auto span = [&](size_t i) -> TlsfGr1Bytes {
    return {reinterpret_cast<const uint8_t *>(proof.bytes[i]), proof.sizes[i]};
  };
  input.certificate_aag = span(0);
  input.certificate_json = span(1);
  input.policy_aag = span(2);
  input.policy_json = span(3);
  // One fixed, independent checker configuration for every candidate order.
  // Its proof obligations cover initial/reset predicates, ownership cubes,
  // next-state substitution, rank progress, and exported variable maps.
  TlsfGr1CheckOptions check{};
  check.method = TLSF_GR1_CHECK_CERTIFICATE;
  check.node_cap = 200000;
  check.cache_cap = 20000;
  check.max_artifact_bytes = 16u << 20;
  TlsfGr1CheckResult result{};
  assert(tlsf_gr1_check(&input, &check, &result) == TLSF_GR1_CHECK_OK);
  assert(result.verdict == TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&result);
}
std::vector<bool> evaluate(const Aig *aig, uint64_t assignment) {
  std::vector<bool> values(size_t(aig_num_inputs(aig)) + aig_num_ands(aig) + 1);
  const auto lit = [&](uint32_t literal) {
    return values.at(literal / 2) != bool(literal & 1);
  };
  for (uint32_t i = 0; i < aig_num_inputs(aig); ++i) {
    uint32_t literal;
    aig_input_name(aig, i, &literal);
    values.at(literal / 2) = (assignment >> i) & 1;
  }
  for (uint32_t i = 0; i < aig_num_ands(aig); ++i) {
    uint32_t lhs, a, b;
    aig_and_at(aig, i, &lhs, &a, &b);
    values.at(lhs / 2) = lit(a) && lit(b);
  }
  std::vector<bool> outputs;
  for (uint32_t i = 0; i < aig_num_outputs(aig); ++i) {
    uint32_t literal;
    aig_output_at(aig, i, &literal);
    outputs.push_back(lit(literal));
  }
  return outputs;
}
void same_ranks(const Proof &a, const Proof &b) {
  const auto am = j::parse(a.bytes[1]).as_object();
  const auto bm = j::parse(b.bytes[1]).as_object();
  if (!a.unreal)
    assert(j::serialize(am.at("variables")) ==
           j::serialize(bm.at("variables")));
  const auto ap = j::parse(a.bytes[3]).as_object();
  const auto bp = j::parse(b.bytes[3]).as_object();
  assert(j::serialize(ap.at("inputs")) == j::serialize(bp.at("inputs")));
  auto left = parse(a.bytes[0], a.sizes[0]);
  auto right = parse(b.bytes[0], b.sizes[0]);
  assert(aig_num_inputs(left.get()) == aig_num_inputs(right.get()));
  assert(aig_num_outputs(left.get()) == aig_num_outputs(right.get()));
  const auto n = aig_num_inputs(left.get());
  assert(n <= 18);
  for (uint32_t i = 0; i < n; ++i)
    assert(!strcmp(aig_input_name(left.get(), i, nullptr),
                   aig_input_name(right.get(), i, nullptr)));
  for (uint64_t assignment = 0; assignment < (uint64_t(1) << n); ++assignment)
    assert(evaluate(left.get(), assignment) ==
           evaluate(right.get(), assignment));
}
void ap_controls() {
  const std::string prefix =
      "INFO { TITLE: \"typed\" SEMANTICS: Mealy TARGET: Mealy } "
      "GLOBAL { PARAMETERS { n = 2; } } MAIN { ";
  const std::string suffix =
      " OUTPUTS { p[n]; } GUARANTEE { &&[0 <= k < n] G (p[k] <-> x[k]); } }";
  auto ordered = [&](const std::string &source, TlsfStructuralOrder order) {
    char **names = nullptr;
    size_t count = 0;
    assert(tlsf_structural_ap_order_v1(
        reinterpret_cast<const uint8_t *>(source.data()), source.size(), order,
        false, &names, &count));
    std::vector<std::string> result;
    for (size_t i = 0; i < count; ++i) {
      result.emplace_back(names[i]);
      free(names[i]);
    }
    free(names);
    return result;
  };
  const auto source = prefix + "INPUTS { x[n]; y[n]; shared; }" + suffix;
  auto renamed = source;
  for (size_t at = 0; (at = renamed.find("x[", at)) != std::string::npos;
       at += 3)
    renamed.replace(at, 2, "zz[");
  auto typed = ordered(source, TLSF_ORDER_TYPED_INTERLEAVED);
  auto twin = ordered(renamed, TLSF_ORDER_TYPED_INTERLEAVED);
  for (auto &name : twin)
    if (name.starts_with("zz_"))
      name.replace(0, 3, "x_");
  assert(typed == twin);
  assert((typed == std::vector<std::string>{"shared", "x_0", "y_0", "x_1",
                                            "y_1", "p_0", "p_1"}));
  auto grouped = ordered(source, TLSF_ORDER_ROLE_GROUPED);
  assert(grouped != typed);
  auto shuffled = ordered(prefix + "INPUTS { y[n]; x[n]; shared; }" + suffix,
                          TLSF_ORDER_TYPED_INTERLEAVED);
  assert((shuffled == std::vector<std::string>{"shared", "y_0", "x_0", "y_1",
                                               "x_1", "p_0", "p_1"}));
  const auto bits = ordered(
      "INFO { TITLE: \"bits\" SEMANTICS: Mealy TARGET: Mealy } "
      "GLOBAL { PARAMETERS { n = 2; } DEFINITIONS { "
      "enum mode = A: 01 B: 10 C: 11; } } MAIN { "
      "INPUTS { x[n]; y[n]; } OUTPUTS { mode st; p[n]; } "
      "GUARANTEE { G (!(st == C)); &&[0 <= k < n] G (p[k] <-> x[k]); } }",
      TLSF_ORDER_TYPED_INTERLEAVED);
  assert((bits == std::vector<std::string>{"x_0", "y_0", "x_1", "y_1", "st_0",
                                           "st_1", "p_0", "p_1"}));
}
int main() {
  ap_controls();
  bool changed = false;
  for (const auto &[formula, expected] :
       std::vector<std::pair<std::string, int>>{
           {"&&[0 <= k < n] G (p[k] <-> x[k]);", 0},
           {"&&[0 <= k < n] G (p[k] <-> X x[k]);", 1},
           {"&&[0 <= k < n] G F (p[k] && !x[k]);", 1},
           {"&&[0 <= i < n] &&[0 <= k < n] "
            "((i != k) -> G (!(p[i] && p[k])));",
            0}}) {
    const auto source =
        "INFO { TITLE: \"small game\" SEMANTICS: Mealy TARGET: Mealy } "
        "GLOBAL { PARAMETERS { n = 2; } } MAIN { "
        "INPUTS { x[n]; } OUTPUTS { p[n]; } "
        "INITIALLY { !x[0]; } PRESET { !p[0]; } GUARANTEE { " +
        formula + " } }";
    char hash[65]{};
    assert(tlsf_pipeline_source_sha256(source.data(), source.size(), hash));
    TlsfPipelineOptions popts{};
    popts.source_sha256 = hash;
    std::unique_ptr<TlsfPipeline, decltype(&tlsf_pipeline_free)> pipeline(
        tlsf_pipeline_load_bytes(
            reinterpret_cast<const uint8_t *>(source.data()), source.size(),
            &popts),
        tlsf_pipeline_free);
    assert(pipeline);
    TlsfGr1ReductionOptions options{};
    options.semantics = TLSF_GR1_EXACT;
    options.max_monitor_states = 1000;
    options.max_artifact_bytes = 16u << 20;
    TlsfGr1Reduction game{};
    TlsfGr1ReductionError error{};
    assert(tlsf_gr1_reduce(pipeline.get(), &options, &game, &error) ==
           TLSF_GR1_REDUCE_OK);
    Proof baseline, explicit_incumbent;
    solve(game, TLSF_ORDER_INCUMBENT, baseline, true);
    solve(game, TLSF_ORDER_INCUMBENT, explicit_incumbent);
    assert(baseline.unreal == expected);
    for (size_t i = 0; i < 4; ++i)
      assert(baseline.sizes[i] == explicit_incumbent.sizes[i] &&
             !memcmp(baseline.bytes[i], explicit_incumbent.bytes[i],
                     baseline.sizes[i]));
    for (auto order : {TLSF_ORDER_TYPED_INTERLEAVED, TLSF_ORDER_ROLE_GROUPED}) {
      uint32_t *variables = nullptr;
      size_t count = 0;
      assert(tlsf_structural_game_order_v1(game.game, game.provenance_json,
                                           order, 2, &variables, &count));
      assert(count ==
             aig_num_inputs(game.game) + aig_num_latches(game.game) + 2);
      std::set<uint32_t> inventory(variables, variables + count);
      assert(inventory.size() == count && *inventory.begin() == 0 &&
             *inventory.rbegin() == count - 1);
      for (size_t i = 0; i < count; ++i)
        changed |= variables[i] != i;
      free(variables);
      assert(tlsf_structural_game_order_v1(game.game, nullptr, order, 2,
                                           &variables, &count));
      for (size_t i = 0; i < count; ++i)
        assert(variables[i] == i);
      free(variables);
      Proof proof;
      solve(game, order, proof);
      assert(proof.unreal == expected);
      same_ranks(baseline, proof);
    }
    tlsf_gr1_reduction_clear(&game);
  }
  assert(changed);
}
