#include "gr1_shared.hh"
#include <cstdio>
#include <cstdlib>
#include <cstring>

using namespace gr1_lift_internal;
#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      std::fprintf(stderr, "line %d: %s\n", __LINE__, #x);                     \
      std::abort();                                                            \
    }                                                                          \
  } while (false)

static std::string source(const std::string &outputs, const std::string &body,
                          const std::string &inputs = "request[extent];") {
  return "INFO { TITLE: \"generated\" SEMANTICS: Mealy TARGET: Mealy }\n"
         "GLOBAL { PARAMETERS { extent = 5; } }\n"
         "MAIN { INPUTS { " +
         inputs + " } OUTPUTS { " + outputs + " } GUARANTEES { " + body +
         " } }\n";
}
static TlsfGr1LiftOptions options(TlsfGr1LiftStats *stats = nullptr) {
  TlsfGr1LiftOptions result{};
  result.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  result.disable_env_lift = 1;
  result.stats = stats;
  result.solver_nodes = result.checker_nodes = result.schema_nodes = 1u << 18;
  result.solver_cache = result.checker_cache = result.schema_cache = 1u << 16;
  result.max_artifact_bytes = 4u << 20;
  result.max_monitor_states = 1000;
  return result;
}
static std::unique_ptr<Instance> instance(const std::string &text) {
  Config cfg;
  cfg.o = options();
  cfg.budget = &cfg.o.budget;
  return lower((const uint8_t *)text.data(), text.size(), {}, TLSF_GR1_EXACT,
               cfg);
}
static TlsfGr1LiftResult lift(const std::string &text, bool typed,
                              bool success = true,
                              const char *stage = "typed_alignment") {
  TlsfGr1LiftStats stats{};
  auto opts = options(&stats);
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)text.data(),
                                           text.size(), &opts, &target,
                                           &error) == TLSF_GR1_LIFT_OK);
  TlsfGr1LiftResult result{};
  TlsfGr1LiftStatus cause{};
  TlsfGr1TypedRolesV1 roles{typed};
  auto status = tlsf_gr1_lift_from_target_v2(target, &opts, &result, &error,
                                             &cause, &roles);
  std::fprintf(stderr, "typed=%d status=%d cause=%d stage=%s message=%s\n",
               typed, status, cause, error.stage, error.message);
  if (success) {
    CHECK(status == TLSF_GR1_LIFT_OK);
    CHECK(result.method == TLSF_GR1_CHECK_REGION);
    CHECK(result.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
    CHECK(!result.policy_aag && stats.internal_checks == 1);
    CHECK(tlsf_gr1_lift_target_matches(target, &result));
    auto evidence = j::parse(result.evidence_json);
    const auto &knobs = evidence.as_object().at("global_knobs").as_object();
    if (typed)
      CHECK(knobs.at("r_typed_roles").as_bool());
    else
      CHECK(!knobs.contains("r_typed_roles"));
  } else {
    CHECK(status == TLSF_GR1_LIFT_DECLINED);
    CHECK(cause == TLSF_GR1_LIFT_DECLINED ||
          cause == TLSF_GR1_LIFT_UNSUPPORTED);
    CHECK(!strcmp(error.stage, stage));
    CHECK(!result.game_aag && stats.internal_checks == 0);
  }
  tlsf_gr1_lift_target_free(target);
  return result;
}
static void reject_wrong_certificate(const TlsfGr1LiftResult &result) {
  auto cert = parse_aig(result.certificate_aag, result.certificate_size);
  // Preserve the interface and sidecar; falsify only the winning predicate.
  std::string bytes(result.certificate_aag, result.certificate_size);
  size_t at = 0;
  for (uint32_t p = 0; p <= aig_num_inputs(cert.get()); p++)
    at = bytes.find('\n', at) + 1;
  CHECK(std::string(aig_output_at(cert.get(), 0, nullptr)) == "inv");
  bytes.replace(at, bytes.find('\n', at) - at, "0");
  TlsfGr1CheckInput input{};
  input.game_aag = {(const uint8_t *)result.game_aag, result.game_size};
  input.certificate_aag = {(const uint8_t *)bytes.data(), bytes.size()};
  input.certificate_json = {(const uint8_t *)result.certificate_json,
                            result.certificate_json_size};
  TlsfGr1CheckOptions opts{};
  opts.method = TLSF_GR1_CHECK_REGION;
  opts.node_cap = 1u << 18;
  opts.cache_cap = 1u << 16;
  opts.max_artifact_bytes = 4u << 20;
  TlsfGr1CheckResult checked{};
  CHECK(tlsf_gr1_check(&input, &opts, &checked) == TLSF_GR1_CHECK_OK);
  CHECK(checked.verdict == TLSF_GR1_CHECK_CERT_FAILED);
  tlsf_gr1_check_result_clear(&checked);
}
int main() {
  auto distinct = source("response[extent]; alternate[extent]; shared;",
                         "&&[0 <= i < extent] G F response[i]; "
                         "&&[0 <= i < extent] G F alternate[i]; G F shared;");
  auto value = lift(distinct, true);
  reject_wrong_certificate(value);
  tlsf_gr1_lift_result_clear(&value);
  // Same-shaped source roles remain distinct in the shared typed inventory.
  auto distinct_game = instance(distinct);
  auto distinct_view =
      typed_game_view(*distinct_game, "extent", {0, 1, 2, 3, 4});
  std::set<std::string> justice_kinds;
  for (const auto &[_, anchor] : distinct_view.goals)
    justice_kinds.insert(anchor.kind);
  CHECK(justice_kinds.size() == 3);
  // The incumbent is still selectable and independently checked.
  value = lift(distinct, false);
  tlsf_gr1_lift_result_clear(&value);
  auto twin = source(
      "z; y[extent]; x[extent];",
      "G F z; &&[0 <= i < extent] G F y[i]; &&[0 <= i < extent] G F x[i];",
      "renamed[extent];");
  value = lift(twin, true);
  tlsf_gr1_lift_result_clear(&value);
  auto fair =
      source("response[extent];", "&&[0 <= i < extent] G F response[i];");
  fair.replace(
      fair.find("GUARANTEES"), std::strlen("GUARANTEES"),
      "ASSUMPTIONS { &&[0 <= i < extent] G F request[i]; } GUARANTEES");
  // Fairness-order-dependent seed ranks need a richer grammar; alignment must
  // reach learning and safely decline rather than manufacture a certificate.
  value = lift(fair, true, false, "schema");
  tlsf_gr1_lift_result_clear(&value);
  auto fixed_fair = source("response[extent];",
                           "&&[0 <= i < extent] G F response[i];", "request;");
  fixed_fair.replace(fixed_fair.find("GUARANTEES"), std::strlen("GUARANTEES"),
                     "ASSUMPTIONS { G F request; } GUARANTEES");
  value = lift(fixed_fair, true);
  tlsf_gr1_lift_result_clear(&value);
  auto encoded = source("mode code; response[extent];",
                        "&&[0 <= i < extent] G F response[i];");
  encoded.replace(encoded.find("PARAMETERS {"), 0,
                  "DEFINITIONS { enum mode = A: 01 B: 10 C: 11; } ");
  auto encoded_game = instance(encoded);
  auto encoded_view = typed_game_view(*encoded_game, "extent", {0, 1, 2, 3, 4});
  bool local_bits = false;
  for (const J &entry : encoded_game->data.at("outputs").as_array()) {
    const O &row = entry.as_object();
    if (s(row, "index_role") == "representation-bit") {
      std::string name;
      for (uint32_t p = 0; p < aig_num_inputs(encoded_game->r.game); p++) {
        uint32_t literal;
        const char *current = aig_input_name(encoded_game->r.game, p, &literal);
        if (literal == uint32_t(n(row, "game_literal")))
          name = current;
      }
      auto var = encoded_view.variables.at(encoded_view.game_names.at(name));
      CHECK(var.owners.empty());
      local_bits = true;
    }
  }
  CHECK(local_bits);
  value = lift(encoded, true);
  tlsf_gr1_lift_result_clear(&value);
  auto pairwise = source("response[extent]; alternate[extent]; shared;",
                         "&&[0 <= i < extent] &&[0 <= j < extent] G "
                         "(!response[i] || !alternate[j]);");
  auto game = instance(pairwise);
  auto view = typed_game_view(*game, "extent", {0, 1, 2, 3, 4});
  bool pair = false, shared = false;
  for (const auto &[_, var] : view.variables) {
    pair |= var.owners.size() == 2;
    shared |= var.owners.empty();
  }
  CHECK(pair && shared);
  CHECK(typed_group(view.roles, {0, 1}, {"goal", {0, 1}}, {}) !=
        typed_group(view.roles, {0, 1}, {"goal", {1, 0}}, {}));
  CHECK(typed_group(view.roles, {0, 1}, {"goal", {0, 0}}, {}) !=
        typed_group(view.roles, {0, 1}, {"goal", {0, 1}}, {}));
  value = lift(pairwise, true, false, "schema");
  tlsf_gr1_lift_result_clear(&value);
  auto pair_goals = source("response[extent]; alternate[extent];",
                           "&&[0 <= i < extent] &&[0 <= j < extent] G F "
                           "(response[i] || alternate[j]);");
  pair_goals.replace(pair_goals.find("extent = 5"), std::strlen("extent = 5"),
                     "extent = 4");
  value = lift(pair_goals, true, false, "schema");
  tlsf_gr1_lift_result_clear(&value);
  // Local bit positions must not be substituted by owner slots with the same
  // integer.
  CHECK(typed_variable_key("bits", {0, 1}, {}, {{0, 3}, {1, 4}}) ==
        typed_variable_key("bits", {0, 1}, {}, {}));
  auto changing = "INFO { TITLE: \"width\" SEMANTICS: Mealy TARGET: Mealy }\n"
                  "GLOBAL { PARAMETERS { extent = 9; } DEFINITIONS { "
                  "half(x) = x <= 1 : 0 otherwise : 1 + half(x / 2); "
                  "bits(x) = x == 0 : 0 otherwise : 1 + half(x - 1); } }\n"
                  "MAIN { INPUTS { request[extent]; code[bits(extent)]; } "
                  "OUTPUTS { response[extent]; } GUARANTEES { "
                  "&&[0 <= i < extent] G F response[i]; } }\n";
  auto changing_game = instance(changing);
  int encoded_bits = 0;
  for (const J &entry : changing_game->data.at("inputs").as_array())
    encoded_bits += s(entry.as_object(), "index_role") == "representation-bit";
  CHECK(encoded_bits == 4);
  value = lift(changing, true, false);
  tlsf_gr1_lift_result_clear(&value);
  // Corrupt duplicate metadata retains its typed integrity cause.
  auto &monitor = game->data.at("monitors").as_array().front();
  game->data.at("monitors").as_array().push_back(monitor);
  try {
    typed_game_view(*game, "extent", {0, 1, 2, 3, 4});
    CHECK(false);
  } catch (const Failure &failure) {
    CHECK(failure.stage == "typed_alignment");
    CHECK(failure.cause == FailureCause::error);
  }
  auto opts = options();
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)distinct.data(),
                                           distinct.size(), &opts, &target,
                                           &error) == TLSF_GR1_LIFT_OK);
  TlsfGr1BothResult both{};
  TlsfGr1TypedRolesV1 roles{1};
  CHECK(tlsf_gr1_both_from_target_v2(target, &opts, nullptr, &both, &error,
                                     &roles) == TLSF_GR1_LIFT_OK);
  CHECK(both.route == TLSF_GR1_BOTH_REAL_LIFT);
  CHECK(both.target_reductions == 1 && both.target_checks == 1);
  CHECK(tlsf_gr1_lift_target_matches(target, &both.proof));
  CHECK(j::parse(both.proof.evidence_json)
            .as_object()
            .at("r_typed_roles")
            .as_bool());
  tlsf_gr1_both_result_clear(&both);
  roles.r_typed_roles = 2;
  CHECK(tlsf_gr1_both_from_target_v2(target, &opts, nullptr, &both, &error,
                                     &roles) == TLSF_GR1_LIFT_INVALID);
  tlsf_gr1_lift_target_free(target);
}
