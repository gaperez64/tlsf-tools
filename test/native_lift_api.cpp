#include "tlsf/gr1_lift.h"
#include "tlsf/pipeline.h"
#include "yyjson_cpp.hh"
#include <cassert>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
extern "C" void tlsf_gr1_lift_test_set_fault(int);

static const char *source =
    "INFO { TITLE: \"unseen\" DESCRIPTION: \"unseen\" SEMANTICS: Mealy TARGET: "
    "Mealy }\n"
    "GLOBAL { PARAMETERS { extent = 5; } }\n"
    "MAIN { INPUTS { demand[extent]; } OUTPUTS { response[extent]; }\n"
    "GUARANTEES { &&[0 <= i < extent] G F response[i]; } }\n";
static const char *nonparam =
    "INFO { TITLE: \"plain\" DESCRIPTION: \"plain\" SEMANTICS: Mealy TARGET: "
    "Mealy }\n"
    "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G F b; } }\n";
static const char *nonparam_moore =
    "INFO { TITLE: \"plain\" DESCRIPTION: \"plain\" SEMANTICS: Moore TARGET: "
    "Moore }\n"
    "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G F b; } }\n";
static const char *encoded_width =
    "INFO { TITLE: \"width\" DESCRIPTION: \"width\" SEMANTICS: Mealy TARGET: "
    "Mealy }\n"
    "GLOBAL { PARAMETERS { span = 8; } DEFINITIONS { "
    "bits(x) = x <= 1 : 1 otherwise : 1 + bits(x / 2); } }\n"
    "MAIN { INPUTS { request[bits(span)]; } OUTPUTS { selector[bits(span)]; } "
    "GUARANTEES { G F selector[0]; } }\n";
static const char *large_arity =
    "INFO { TITLE: \"arity\" DESCRIPTION: \"arity\" SEMANTICS: Mealy TARGET: "
    "Mealy }\n"
    "GLOBAL { PARAMETERS { span = 6; } }\n"
    "MAIN { INPUTS { req[span]; } OUTPUTS { grant[span]; } GUARANTEES { "
    "G F (grant[0] && !grant[1] && grant[2] && !grant[3] && grant[4]); } }\n";
static const char *rank_chain =
    "INFO { TITLE: \"rank chain\" DESCRIPTION: \"rank chain\" "
    "SEMANTICS: Mealy TARGET: Mealy }\n"
    "GLOBAL { PARAMETERS { span = 6; } }\n"
    "MAIN { INPUTS { dummy; } OUTPUTS { pulse[span]; }\n"
    "PRESET { pulse[0]; &&[1 <= i < span] !pulse[i]; }\n"
    "ASSERT { &&[0 <= i < span - 1] (pulse[i] <-> X pulse[i + 1]); }\n"
    "GUARANTEES { &&[0 <= i < span] G F pulse[i]; } }\n";
static uint64_t deadline(unsigned seconds) {
  auto now = std::chrono::steady_clock::now().time_since_epoch();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now).count() +
         uint64_t(seconds) * 1000000000ull;
}
static int cancelled(void *) { return 1; }
struct Mutate {
  char *bytes;
  int calls;
};
static int mutate_after_snapshot(void *raw) {
  auto *ctx = static_cast<Mutate *>(raw);
  if (++ctx->calls == 2)
    ctx->bytes[0] = 'X';
  return 0;
}
static TlsfGr1LiftOptions options() {
  TlsfGr1LiftOptions o{};

  o.deadline_mono_ns = deadline(10);
  o.solver_nodes = 1u << 18;
  o.solver_cache = 1u << 16;
  o.checker_nodes = 1u << 18;
  o.checker_cache = 1u << 16;
  o.schema_nodes = 1u << 18;
  o.schema_cache = 1u << 16;
  o.max_monitor_states = 1000;
  o.max_artifact_bytes = 4u << 20;
  return o;
}
static TlsfGr1LiftStatus lift(const char *bytes, const TlsfGr1LiftOptions &o,
                              TlsfGr1LiftResult *r, TlsfGr1LiftError *e) {
  return tlsf_gr1_lift(reinterpret_cast<const uint8_t *>(bytes), strlen(bytes),
                       nullptr, 0, &o, r, e);
}
int main() {
  TlsfGr1LiftResult result{};
  TlsfGr1LiftError error{};
  auto o = options();
  assert(lift(nonparam, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  assert(!strcmp(error.stage, "parameters") && !result.game_aag);
  assert(lift(nonparam_moore, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  assert(!strcmp(error.stage, "parameters") && !result.game_aag);
  assert(lift(encoded_width, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  assert(!strcmp(error.stage, "seed_window") && !result.game_aag);
  assert(lift(large_arity, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  assert(!strcmp(error.stage, "bus_schema") && !result.game_aag);
  assert(lift(rank_chain, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  assert(!strcmp(error.stage, "schema") &&
         strstr(error.message, "rank depth changed from") && !result.game_aag);
  o = options();
  o.cancelled = cancelled;
  assert(lift(source, o, &result, &error) == TLSF_GR1_LIFT_CANCELLED);
  assert(!result.certificate_aag);
  o = options();
  o.deadline_mono_ns = 1;
  assert(lift(source, o, &result, &error) == TLSF_GR1_LIFT_DEADLINE);
  o = options();
  o.max_artifact_bytes = 1;
  assert(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  assert(!result.game_aag && !result.policy_aag);
  o = options();
  o.max_subsets_per_predicate = 1;
  assert(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  assert(!result.game_aag && !result.certificate_aag);
  o = options();
  tlsf_gr1_lift_test_set_fault(1);
  assert(lift(source, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  assert(!strcmp(error.stage, "seed_window") &&
         strstr(error.message, "selected seed choice") && !result.game_aag);
  tlsf_gr1_lift_test_set_fault(0);
  o = options();
  auto status = lift(source, o, &result, &error);
  if (status != TLSF_GR1_LIFT_OK)
    fprintf(stderr, "native lift failed: status=%d stage=%s message=%s\n",
            status, error.stage, error.message);
  assert(status == TLSF_GR1_LIFT_OK);
  assert(result.verdict == TLSF_GR1_CHECK_VERIFIED);
  assert(result.method == TLSF_GR1_CHECK_CERTIFICATE);
  assert(result.game_aag && result.certificate_aag && result.policy_aag);
  assert(result.evidence_json &&
         strstr(result.evidence_json, "target_transition"));
  auto baseline = tlsf_json::parse(result.evidence_json).as_object();
  assert(baseline.at("format") == TLSF_GR1_LIFT_EVIDENCE_FORMAT);
  char policy_hash[65]{};
  assert(tlsf_pipeline_source_sha256(result.policy_aag, result.policy_size,
                                     policy_hash));
  assert(baseline.at("policy_sha256") == policy_hash);
  auto baseline_roles = baseline.at("roles");
  auto baseline_seeds = baseline.at("seed_values");
  FILE *fp = fmemopen(result.certificate_aag, result.certificate_size, "r");
  assert(fp);
  std::unique_ptr<Aig, decltype(&aig_free)> mutated(aig_read_aag(fp),
                                                    &aig_free);
  fclose(fp);
  assert(mutated);
  aig_set_output(mutated.get(), "inv", AIG_FALSE);
  char *bytes = nullptr;
  size_t size = 0;
  fp = open_memstream(&bytes, &size);
  assert(fp);
  aig_write_aag(fp, mutated.get());
  assert(fclose(fp) == 0);
  TlsfGr1CheckInput input{};
  input.game_aag = {(const uint8_t *)result.game_aag, result.game_size};
  input.certificate_aag = {(const uint8_t *)bytes, size};
  input.certificate_json = {(const uint8_t *)result.certificate_json,
                            result.certificate_json_size};
  input.policy_aag = {(const uint8_t *)result.policy_aag, result.policy_size};
  input.policy_json = {(const uint8_t *)result.policy_json,
                       result.policy_json_size};
  TlsfGr1CheckOptions check_options{};
  check_options.method = TLSF_GR1_CHECK_CERTIFICATE;
  check_options.node_cap = 1u << 18;
  check_options.cache_cap = 1u << 16;
  check_options.max_artifact_bytes = 4u << 20;
  check_options.deadline_mono_ns = deadline(10);
  TlsfGr1CheckResult check{};
  input.certificate_aag = {(const uint8_t *)result.certificate_aag,
                           result.certificate_size};
  std::string original_policy(result.policy_json, result.policy_json_size);
  assert(!original_policy.empty() && original_policy.front() == '{');
  auto replace_once = [](std::string text, const char *from, const char *to) {
    size_t at = text.find(from);
    assert(at != std::string::npos);
    text.replace(at, strlen(from), to);
    return text;
  };
  auto check_policy = [&](const std::string &policy,
                          TlsfGr1CheckVerdict expected) {
    input.policy_json = {(const uint8_t *)policy.data(), policy.size()};
    check_options.deadline_mono_ns = deadline(10);
    assert(tlsf_gr1_check(&input, &check_options, &check) == TLSF_GR1_CHECK_OK);
    assert(check.verdict == expected);
    tlsf_gr1_check_result_clear(&check);
  };
  check_policy(original_policy, TLSF_GR1_CHECK_VERIFIED);
  check_policy(replace_once(original_policy, "\"format\"", "\"for\\u006dat\""),
               TLSF_GR1_CHECK_VERIFIED);
  check_policy(replace_once(original_policy, "tlsf-gr1-policy-v1",
                            "tlsf-gr1-policy-\\u00761"),
               TLSF_GR1_CHECK_VERIFIED);
  std::string duplicate_format = original_policy;
  duplicate_format.insert(1, "\"for\\u006dat\":\"tlsf-gr1-policy-v1\",");
  check_policy(duplicate_format, TLSF_GR1_CHECK_INVALID);
  std::string duplicate_source = original_policy;
  duplicate_source.insert(
      1, "\"source_sha256\":\"first\",\"source_\\u0073ha256\":\"second\",");
  check_policy(duplicate_source, TLSF_GR1_CHECK_INVALID);
  std::string duplicate_policy =
      "{\"source_sha256\":\"first\",\"source_sha256\":\"second\"," +
      original_policy.substr(1);
  check_policy(duplicate_policy, TLSF_GR1_CHECK_INVALID);
  input.certificate_aag = {(const uint8_t *)bytes, size};
  input.policy_json = {(const uint8_t *)result.policy_json,
                       result.policy_json_size};
  tlsf_gr1_check(&input, &check_options, &check);
  assert(check.verdict != TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&check);
  free(bytes);
  tlsf_gr1_lift_result_clear(&result);
  assert(!result.game_aag);
  std::string renamed(source);
  auto rename_all = [&](const std::string &from, const std::string &to) {
    size_t at = 0;
    while ((at = renamed.find(from, at)) != std::string::npos) {
      renamed.replace(at, from.size(), to);
      at += to.size();
    }
  };
  rename_all("demand", "monitor_17_state_3");
  rename_all("response", "assumption_safety_violated");
  o = options();
  assert(lift(renamed.c_str(), o, &result, &error) == TLSF_GR1_LIFT_OK);
  auto renamed_evidence = tlsf_json::parse(result.evidence_json).as_object();
  assert(tlsf_json::serialize(renamed_evidence.at("roles")) ==
         tlsf_json::serialize(baseline_roles));
  assert(tlsf_json::serialize(renamed_evidence.at("seed_values")) ==
         tlsf_json::serialize(baseline_seeds));
  tlsf_gr1_lift_result_clear(&result);
  o = options();
  o.policy_proof_fraction = 1e-12;
  assert(lift(source, o, &result, &error) == TLSF_GR1_LIFT_OK);
  assert(result.method == TLSF_GR1_CHECK_REGION);
  assert(result.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  assert(!result.policy_aag && result.check_json);
  auto region_evidence = tlsf_json::parse(result.evidence_json).as_object();
  assert(region_evidence.at("format") == TLSF_GR1_LIFT_EVIDENCE_FORMAT);
  assert(!region_evidence.if_contains("policy_sha256"));
  tlsf_gr1_lift_result_clear(&result);
  std::string mutable_source(source);
  Mutate mutation{mutable_source.data(), 0};
  o = options();
  o.cancelled = mutate_after_snapshot;
  o.cancel_ctx = &mutation;
  assert(lift(mutable_source.c_str(), o, &result, &error) == TLSF_GR1_LIFT_OK);
  assert(mutation.calls >= 2 && mutable_source[0] == 'X');
  tlsf_gr1_lift_result_clear(&result);
  std::string smaller_source(source);
  auto position = smaller_source.find("extent = 5");
  assert(position != std::string::npos);
  smaller_source.replace(position, 10, "extent = 2");
  ParamOverride override{"extent", 5};
  o = options();
  assert(tlsf_gr1_lift((const uint8_t *)smaller_source.data(),
                       smaller_source.size(), &override, 1, &o, &result,
                       &error) == TLSF_GR1_LIFT_OK);
  assert(result.evidence_json &&
         strstr(result.evidence_json, "\"axis\":\"extent\""));
  tlsf_gr1_lift_result_clear(&result);
  ParamOverride duplicates[2] = {{"extent", 5}, {"extent", 6}};
  assert(tlsf_gr1_lift((const uint8_t *)source, strlen(source), duplicates, 2,
                       &o, &result, &error) == TLSF_GR1_LIFT_INVALID);
  assert(!result.game_aag);
  tlsf_gr1_lift_result_clear(nullptr);
  return 0;
}
