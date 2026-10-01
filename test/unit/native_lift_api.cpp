#include "tlsf/gr1_lift.h"
#include "tlsf/pipeline.h"
#include "yyjson_cpp.hh"
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      std::fprintf(stderr, "check failed at line %d: %s\n", __LINE__,          \
                   #condition);                                                \
      std::abort();                                                            \
    }                                                                          \
  } while (false)
extern "C" void tlsf_gr1_lift_test_set_fault(int);
extern "C" const char *tlsf_gr1_lift_test_generated_certificate_json();
extern "C" int tlsf_gr1_lift_test_fallback_started_before_deadline();
extern "C" int tlsf_gr1_lift_test_checked_game_equals(const char *, size_t);
extern "C" int
tlsf_gr1_lift_test_prepared_game_equals(const TlsfGr1LiftTarget *, const char *,
                                        size_t);
extern "C" void tlsf_gr1_lift_test_corrupt_prepared_game(TlsfGr1LiftTarget *);

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
static void tighten_rss_after_window(void *context, TlsfGr1LiftStatsStage stage,
                                     const TlsfGr1LiftStageStats *) {
  if (stage == TLSF_GR1_LIFT_STATS_SEED_WINDOW)
    static_cast<TlsfGr1LiftOptions *>(context)->budget.max_rss_bytes = 1;
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
  CHECK(lift(nonparam, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "parameters") && !result.game_aag);
  CHECK(lift(nonparam_moore, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "parameters") && !result.game_aag);
  CHECK(lift(encoded_width, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "seed_window") && !result.game_aag);
  CHECK(lift(large_arity, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "bus_schema") && !result.game_aag);
  CHECK(lift(rank_chain, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "schema") &&
        strstr(error.message, "rank depth changed from") && !result.game_aag);
  o = options();
  o.cancelled = cancelled;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_CANCELLED);
  CHECK(!result.certificate_aag);
  o = options();
  o.deadline_mono_ns = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_DEADLINE);
  o = options();
  o.max_artifact_bytes = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!result.game_aag && !result.policy_aag);
  o = options();
  o.max_subsets_per_predicate = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!result.game_aag && !result.certificate_aag);
  o = options();
  tlsf_gr1_lift_test_set_fault(1);
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "seed_window") &&
        strstr(error.message, "selected seed choice") && !result.game_aag);
  tlsf_gr1_lift_test_set_fault(0);
  o = options();
  auto status = lift(source, o, &result, &error);
  if (status != TLSF_GR1_LIFT_OK)
    fprintf(stderr, "native lift failed: status=%d stage=%s message=%s\n",
            status, error.stage, error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(result.verdict == TLSF_GR1_CHECK_VERIFIED);
  CHECK(result.method == TLSF_GR1_CHECK_CERTIFICATE);
  CHECK(result.game_aag && result.certificate_aag && result.policy_aag);
  CHECK(result.evidence_json &&
        strstr(result.evidence_json, "target_transition"));
  auto baseline = tlsf_json::parse(result.evidence_json).as_object();
  CHECK(baseline.at("format") == TLSF_GR1_LIFT_EVIDENCE_FORMAT);
  char policy_hash[65]{};
  CHECK(tlsf_pipeline_source_sha256(result.policy_aag, result.policy_size,
                                    policy_hash));
  CHECK(baseline.at("policy_sha256") == policy_hash);
  auto baseline_roles = baseline.at("roles");
  auto baseline_seeds = baseline.at("seed_values");
  FILE *fp = fmemopen(result.certificate_aag, result.certificate_size, "r");
  CHECK(fp);
  std::unique_ptr<Aig, decltype(&aig_free)> mutated(aig_read_aag(fp),
                                                    &aig_free);
  fclose(fp);
  CHECK(mutated);
  aig_set_output(mutated.get(), "inv", AIG_FALSE);
  char *bytes = nullptr;
  size_t size = 0;
  fp = open_memstream(&bytes, &size);
  CHECK(fp);
  aig_write_aag(fp, mutated.get());
  CHECK(fclose(fp) == 0);
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
  CHECK(!original_policy.empty() && original_policy.front() == '{');
  auto replace_once = [](std::string text, const char *from, const char *to) {
    size_t at = text.find(from);
    CHECK(at != std::string::npos);
    text.replace(at, strlen(from), to);
    return text;
  };
  auto check_policy = [&](const std::string &policy,
                          TlsfGr1CheckVerdict expected) {
    input.policy_json = {(const uint8_t *)policy.data(), policy.size()};
    check_options.deadline_mono_ns = deadline(10);
    CHECK(tlsf_gr1_check(&input, &check_options, &check) == TLSF_GR1_CHECK_OK);
    CHECK(check.verdict == expected);
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
  CHECK(check.verdict != TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&check);
  // A failed speculative certificate check retries with a fresh manager.
  // The next call on this same thread must still create and release one.
  input.certificate_aag = {(const uint8_t *)result.certificate_aag,
                           result.certificate_size};
  check_policy(original_policy, TLSF_GR1_CHECK_VERIFIED);
  free(bytes);
  tlsf_gr1_lift_result_clear(&result);
  CHECK(!result.game_aag);
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
  CHECK(lift(renamed.c_str(), o, &result, &error) == TLSF_GR1_LIFT_OK);
  auto renamed_evidence = tlsf_json::parse(result.evidence_json).as_object();
  CHECK(tlsf_json::serialize(renamed_evidence.at("roles")) ==
        tlsf_json::serialize(baseline_roles));
  CHECK(tlsf_json::serialize(renamed_evidence.at("seed_values")) ==
        tlsf_json::serialize(baseline_seeds));
  tlsf_gr1_lift_result_clear(&result);
  o = options();
  o.phase_budget.policy_proof_ns = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_OK);
  CHECK(result.method == TLSF_GR1_CHECK_REGION);
  CHECK(result.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  CHECK(!result.policy_aag && result.check_json);
  auto region_evidence = tlsf_json::parse(result.evidence_json).as_object();
  CHECK(region_evidence.at("format") == TLSF_GR1_LIFT_EVIDENCE_FORMAT);
  CHECK(!region_evidence.if_contains("policy_sha256"));
  tlsf_gr1_lift_result_clear(&result);
  std::string mutable_target(source);
  o = options();
  TlsfGr1LiftStats trusted_stats{};
  o.stats = &trusted_stats;
  o.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  TlsfGr1LiftTarget *target = nullptr;
  CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)mutable_target.data(),
                                     mutable_target.size(), nullptr, 0, &o,
                                     &target, &error) == TLSF_GR1_LIFT_OK);
  CHECK(target);
  mutable_target[0] = 'X';
  CHECK(tlsf_gr1_lift_from_target(target, &o, &result, &error) ==
        TLSF_GR1_LIFT_OK);
  CHECK(result.method == TLSF_GR1_CHECK_REGION);
  CHECK(trusted_stats.internal_checks == 1);
  CHECK(trusted_stats.stages[TLSF_GR1_LIFT_STATS_POLICY_EXPORT].calls == 0);
  CHECK(tlsf_gr1_lift_target_matches(target, &result));
  std::string trusted_game(result.game_aag, result.game_size);
  std::string trusted_certificate_json(result.certificate_json,
                                       result.certificate_json_size);
  result.certificate_aag[0] = 'X';
  CHECK(!tlsf_gr1_lift_target_matches(target, &result));
  result.certificate_aag[0] = 'a';
  CHECK(tlsf_gr1_lift_target_matches(target, &result));
  std::swap(result.game_aag, result.certificate_aag);
  std::swap(result.game_size, result.certificate_size);
  auto swapped = tlsf_json::parse(result.evidence_json).as_object();
  char swapped_game_hash[65]{}, swapped_cert_hash[65]{};
  CHECK(tlsf_pipeline_source_sha256(result.game_aag, result.game_size,
                                    swapped_game_hash));
  CHECK(tlsf_pipeline_source_sha256(
      result.certificate_aag, result.certificate_size, swapped_cert_hash));
  swapped["game_sha256"] = swapped_game_hash;
  swapped["certificate_sha256"] = swapped_cert_hash;
  std::string swapped_json = tlsf_json::serialize(swapped);
  free(result.evidence_json);
  result.evidence_size = swapped_json.size();
  result.evidence_json = (char *)malloc(result.evidence_size + 1);
  CHECK(result.evidence_json);
  memcpy(result.evidence_json, swapped_json.c_str(), result.evidence_size + 1);
  CHECK(!tlsf_gr1_lift_target_matches(target, &result));
  tlsf_gr1_lift_result_clear(&result);
  tlsf_gr1_lift_target_free(target);
  target = nullptr;
  o = options();
  o.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)source, strlen(source),
                                     nullptr, 0, &o, &target,
                                     &error) == TLSF_GR1_LIFT_OK);
  TlsfGr1LiftStats generation_stats{};
  o.stats = &generation_stats;
  tlsf_gr1_lift_test_set_fault(5);
  auto generation_status =
      tlsf_gr1_lift_from_target(target, &o, &result, &error);
  if (generation_status != TLSF_GR1_LIFT_OK)
    fprintf(stderr, "generation status=%d stage=%s message=%s checks=%llu\n",
            generation_status, error.stage, error.message,
            (unsigned long long)generation_stats.internal_checks);
  CHECK(generation_status == TLSF_GR1_LIFT_OK);
  CHECK(generation_stats.internal_checks == 1);
  CHECK(result.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  CHECK(tlsf_gr1_lift_target_matches(target, &result));
  CHECK(std::string(result.game_aag, result.game_size) == trusted_game);
  std::string mutated_certificate_json(
      tlsf_gr1_lift_test_generated_certificate_json());
  CHECK(!mutated_certificate_json.empty());
  auto trusted_sidecar = tlsf_json::parse(trusted_certificate_json).as_object();
  auto mutated_sidecar = tlsf_json::parse(mutated_certificate_json).as_object();
  CHECK(tlsf_json::serialize(trusted_sidecar.at("variables")
                                 .as_object()
                                 .at("state")
                                 .as_array()
                                 .at(0)
                                 .as_object()
                                 .at("next_game_literal")) !=
        tlsf_json::serialize(mutated_sidecar.at("variables")
                                 .as_object()
                                 .at("state")
                                 .as_array()
                                 .at(0)
                                 .as_object()
                                 .at("next_game_literal")));
  CHECK(tlsf_gr1_lift_test_prepared_game_equals(target, trusted_game.data(),
                                                trusted_game.size()));
  CHECK(tlsf_gr1_lift_test_checked_game_equals(trusted_game.data(),
                                               trusted_game.size()));
  tlsf_gr1_lift_result_clear(&result);
  tlsf_gr1_lift_test_set_fault(0);
  tlsf_gr1_lift_target_free(target);
  target = nullptr;
  TlsfGr1LiftStats corrupt_stats{};
  o.stats = &corrupt_stats;
  CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)source, strlen(source),
                                     nullptr, 0, &o, &target,
                                     &error) == TLSF_GR1_LIFT_OK);
  tlsf_gr1_lift_test_corrupt_prepared_game(target);
  CHECK(tlsf_gr1_lift_from_target(target, &o, &result, &error) ==
        TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "target_check"));
  CHECK(corrupt_stats.internal_checks == 0);
  CHECK(!result.game_aag);
  tlsf_gr1_lift_target_free(target);
  target = nullptr;
  o.stats = &trusted_stats;
  o.deadline_mono_ns = deadline(10);
  tlsf_gr1_lift_test_set_fault(2);
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_OK);
  CHECK(result.method == TLSF_GR1_CHECK_CERTIFICATE);
  CHECK(trusted_stats.internal_checks == 2);
  CHECK(result.policy_aag);
  tlsf_gr1_lift_result_clear(&result);
  tlsf_gr1_lift_test_set_fault(3);
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "target_check"));
  CHECK(trusted_stats.internal_checks == 1);
  CHECK(trusted_stats.stages[TLSF_GR1_LIFT_STATS_POLICY_EXPORT].calls == 0);
  o.deadline_mono_ns = deadline(2);
  tlsf_gr1_lift_test_set_fault(4);
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_DEADLINE);
  CHECK(tlsf_gr1_lift_test_fallback_started_before_deadline());
  CHECK(deadline(0) >= o.deadline_mono_ns);
  CHECK(!strcmp(error.stage, "target_check"));
  CHECK(!result.game_aag);
  tlsf_gr1_lift_test_set_fault(0);
  o = options();
  o.phase_budget.max_discovery_bdd_ops = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!result.game_aag && !result.certificate_aag);
  o = options();
  TlsfGr1LiftStats stats{};
  o.stats = &stats;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_OK);
  CHECK(stats.seed_solves && stats.work.monitors_completed);
  tlsf_gr1_lift_result_clear(&result);
  o.budget.max_formula_nodes = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!strcmp(error.stage, "budget-structure") &&
        !strcmp(stats.final_stage, "budget-structure"));
  CHECK(stats.work.formula_nodes > o.budget.max_formula_nodes);
  o.budget.max_formula_nodes = 0;
  // The budget is read live, so tightening it after the seed window makes
  // lifting's own seed-stage check decline.
  o.stats_callback = tighten_rss_after_window;
  o.stats_context = &o;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!strcmp(error.stage, "budget-memory") && strstr(error.message, "seed"));
  CHECK(stats.work.peak_rss_bytes > o.budget.max_rss_bytes);
  CHECK(!result.game_aag && !result.certificate_aag);
  std::string mutable_source(source);
  Mutate mutation{mutable_source.data(), 0};
  o = options();
  o.cancelled = mutate_after_snapshot;
  o.cancel_ctx = &mutation;
  CHECK(lift(mutable_source.c_str(), o, &result, &error) == TLSF_GR1_LIFT_OK);
  CHECK(mutation.calls >= 2 && mutable_source[0] == 'X');
  tlsf_gr1_lift_result_clear(&result);
  std::string smaller_source(source);
  auto position = smaller_source.find("extent = 5");
  CHECK(position != std::string::npos);
  smaller_source.replace(position, 10, "extent = 2");
  ParamOverride override{"extent", 5};
  o = options();
  CHECK(tlsf_gr1_lift((const uint8_t *)smaller_source.data(),
                      smaller_source.size(), &override, 1, &o, &result,
                      &error) == TLSF_GR1_LIFT_OK);
  CHECK(result.evidence_json &&
        strstr(result.evidence_json, "\"axis\":\"extent\""));
  tlsf_gr1_lift_result_clear(&result);
  ParamOverride duplicates[2] = {{"extent", 5}, {"extent", 6}};
  CHECK(tlsf_gr1_lift((const uint8_t *)source, strlen(source), duplicates, 2,
                      &o, &result, &error) == TLSF_GR1_LIFT_INVALID);
  CHECK(!result.game_aag);
  tlsf_gr1_lift_result_clear(nullptr);
  return 0;
}
