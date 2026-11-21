#include "tlsf/gr1_lift.h"
#include "tlsf/obfuscate.h"
#include "tlsf/pipeline.h"
#include "yyjson_cpp.hh"
#include "resource_usage.h"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      std::fprintf(stderr, "check failed at line %d: %s\n", __LINE__,          \
                   #condition);                                                \
      std::abort();                                                            \
    }                                                                          \
  } while (false)
extern "C" void tlsf_gr1_lift_test_set_fault(int);
extern "C" unsigned tlsf_gr1_lift_test_check_json_clears();
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
static int never_cancelled(void *) { return 0; }
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
  if (stage == TLSF_GR1_LIFT_STATS_SEED_WINDOW) {
    uint64_t current = 0;
    CHECK(tlsf_current_rss_bytes(&current) && current > 1);
    static_cast<TlsfGr1LiftOptions *>(context)->budget.max_rss_bytes =
        current / 2;
  }
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
static void bounded_seed_declines() {
  std::string parameters = "GLOBAL { PARAMETERS { ";
  for (int i = 0; i < 12; ++i)
    parameters += "axis" + std::to_string(i) + std::string(200, 'x') + " = 2; ";
  parameters += "} }\n";
  std::string bytes(nonparam);
  bytes.insert(bytes.find("MAIN"), parameters);
  auto o = options();
  struct {
    uint64_t before = 0x123456789abcdef0ull;
    TlsfGr1LiftResult result{};
    uint64_t after = 0xfedcba9876543210ull;
  } guarded;
  struct {
    uint64_t before = 0x123456789abcdef0ull;
    TlsfGr1LiftError error{};
    uint64_t after = 0xfedcba9876543210ull;
  } guarded_error;
  auto &result = guarded.result;
  auto &error = guarded_error.error;
  CHECK(lift(bytes.c_str(), o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(guarded.before == 0x123456789abcdef0ull &&
        guarded.after == 0xfedcba9876543210ull);
  CHECK(guarded_error.before == 0x123456789abcdef0ull &&
        guarded_error.after == 0xfedcba9876543210ull);
  CHECK(memchr(result.decline_detail, '\0', sizeof result.decline_detail));
  CHECK(error.message[sizeof error.message - 1] == '\0');
  const std::string detail = result.decline_detail;
  CHECK(detail.size() < sizeof result.decline_detail);
  CHECK(detail.find("[1]=parameter_not_indexed") != std::string::npos);
  CHECK(detail.compare(detail.size() - strlen("; [truncated]"),
                       strlen("; [truncated]"), "; [truncated]") == 0);
  tlsf_gr1_lift_result_clear(&result);
}
static void discovery_budget_declines() {
  auto o = options();
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)source, strlen(source),
                                     nullptr, 0, &o, &target,
                                     &error) == TLSF_GR1_LIFT_OK);
  TlsfGr1LiftResult result{};
  o.deadline_mono_ns = 1;
  CHECK(tlsf_gr1_lift_from_target(target, &o, &result, &error) ==
        TLSF_GR1_LIFT_DEADLINE);
  CHECK(strstr(result.decline_detail, "extent[1]=time_budget"));
  CHECK(strstr(result.decline_detail, "stage=seed_window,cause=deadline"));
  o = options();
  o.budget.max_rss_bytes = 1;
  CHECK(tlsf_gr1_lift_from_target(target, &o, &result, &error) ==
        TLSF_GR1_LIFT_LIMIT);
  CHECK(strstr(result.decline_detail, "extent[1]=memory_budget"));
  CHECK(strstr(result.decline_detail, "stage=budget-memory,cause=resource"));
  CHECK(!result.game_aag && result.verdict == TLSF_GR1_CHECK_UNKNOWN);
  tlsf_gr1_lift_result_clear(&result);
  tlsf_gr1_lift_target_free(target);
}
static void corruption_guards() {
  for (auto order : {TLSF_GR1_LIFT_POLICY_FIRST, TLSF_GR1_LIFT_REGION_FIRST}) {
    for (int fault : {6, 7}) {
      auto o = options();
      o.proof_order = order;
      TlsfGr1LiftStats stats{};
      o.stats = &stats;
      TlsfGr1LiftTarget *target = nullptr;
      TlsfGr1LiftError error{};
      CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)source,
                                         strlen(source), nullptr, 0, &o,
                                         &target, &error) == TLSF_GR1_LIFT_OK);
      tlsf_gr1_lift_test_set_fault(fault);
      TlsfGr1LiftResult result{};
      CHECK(tlsf_gr1_lift_from_target(target, &o, &result, &error) ==
            TLSF_GR1_LIFT_DECLINED);
      CHECK(stats.internal_checks == (fault == 6 ? 0u : 1u));
      CHECK(!result.game_aag && !result.certificate_aag &&
            !result.evidence_json);
      stats = {};
      TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_OK;
      CHECK(tlsf_gr1_lift_from_target_v1(target, &o, &result, &error, &cause) ==
            TLSF_GR1_LIFT_DECLINED);
      CHECK(cause == TLSF_GR1_LIFT_ERROR);
      CHECK(error.status == TLSF_GR1_LIFT_DECLINED);
      CHECK(!strcmp(error.stage, fault == 6 ? "schema_abi" : "target_check"));
      std::string message =
          fault == 6 ? "multi-member justice" : "unverified candidate";
      if (result.decline_detail[0])
        message += std::string(": ") + result.decline_detail;
      CHECK(error.message == message);
      CHECK(stats.internal_checks == (fault == 6 ? 0u : 1u));
      CHECK(stats.stages[TLSF_GR1_LIFT_STATS_PUBLISH].calls == 0);
      CHECK(!result.game_aag && !result.certificate_aag && !result.policy_aag &&
            !result.evidence_json && !result.check_json);
      tlsf_gr1_lift_result_clear(&result);
      tlsf_gr1_lift_test_set_fault(0);
      stats = {};
      CHECK(tlsf_gr1_lift_from_target_v1(target, &o, &result, &error, &cause) ==
            TLSF_GR1_LIFT_OK);
      CHECK(cause == TLSF_GR1_LIFT_OK && stats.internal_checks == 1);
      CHECK(result.verdict == (order == TLSF_GR1_LIFT_POLICY_FIRST
                                   ? TLSF_GR1_CHECK_VERIFIED
                                   : TLSF_GR1_CHECK_REGION_VERIFIED));
      CHECK(tlsf_gr1_lift_target_matches(target, &result));
      tlsf_gr1_lift_result_clear(&result);
      tlsf_gr1_lift_target_free(target);
    }
  }
}
static std::string read_source(const char *path) {
  std::ifstream file(path);
  CHECK(file.good());
  return {std::istreambuf_iterator<char>(file), {}};
}
// The library obfuscator's RENAME mode: neutral names for every identifier,
// verified against the input. `axis` receives the new name of `parameter`.
static std::string obfuscated(const std::string &bytes, uint64_t seed,
                              std::string &axis, const char *parameter = "n") {
  TlsfObfuscateOptions o{};
  o.mode = TLSF_OBFUSCATE_RENAME;
  o.seed = seed;
  TlsfObfuscateResult r{};
  auto status = tlsf_obfuscate(bytes.data(), bytes.size(), &o, &r);
  if (status != TLSF_OBFUSCATE_OK)
    std::cerr << "tlsf_obfuscate: " << r.message << '\n';
  CHECK(status == TLSF_OBFUSCATE_OK);
  const char *renamed =
      tlsf_obfuscate_lookup(&r, parameter, TLSF_OBFUSCATE_PARAMETER);
  CHECK(renamed);
  axis = renamed;
  std::string text(r.text, r.size);
  tlsf_obfuscate_result_clear(&r);
  return text;
}
static TlsfGr1LiftStatus fold_lift(const std::string &bytes, int size,
                                   TlsfGr1LiftOptions &o, TlsfGr1LiftResult &r,
                                   TlsfGr1LiftError &e,
                                   const char *axis = "n") {
  ParamOverride param{axis, size};
  return tlsf_gr1_lift((const uint8_t *)bytes.data(), bytes.size(), &param, 1,
                       &o, &r, &e);
}
static int fold_measure(const char *path, int size, bool both) {
  auto bytes = read_source(path);
  auto o = options();
  o.deadline_mono_ns = deadline(290);
  o.solver_nodes = o.schema_nodes = 1u << 20;
  o.solver_cache = o.schema_cache = 1u << 18;
  o.checker_nodes = 1u << 22;
  o.checker_cache = 1u << 18;
  o.budget.max_rss_bytes = uint64_t(4) << 30;
  o.disable_env_lift = 1;
  TlsfGr1LiftError e{};
  TlsfGr1LiftResult r{};
  TlsfGr1BothResult combined{};
  auto start = std::chrono::steady_clock::now();
  TlsfGr1LiftStatus status;
  if (both) {
    ParamOverride param{"n", size};
    TlsfGr1LiftTarget *target = nullptr;
    status =
        tlsf_gr1_lift_target_prepare((const uint8_t *)bytes.data(),
                                     bytes.size(), &param, 1, &o, &target, &e);
    if (status == TLSF_GR1_LIFT_OK)
      status = tlsf_gr1_both_from_target(target, &o, &combined, &e);
    tlsf_gr1_lift_target_free(target);
  } else
    status = fold_lift(bytes, size, o, r, e);
  auto &proof = both ? combined.proof : r;
  double elapsed =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - start)
          .count();
  std::cout << "n=" << size << " both=" << both << " status=" << status
            << " verdict=" << proof.verdict << " elapsed=" << elapsed
            << " stage=" << e.stage << " message=" << e.message << '\n';
  if (status == TLSF_GR1_LIFT_OK) {
    auto evidence = tlsf_json::parse(std::string_view(proof.evidence_json,
                                                      proof.evidence_size))
                        .as_object();
    std::cout << "fold=" << evidence.contains("fold") << " order="
              << (evidence.contains("checker_order")
                      ? std::string(evidence.at("checker_order").as_string())
                      : "none")
              << " route=" << (both ? int(combined.route) : -1) << '\n';
    if (evidence.contains("fold"))
      for (const auto &seed :
           evidence.at("fold").as_object().at("seeds").as_array()) {
        const auto &row = seed.as_object();
        std::cout << "seed=" << tlsf_json::serialize(row.at("parameters"))
                  << " widths=" << tlsf_json::serialize(row.at("widths"))
                  << " exact=" << row.at("exact_predicates").as_bool() << '\n';
      }
    std::cout.write(proof.check_json, proof.check_json_size);
    std::cout << '\n';
    CHECK(evidence.contains("fold"));
    CHECK(proof.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
    if (both)
      CHECK(combined.route == TLSF_GR1_BOTH_REAL_LIFT);
  } else
    std::cout << "decline_detail="
              << (both ? combined.decline_detail : r.decline_detail) << '\n';
  tlsf_gr1_lift_result_clear(&r);
  tlsf_gr1_both_result_clear(&combined);
  return status == TLSF_GR1_LIFT_OK ? 0 : 3;
}
static TlsfGr1LiftStatus
fold_both(const std::string &bytes, int size, TlsfGr1LiftOptions &o,
          TlsfGr1BothResult &r, TlsfGr1LiftError &e,
          const TlsfGr1BothObserverV1 *observer = nullptr) {
  ParamOverride param{"n", size};
  TlsfGr1LiftTarget *target = nullptr;
  CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)bytes.data(),
                                     bytes.size(), &param, 1, &o, &target,
                                     &e) == TLSF_GR1_LIFT_OK);
  auto status = tlsf_gr1_both_from_target_v1(target, &o, observer, &r, &e);
  tlsf_gr1_lift_target_free(target);
  return status;
}
struct FoldStop {
  TlsfGr1LiftOptions *options;
  const char *phase;
  int at_call;
  bool rss;
  bool active = false;
  int calls = 0;
};
static void fold_stop_phase(void *raw, const char *name, int entering,
                            const char *) {
  auto &stop = *static_cast<FoldStop *>(raw);
  if (!strcmp(name, stop.phase))
    stop.active = entering;
}
static int fold_stop(void *raw) {
  auto &stop = *static_cast<FoldStop *>(raw);
  if (!stop.active || ++stop.calls < stop.at_call)
    return 0;
  if (!stop.rss)
    return 1;
  uint64_t current = 0;
  CHECK(tlsf_current_rss_bytes(&current));
  stop.options->budget.max_rss_bytes = current / 2;
  return 0;
}
static void check_no_artifacts(const TlsfGr1LiftResult &r) {
  CHECK(r.verdict == TLSF_GR1_CHECK_UNKNOWN);
  CHECK(!r.game_aag && !r.certificate_aag && !r.certificate_json &&
        !r.policy_aag && !r.policy_json && !r.check_json && !r.evidence_json);
}
struct FoldFrontendStop {
  const TlsfGr1LiftStats &stats;
  unsigned calls = 0;
};
static int cancel_fold_frontend(void *raw) {
  auto &stop = *static_cast<FoldFrontendStop *>(raw);
  // Six legacy probes, then fold sizes 3..7. Allow parsing to finish before
  // cancelling the pathological seed's frontend work at a fixed poll count.
  return stop.stats.seed_probes ==
             TLSF_GR1_LIFT_DEFAULT_MAX_SIZES_PER_AXIS + 5 &&
         ++stop.calls >= 128;
}
static void fold_review_regressions(const char *path) {
  auto bytes = read_source(path);
  auto o = options();
  o.deadline_mono_ns = deadline(300);
  o.cancelled = never_cancelled;
  o.solver_nodes = o.schema_nodes = 1u << 20;
  o.disable_env_lift = 1;
  TlsfGr1LiftResult r{};
  TlsfGr1LiftError e{};
  TlsfGr1BothResult combined{};

  // Unequal target widths select two distinct strata, n=4 and n=8.
  CHECK(fold_lift(bytes, 16, o, r, e) == TLSF_GR1_LIFT_OK);
  auto evidence =
      tlsf_json::parse(std::string_view(r.evidence_json, r.evidence_size))
          .as_object();
  CHECK(tlsf_json::serialize(evidence.at("seed_values")) == "[4,8]");
  const auto &seeds = evidence.at("fold").as_object().at("seeds").as_array();
  CHECK(tlsf_json::serialize(seeds[0].as_object().at("widths")) == "[2,3]");
  CHECK(tlsf_json::serialize(seeds[1].as_object().at("widths")) == "[3,4]");
  CHECK(r.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  tlsf_gr1_lift_result_clear(&r);

  // Only the target's repeat obligation observes the environment. The
  // environment can alternate forever; all selected seeds still win.
  auto unreal = bytes;
  const std::string repeat_width = "i < nbits(n)]";
  CHECK(unreal.find(repeat_width) != std::string::npos);
  unreal.replace(unreal.find(repeat_width), repeat_width.size(), "i < 1]");
  unreal.insert(unreal.find("DEFINITIONS {") + strlen("DEFINITIONS {"),
                " observed(bus,i) = n < 9 : bus[i] otherwise : request[i];\n");
  const std::string repeat = "grant[i] <-> X grant[i]";
  CHECK(unreal.find(repeat) != std::string::npos);
  unreal.replace(unreal.find(repeat), repeat.size(),
                 "observed(grant,i) <-> X observed(grant,i)");
  CHECK(fold_lift(unreal, 9, o, r, e) == TLSF_GR1_LIFT_DECLINED);
  CHECK(r.verdict == TLSF_GR1_CHECK_UNKNOWN && !r.certificate_aag);
  CHECK(strstr(r.decline_detail, "fold_region_failed"));
  tlsf_gr1_lift_result_clear(&r);
  CHECK(fold_both(unreal, 9, o, combined, e) == TLSF_GR1_LIFT_OK);
  CHECK(combined.seed_polarity == TLSF_GR1_SEEDS_REAL);
  CHECK(combined.seed_solves == 3 && combined.seed_checks == 6);
  CHECK(combined.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(combined.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  CHECK(tlsf_json::parse(std::string_view(combined.proof.certificate_json,
                                          combined.proof.certificate_json_size))
            .as_object()
            .at("side")
            .as_string() == "environment");
  CHECK(strstr(combined.decline_detail, "fold_region_failed"));
  CHECK(combined.target_checks == 2);
  tlsf_gr1_both_result_clear(&combined);

  // A rejected second folded seed retains the first and interrupted checks,
  // including after the combined API's independently checked direct fallback.
  tlsf_gr1_lift_test_set_fault(9);
  CHECK(fold_both(unreal, 9, o, combined, e) == TLSF_GR1_LIFT_OK);
  CHECK(combined.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(combined.seed_checks == 5 && combined.target_checks == 1);
  CHECK(
      strstr(combined.decline_detail,
             "fold_seed_mismatch(stage=fold_seed_check,cause=applicability)"));
  CHECK(combined.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_both_result_clear(&combined);
  tlsf_gr1_lift_test_set_fault(0);

  for (int fault : {10, 11, 12, 13}) {
    tlsf_gr1_lift_test_set_fault(fault);
    CHECK(fold_lift(bytes, 9, o, r, e) == TLSF_GR1_LIFT_LIMIT);
    CHECK(strstr(r.decline_detail, "cause=resource"));
    CHECK(!strstr(r.decline_detail, "cause=error"));
    CHECK(r.verdict == TLSF_GR1_CHECK_UNKNOWN && !r.certificate_aag);
    if (fault == 13)
      CHECK(tlsf_gr1_lift_test_check_json_clears() == 1);
    tlsf_gr1_lift_result_clear(&r);
    tlsf_gr1_lift_test_set_fault(0);
  }

  // Tighten the live RSS budget inside a check callback. finish() rethrows
  // after the C checker returns; both counters must already include the call.
  for (const char *phase : {"native_fold_seed_check", "native_target_check"}) {
    FoldStop stop{&o, phase, !strcmp(phase, "native_target_check") ? 4 : 2,
                  true};
    TlsfGr1BothObserverV1 observer{};
    observer.context = &stop;
    observer.phase = fold_stop_phase;
    o.cancelled = fold_stop;
    o.cancel_ctx = &stop;
    CHECK(fold_both(bytes, 9, o, combined, e, &observer) != TLSF_GR1_LIFT_OK);
    CHECK(stop.calls >= stop.at_call);
    CHECK(combined.seed_checks ==
          (!strcmp(phase, "native_target_check") ? 6 : 4));
    CHECK(combined.target_checks ==
          (!strcmp(phase, "native_target_check") ? 1 : 0));
    CHECK(strstr(combined.decline_detail, "cause=resource"));
    CHECK(combined.proof.verdict == TLSF_GR1_CHECK_UNKNOWN);
    tlsf_gr1_both_result_clear(&combined);
    o.cancelled = nullptr;
    o.cancel_ctx = nullptr;
    o.budget.max_rss_bytes = 0;
  }

  // Old probes and the target are cheap. Only the newly reached n=7 asks
  // for a billion generated next nodes; storage growth must stop at the cap.
  auto explosion = bytes;
  explosion.insert(explosion.find("DEFINITIONS {") + strlen("DEFINITIONS {"),
                   " burst(x) = x == 7 : 1000000000 otherwise : 0;\n");
  explosion.insert(explosion.find("INVARIANTS {") + strlen("INVARIANTS {"),
                   " X[burst(n)] true;\n");
  uint64_t current = 0;
  CHECK(tlsf_current_rss_bytes(&current));
  // Reduction's existing budget also reads the process's historical peak.
  uint64_t peak = 0;
  CHECK(tlsf_peak_rss_bytes(&peak));
  o.budget.max_rss_bytes = std::max(current, peak) + (64u << 20);
  CHECK(fold_lift(explosion, 9, o, r, e) == TLSF_GR1_LIFT_LIMIT);
  CHECK(tlsf_current_rss_bytes(&current) && current < o.budget.max_rss_bytes);
  CHECK(tlsf_peak_rss_bytes(&peak) && peak <= o.budget.max_rss_bytes);
  if (!strstr(r.decline_detail, "n[7]:fold=memory_budget"))
    std::cerr << e.stage << ": " << e.message << '\n'
              << r.decline_detail << '\n';
  CHECK(strstr(r.decline_detail, "n[7]:fold=memory_budget"));
  CHECK(strstr(r.decline_detail, "cause=resource"));
  check_no_artifacts(r);
  tlsf_gr1_lift_result_clear(&r);

  // A generator that keeps allocating small terms must also stop promptly
  // during expansion, rather than waiting for the frontend call to return.
  explosion = bytes;
  explosion.insert(explosion.find("DEFINITIONS {") + strlen("DEFINITIONS {"),
                   " burst(x) = x == 7 : 1000000000 otherwise : 0;\n");
  explosion.insert(explosion.find("INVARIANTS {") + strlen("INVARIANTS {"),
                   " &&[0 <= j < burst(n)] request[0];\n");
  TlsfGr1LiftStats stats{};
  FoldFrontendStop stop{stats};
  o.stats = &stats;
  o.cancelled = cancel_fold_frontend;
  o.cancel_ctx = &stop;
  CHECK(tlsf_peak_rss_bytes(&peak));
  o.budget.max_rss_bytes = std::max(current, peak) + (64u << 20);
  CHECK(fold_lift(explosion, 9, o, r, e) == TLSF_GR1_LIFT_CANCELLED);
  CHECK(stop.calls >= 128);
  CHECK(tlsf_current_rss_bytes(&current) && current < o.budget.max_rss_bytes);
  CHECK(tlsf_peak_rss_bytes(&peak) && peak <= o.budget.max_rss_bytes);
  if (!strstr(r.decline_detail, "n[7]:fold=probe_failure"))
    std::cerr << e.stage << ": " << e.message << '\n'
              << r.decline_detail << '\n';
  CHECK(strstr(r.decline_detail, "n[7]:fold=probe_failure"));
  CHECK(strstr(r.decline_detail, "stage=expand,cause=cancelled"));
  check_no_artifacts(r);
  tlsf_gr1_lift_result_clear(&r);
}
static void legacy_depth_regressions() {
  const char *deep =
      "INFO { SEMANTICS: Mealy TARGET: Mealy } "
      "GLOBAL { PARAMETERS { extent = 5; } } "
      "MAIN { INPUTS { demand[extent]; } OUTPUTS { response[extent]; } "
      "GUARANTEES { &&[0 <= i < extent] "
      "G F (response[i] && (&&[0 <= k < 3000] true)); } }";
  auto o = options();
  o.disable_env_lift = 1;
  o.deadline_mono_ns = 0;
  TlsfGr1LiftResult r{};
  TlsfGr1LiftError e{};
  // Every target/probe contains the same deep tautology, preserving its shape.
  CHECK(lift(deep, o, &r, &e) == TLSF_GR1_LIFT_OK);
  const auto verdict = r.verdict;
  const std::string game(r.game_aag, r.game_size);
  tlsf_gr1_lift_result_clear(&r);
  o.cancelled = never_cancelled;
  TlsfGr1LiftStats stats{};
  o.stats = &stats;
  CHECK(lift(deep, o, &r, &e) == TLSF_GR1_LIFT_OK);
  CHECK(r.verdict == verdict && stats.seeds_selected >= 2);
  CHECK(std::string(r.game_aag, r.game_size) == game);
  CHECK(!strstr(r.decline_detail, "generated AST depth"));
  tlsf_gr1_lift_result_clear(&r);
}
static void fold_depth_regressions(const char *path) {
  legacy_depth_regressions();
  auto deep = read_source(path);
  deep.insert(deep.find("DEFINITIONS {") + strlen("DEFINITIONS {"),
              " burst(x) = x == 7 : 200000 otherwise : 0;\n");
  deep.insert(deep.find("INVARIANTS {") + strlen("INVARIANTS {"),
              " X[burst(n)] true;\n");
  auto o = options();
  o.disable_env_lift = 1;
  TlsfGr1LiftResult r{};
  TlsfGr1BothResult combined{};
  TlsfGr1LiftError e{};
  // The target and old probes are cheap; seed 7 reaches the depth guard
  // with budgeting activated by a callback that never cancels.
  o.deadline_mono_ns = deadline(300);
  o.cancelled = never_cancelled;
  CHECK(fold_lift(deep, 9, o, r, e) == TLSF_GR1_LIFT_LIMIT);
  CHECK(strstr(r.decline_detail, "n[7]:fold="));
  CHECK(strstr(r.decline_detail, "cause=resource"));
  CHECK(strstr(r.decline_detail, "generated AST depth exceeds limit 2000"));
  check_no_artifacts(r);
  tlsf_gr1_lift_result_clear(&r);
  // Stop the independent direct solve after observing the seed decline.
  FoldStop stop{&o, "native_direct_solve", 1, true};
  TlsfGr1BothObserverV1 observer{};
  observer.context = &stop;
  observer.phase = fold_stop_phase;
  o.cancelled = fold_stop;
  o.cancel_ctx = &stop;
  CHECK(fold_both(deep, 9, o, combined, e, &observer) == TLSF_GR1_LIFT_LIMIT);
  CHECK(strstr(combined.decline_detail, "n[7]:fold="));
  CHECK(strstr(combined.decline_detail, "cause=resource"));
  CHECK(strstr(combined.decline_detail,
               "generated AST depth exceeds limit 2000"));
  check_no_artifacts(combined.proof);
  tlsf_gr1_both_result_clear(&combined);
}
static void fold_frontend_regressions(const char *path) {
  auto bytes = read_source(path);
  auto o = options();
  o.disable_env_lift = 1;
  o.deadline_mono_ns = deadline(300);
  TlsfGr1LiftStats stats{};
  o.stats = &stats;
  uint64_t current = 0, peak = 0;
  CHECK(tlsf_current_rss_bytes(&current) && tlsf_peak_rss_bytes(&peak));
  o.budget.max_rss_bytes = std::max(current, peak) + (64u << 20);
  TlsfGr1LiftResult r{};
  TlsfGr1LiftError e{};
  for (bool wide_bus : {false, true}) {
    auto stalled = bytes;
    stalled.insert(stalled.find("DEFINITIONS {") + strlen("DEFINITIONS {"),
                   " width(x) = x == 7 : 50000 otherwise : 1;\n");
    if (wide_bus)
      stalled.insert(stalled.find("INPUTS {") + strlen("INPUTS {"),
                     " aux[width(n)];\n");
    else
      stalled.insert(stalled.find("INVARIANTS {") + strlen("INVARIANTS {"),
                     " &&[j IN ({0,1 .. width(n)} CAP "
                     "{width(n)+1,width(n)+2 .. 2*width(n)})] request[0];\n");
    // Both sources stay cheap at the target and old probes. The disjoint
    // intersection returns no generated terms; the auxiliary bus reaches
    // provenance. frontend_budget exercises these exact allocation-free scans.
    FoldFrontendStop stop{stats};
    o.cancelled = cancel_fold_frontend;
    o.cancel_ctx = &stop;
    CHECK(fold_lift(stalled, 9, o, r, e) == TLSF_GR1_LIFT_CANCELLED);
    CHECK(stop.calls >= 128);
    if (!strstr(r.decline_detail, "n[7]:fold=probe_failure"))
      std::cerr << "wide_bus=" << wide_bus << " " << e.stage << ": "
                << e.message << '\n'
                << r.decline_detail << '\n';
    CHECK(strstr(r.decline_detail, "n[7]:fold=probe_failure"));
    CHECK(strstr(r.decline_detail, "stage=expand,cause=cancelled"));
    check_no_artifacts(r);
    CHECK(tlsf_current_rss_bytes(&current) && current < o.budget.max_rss_bytes);
    tlsf_gr1_lift_result_clear(&r);
  }
}
static void fold_regressions(const char *path) {
  auto bytes = read_source(path);
  auto o = options();
  o.deadline_mono_ns = deadline(50);
  o.solver_nodes = o.schema_nodes = 1u << 20;
  o.solver_cache = o.schema_cache = 1u << 16;
  // The same width crossing as n=14; this cap also exercises the order retry.
  o.checker_nodes = 1u << 18;
  TlsfGr1LiftResult r{};
  TlsfGr1LiftError e{};
  auto status = fold_lift(bytes, 9, o, r, e);
  if (status != TLSF_GR1_LIFT_OK)
    std::cerr << e.stage << ": " << e.message << '\n'
              << r.decline_detail << '\n';
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(r.method == TLSF_GR1_CHECK_REGION &&
        r.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  auto evidence =
      tlsf_json::parse(std::string_view(r.evidence_json, r.evidence_size))
          .as_object();
  CHECK(evidence.at("seed_values").as_array().size() == 3);
  CHECK(evidence.at("seed_values").as_array()[0].as_int64() == 5);
  CHECK(evidence.at("checker_order").as_string() == "input-first");
  CHECK(strstr(r.decline_detail, "fold_region_failed(default)"));
  CHECK(evidence.at("fold").as_object().at("seeds").as_array().size() == 3);
  auto game = std::string(r.game_aag, r.game_size);
  tlsf_gr1_lift_result_clear(&r);

  ParamOverride param{"n", 9};
  TlsfGr1LiftTarget *target = nullptr;
  CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)bytes.data(),
                                     bytes.size(), &param, 1, &o, &target,
                                     &e) == TLSF_GR1_LIFT_OK);
  TlsfGr1BothResult combined{};
  o.disable_env_lift = 1;
  CHECK(tlsf_gr1_both_from_target(target, &o, &combined, &e) ==
        TLSF_GR1_LIFT_OK);
  CHECK(combined.route == TLSF_GR1_BOTH_REAL_LIFT);
  CHECK(combined.proof.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  CHECK(combined.target_checks == 2 && combined.seed_solves == 3 &&
        combined.seed_checks == 6);
  CHECK(tlsf_gr1_lift_target_matches(target, &combined.proof));
  tlsf_gr1_both_result_clear(&combined);
  tlsf_gr1_lift_target_free(target);

  // Mutate the actual candidate invariant after seed checks; the real checker
  // must reject it, leaving UNKNOWN and no published certificate.
  tlsf_gr1_lift_test_set_fault(8);
  CHECK(fold_lift(bytes, 9, o, r, e) == TLSF_GR1_LIFT_DECLINED);
  CHECK(r.verdict == TLSF_GR1_CHECK_UNKNOWN && !r.certificate_aag);
  CHECK(strstr(r.decline_detail, "fold_region_failed"));
  tlsf_gr1_lift_test_set_fault(0);
  tlsf_gr1_lift_result_clear(&r);

  // Every identifier renamed, including the recursive helpers, their
  // arguments and the binders. With unused parameters around the axis, the
  // seeds give the axis each relative position among the neutral names, so
  // neither spelling nor its order may decide which parameter is folded.
  std::string padded = bytes;
  padded.insert(padded.find("n = 14;"), "alpha = 3; omega = 1;\n");
  padded.insert(padded.find("n = 14;") + strlen("n = 14;"),
                "\nbeta = 2; gamma = 4;");
  std::vector<std::pair<const std::string *, uint64_t>> renamings{{&bytes, 11}};
  std::vector<std::string> axes;
  for (uint64_t seed = 0; seed < 64 && axes.size() < 5; seed++) {
    std::string axis;
    obfuscated(padded, seed, axis);
    if (std::find(axes.begin(), axes.end(), axis) == axes.end()) {
      axes.push_back(axis);
      renamings.push_back({&padded, seed});
    }
  }
  CHECK(axes.size() == 5);
  for (auto [source, seed] : renamings) {
    std::string axis;
    auto renamed = obfuscated(*source, seed, axis);
    CHECK(fold_lift(renamed, 9, o, r, e, axis.c_str()) == TLSF_GR1_LIFT_OK);
    CHECK(r.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
    CHECK(std::string(r.game_aag, r.game_size) == game);
    tlsf_gr1_lift_result_clear(&r);
  }

  auto broken = bytes;
  auto begin = broken.find("G F (");
  CHECK(begin != std::string::npos);
  broken.replace(begin, broken.find(';', begin) - begin, "G F request[0]");
  std::string axis;
  auto renamed = obfuscated(broken, 11, axis);
  CHECK(fold_lift(renamed, 9, o, r, e, axis.c_str()) != TLSF_GR1_LIFT_OK);
  CHECK(r.verdict == TLSF_GR1_CHECK_UNKNOWN && !r.certificate_aag);
  CHECK(strstr(r.decline_detail, "fold_seed_failed") ||
        strstr(r.decline_detail, "fold_failed"));
  tlsf_gr1_lift_result_clear(&r);

  o.phase_budget.max_seed_probes = 7;
  CHECK(fold_lift(bytes, 9, o, r, e) == TLSF_GR1_LIFT_LIMIT);
  CHECK(strstr(r.decline_detail, "fold_probe_budget"));
  CHECK(!r.certificate_aag && r.verdict == TLSF_GR1_CHECK_UNKNOWN);
  tlsf_gr1_lift_result_clear(&r);
}
int main(int argc, char **argv) {
  if (argc == 3 && !strcmp(argv[1], "--fold-depth")) {
    fold_depth_regressions(argv[2]);
    return 0;
  }
  if (argc == 3 && !strcmp(argv[1], "--fold-review")) {
    fold_review_regressions(argv[2]);
    return 0;
  }
  if (argc == 3 && !strcmp(argv[1], "--fold")) {
    fold_regressions(argv[2]);
    return 0;
  }
  if (argc == 3 && !strcmp(argv[1], "--fold-frontend")) {
    fold_frontend_regressions(argv[2]);
    return 0;
  }
  if (argc >= 4 && !strcmp(argv[1], "--fold-measure"))
    return fold_measure(argv[2], std::stoi(argv[3]), argc == 5);
  bounded_seed_declines();
  discovery_budget_declines();
  corruption_guards();
  TlsfGr1LiftResult result{};
  TlsfGr1LiftError error{};
  auto o = options();
  CHECK(lift(nonparam, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "parameters") && !result.game_aag);
  CHECK(lift(nonparam_moore, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "parameters") && !result.game_aag);
  CHECK(lift(encoded_width, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "seed_window") && !result.game_aag);
  CHECK(strstr(error.message, "no stable index axis: span[1]=encoding_width"));
  CHECK(strstr(result.decline_detail,
               "span[1]=encoding_width(stage=axis,cause=applicability)"));
  o.max_predicate_arity = 2;
  CHECK(lift(large_arity, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "bus_schema") && !result.game_aag);
  CHECK(strstr(error.message, "large_template(arity 5>2)"));
  CHECK(strstr(
      result.decline_detail,
      "span=large_template(arity 5>2)(stage=bus_schema,cause=applicability)"));
  o = options();
  o.phase_budget.max_seed_probes = 1;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!strcmp(error.stage, "seed_window") && !result.game_aag);
  CHECK(strstr(error.message, "probe_budget_exhausted"));
  CHECK(strstr(result.decline_detail,
               "extent[2]=probe_failure(stage=seed_window,"
               "cause=resource):probe_budget_exhausted"));
  tlsf_gr1_lift_result_clear(&result);
  CHECK(!result.decline_detail[0]);
  o = options();
  CHECK(lift(rank_chain, o, &result, &error) == TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "schema") &&
        strstr(error.message, "rank depth changed from") && !result.game_aag);
  o = options();
  o.cancelled = cancelled;
  CHECK(lift(source, o, &result, &error) == TLSF_GR1_LIFT_CANCELLED);
  CHECK(!result.certificate_aag);
  CHECK(!result.decline_detail[0]);
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
  CHECK(result.verdict == TLSF_GR1_CHECK_UNKNOWN);
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
