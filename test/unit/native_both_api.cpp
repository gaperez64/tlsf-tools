#include "tlsf/gr1_lift.h"
#include "gr1_shared.hh"
#include "resource_usage.h"
#include <algorithm>
#include <chrono>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>
#include <new>
#include <string>
#include <vector>

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      std::fprintf(stderr, "line %d: %s\n", __LINE__, #x);                     \
      std::abort();                                                            \
    }                                                                          \
  } while (false)

// Match the caller-local allocation seam in symmetry_overlay; worker threads
// retain their allocator while every C++ allocation on the failure path fails.
static thread_local bool fail_cpp_allocations = false;
static thread_local int allocations_until_failure = -1;
void *operator new(size_t size) {
  if (!fail_cpp_allocations && allocations_until_failure != 0) {
    if (allocations_until_failure > 0)
      --allocations_until_failure;
    if (void *p = std::malloc(size ? size : 1))
      return p;
  }
  throw std::bad_alloc();
}
[[gnu::noinline]] void operator delete(void *p) noexcept { std::free(p); }
[[gnu::noinline]] void operator delete(void *p, size_t) noexcept {
  std::free(p);
}

extern "C" void tlsf_gr1_lift_test_set_fault(int);
extern "C" unsigned tlsf_gr1_lift_test_check_json_clears();
extern "C" uint64_t tlsf_gr1_lift_test_reduction_calls();
extern "C" void tlsf_gr1_both_test_set_seed_fault(int);
extern "C" void tlsf_gr1_both_test_set_candidate_ns(uint64_t);
extern "C" void tlsf_gr1_both_test_set_check_fault(int);
extern "C" void tlsf_gr1_both_test_set_env_rss_spike(size_t);
extern "C" void tlsf_gr1_env_test_swap_rehashed_game(TlsfGr1LiftTarget *,
                                                     TlsfGr1LiftTarget *);

extern "C" void tlsf_gr1_env_test_set_check_bytes(size_t);
extern "C" void tlsf_gr1_env_rank_test_set_fault(int);

struct Event {
  TlsfGr1BothEventKind kind;
  TlsfGr1BothEventRoute route;
  TlsfGr1LiftStatus failure;
  std::string stage, reason;
};
struct Observation {
  std::vector<Event> events;
  bool limit_env_checker = false;
  bool corrupt_env_binding = false;
};
static void observe(void *context, TlsfGr1BothEventKind kind,
                    TlsfGr1BothEventRoute route, int, const char *stage,
                    const char *reason, TlsfGr1LiftStatus failure) {
  auto &state = *static_cast<Observation *>(context);
  state.events.push_back({kind, route, failure, stage, reason});
  if (state.corrupt_env_binding && kind == TLSF_GR1_BOTH_EVENT_CHECK_START &&
      route == TLSF_GR1_BOTH_EVENT_U)
    tlsf_gr1_env_rank_test_set_fault(12);
  if (state.limit_env_checker && kind == TLSF_GR1_BOTH_EVENT_CHECK_START &&
      route == TLSF_GR1_BOTH_EVENT_U)
    tlsf_gr1_env_test_set_check_bytes(1);
  if (kind == TLSF_GR1_BOTH_EVENT_SELECTED &&
      route == TLSF_GR1_BOTH_EVENT_DIRECT)
    tlsf_gr1_env_test_set_check_bytes(0);
}
static void failed_fallback(const Observation &state,
                            TlsfGr1BothEventRoute route, const char *stage,
                            TlsfGr1LiftStatus cause, TlsfGr1BothEventKind kind,
                            int fault = 0) {
  unsigned stops = 0, verified = 0;
  bool direct = false;
  for (const auto &event : state.events) {
    if (event.route == route) {
      CHECK(!direct);
      if (event.kind == TLSF_GR1_BOTH_EVENT_DECLINE ||
          event.kind == TLSF_GR1_BOTH_EVENT_STOPPED)
        if (event.kind != kind)
          std::fprintf(
              stderr,
              "fault=%d route=%d event=%d cause=%d stage=%s expected_kind=%d\n",
              fault, route, event.kind, event.failure, event.stage.c_str(),
              kind);
      CHECK(event.kind != (kind == TLSF_GR1_BOTH_EVENT_STOPPED
                               ? TLSF_GR1_BOTH_EVENT_DECLINE
                               : TLSF_GR1_BOTH_EVENT_STOPPED));
      if (event.kind == kind) {
        if (event.failure != cause || event.stage != stage)
          std::fprintf(stderr, "route=%d failure=%d stage=%s expected=%s\n",
                       route, event.failure, event.stage.c_str(), stage);
        CHECK(event.failure == cause && event.stage == stage);
        ++stops;
      }
    } else if (event.route == TLSF_GR1_BOTH_EVENT_DIRECT) {
      CHECK(stops == 1);
      direct = true;
      if (event.kind == TLSF_GR1_BOTH_EVENT_VERIFIED)
        ++verified;
    }
  }
  CHECK(stops == 1 && direct && verified == 1);
}

static void stopped_fallback(const Observation &state,
                             TlsfGr1BothEventRoute route, const char *stage,
                             TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_LIMIT) {
  failed_fallback(state, route, stage, cause, TLSF_GR1_BOTH_EVENT_STOPPED);
}

struct FaultCase {
  int fault;
  TlsfGr1BothEventKind kind;
  TlsfGr1LiftStatus cause;
  const char *stage;
  const char *reason = nullptr;
};
static const FaultCase env_fault_cases[] = {
    {1, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "typed_alignment"},
    {2, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "typed_alignment"},
    {3, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "typed_alignment"},
    {4, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "typed_alignment"},
    {5, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "schema_abi"},
    {6, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "schema"},
    {7, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "typed_alignment"},
    {8, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED,
     "checker_rejected"},
    {9, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "checker_rejected"},
    {10, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "checker_rejected"},
    {12, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "target_binding"},
    {13, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "typed_alignment"},
};
static const FaultCase lift_fault_cases[] = {
    {1, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "seed_window"},
    {2, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "target_check"},
    {3, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "target_check"},
    {4, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "target_check"},
    {5, TLSF_GR1_BOTH_EVENT_VERIFIED, TLSF_GR1_LIFT_OK, "target_check"},
    {6, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "schema_abi"},
    {7, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "target_check"},
    {8, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "target_check"},
    {9, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "fold_seed_check"},
    {10, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation"},
    {11, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation"},
    {12, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation"},
    {13, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation"},
    {14, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "seed_window",
     "param_state_growth"},
    {15, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "seed_window",
     "param_ordered_domain"},
    {16, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "param_schema",
     "param_tag_transport"},
    {17, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "param_schema",
     "param_no_candidate"},
    {18, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "param_schema",
     "param_seed_mismatch"},
    {19, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED,
     "param_region_check", "param_region_failed(input-first)"},
    {20, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "param_schema",
     "param_rank_depth_changed"},
    {21, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "param_schema",
     "param_fairness_changed"},
    {22, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation",
     "host allocation failed"},
    {23, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation",
     "param_failed"},
    {24, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation",
     "fold_region_stopped"},
    {25, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation",
     "fold_region_stopped"},
    {26, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "allocation",
     "host allocation failed"},
};
static const FaultCase seed_fault_cases[] = {
    {1, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED, "seed_mixed"},
    {2, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_ERROR, "seed_error"},
    {3, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT, "schema_capacity"},
    {4, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_DEADLINE, "seed_solve"},
};
static const int binding_fault_cases[] = {1, 2};

static const char *real_source =
    "INFO { TITLE: \"repeated liveness\" SEMANTICS: Mealy TARGET: Mealy }\n"
    "GLOBAL { PARAMETERS { extent = 5; } }\n"
    "MAIN { INPUTS { demand[extent]; } OUTPUTS { response[extent]; }\n"
    "GUARANTEES { &&[0 <= i < extent] G F response[i]; } }\n";
static const char *plain_source =
    "INFO { TITLE: \"plain\" SEMANTICS: Mealy TARGET: Mealy }\n"
    "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G F b; } }\n";

static uint64_t deadline(unsigned seconds = 30) {
  auto now = std::chrono::steady_clock::now().time_since_epoch();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now).count() +
         uint64_t(seconds) * 1000000000ull;
}

static uint64_t resident_bytes() {
  uint64_t bytes = 0;
  CHECK(tlsf_current_rss_bytes(&bytes) && bytes);
  return bytes;
}

static uint64_t peak_bytes() {
  uint64_t bytes = 0;
  CHECK(tlsf_peak_rss_bytes(&bytes) && bytes);
  return bytes;
}

static void binding_error(const Observation &state) {
  CHECK(!state.events.empty());
  const auto &terminal = state.events.back();
  CHECK(terminal.kind == TLSF_GR1_BOTH_EVENT_STOPPED);
  unsigned stops = 0;
  for (const auto &event : state.events) {
    if (event.route == terminal.route) {
      CHECK(event.kind != TLSF_GR1_BOTH_EVENT_DECLINE);
      CHECK(event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED);
    }
    if (event.kind == TLSF_GR1_BOTH_EVENT_STOPPED) {
      CHECK(event.failure == TLSF_GR1_LIFT_ERROR);
      CHECK(event.stage == "target_binding");
      ++stops;
    }
  }
  CHECK(stops == 1);
}

static void check_late_binding_decline(const std::string &source, int fault) {
  TlsfGr1LiftOptions options{};
  options.deadline_mono_ns = deadline();
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)source.data(),
                                           source.size(), &options, &target,
                                           &error) == TLSF_GR1_LIFT_OK);
  tlsf_gr1_both_test_set_check_fault(fault);
  TlsfGr1BothResult result{};
  Observation state;
  state.corrupt_env_binding = fault == 3;
  const TlsfGr1BothObserverV1 observer{observe, &state};
  CHECK(tlsf_gr1_both_from_target_v1(target, &options, &observer, &result,
                                     &error) == TLSF_GR1_LIFT_DECLINED);
  binding_error(state);
  CHECK(!strcmp(error.stage, "target_binding"));
  CHECK(result.target_checks == 0);
  CHECK(!result.proof.game_aag && !result.proof.certificate_aag);
  CHECK(result.seed_polarity == (fault == 1   ? TLSF_GR1_SEEDS_REAL
                                 : fault == 3 ? TLSF_GR1_SEEDS_UNREAL
                                              : TLSF_GR1_SEEDS_NONE));
  tlsf_gr1_both_result_clear(&result);
  tlsf_gr1_both_test_set_check_fault(0);
  tlsf_gr1_env_rank_test_set_fault(0);
  tlsf_gr1_lift_target_free(target);
}

static TlsfGr1BothResult run(const std::string &source,
                             TlsfGr1LiftOptions options, int check_fault = 0,
                             Observation *observation = nullptr,
                             TlsfGr1LiftStatus expected = TLSF_GR1_LIFT_OK,
                             int disable_real_lift = -1) {
  tlsf_gr1_lift_test_set_fault(check_fault);
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  options.deadline_mono_ns = deadline();
  auto status = tlsf_gr1_lift_target_prepare_exact(
      (const uint8_t *)source.data(), source.size(), &options, &target, &error);
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "prepare status=%d stage=%s message=%s\n", status,
                 error.stage, error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  TlsfGr1BothResult result{};
  const TlsfGr1BothObserverV1 observer{observe, observation};
  if (disable_real_lift >= 0) {
    const TlsfGr1BothOptionsV2 routing{&options,
                                       observation ? &observer : nullptr,
                                       uint32_t(disable_real_lift)};
    status = tlsf_gr1_both_from_target_v2(target, &routing, &result, &error);
  } else {
    status = observation
                 ? tlsf_gr1_both_from_target_v1(target, &options, &observer,
                                                &result, &error)
                 : tlsf_gr1_both_from_target(target, &options, &result, &error);
  }
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "both status=%d stage=%s message=%s\n", status,
                 error.stage, error.message);
  CHECK(status == expected);
  CHECK(result.target_reductions == 1);
  CHECK(tlsf_gr1_lift_test_reduction_calls() == 1 + result.seed_reductions);
  CHECK(bool(tlsf_gr1_lift_target_matches(target, &result.proof)) ==
        (expected == TLSF_GR1_LIFT_OK));
  tlsf_gr1_lift_test_set_fault(0);
  tlsf_gr1_lift_target_free(target);
  return result;
}

static void corruption_fallbacks(const std::string &unreal_source) {
  for (int fault : {6, 8}) {
    const std::string source = fault == 6 ? real_source : unreal_source;
    const auto route =
        fault == 6 ? TLSF_GR1_BOTH_EVENT_R : TLSF_GR1_BOTH_EVENT_U;
    const char *stage = fault == 6 ? "schema_abi" : "target_check";
    TlsfGr1LiftOptions options{};
    options.disable_env_lift = 1;
    auto direct = run(source, options, 0, nullptr, TLSF_GR1_LIFT_OK, 1);
    options.disable_env_lift = 0;
    Observation state;
    auto recovered = run(source, options, fault, &state);
    stopped_fallback(state, route, stage, TLSF_GR1_LIFT_ERROR);
    std::string reason = fault == 6 ? "multi-member justice"
                                    : "environment proof did not verify";
    if (recovered.decline_detail[0])
      reason += std::string(": ") + recovered.decline_detail;
    for (const auto &event : state.events)
      if (event.route == route) {
        CHECK(event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED);
        if (event.kind == TLSF_GR1_BOTH_EVENT_STOPPED)
          CHECK(event.reason == reason);
      }
    CHECK(recovered.seed_polarity ==
          (fault == 6 ? TLSF_GR1_SEEDS_REAL : TLSF_GR1_SEEDS_UNREAL));
    CHECK(recovered.route == TLSF_GR1_BOTH_DIRECT);
    CHECK(recovered.target_checks == (fault == 6 ? 1u : 2u));
    CHECK(!strcmp(recovered.decline_stage, stage));
    CHECK(recovered.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
    CHECK(recovered.proof.method == TLSF_GR1_CHECK_CERTIFICATE);
    CHECK(!strcmp(recovered.proof.game_aag, direct.proof.game_aag));
    CHECK(
        !strcmp(recovered.proof.certificate_aag, direct.proof.certificate_aag));
    CHECK(!strcmp(recovered.proof.certificate_json,
                  direct.proof.certificate_json));
    CHECK(!strcmp(recovered.proof.policy_aag, direct.proof.policy_aag));
    CHECK(!strcmp(recovered.proof.policy_json, direct.proof.policy_json));
    auto legacy = run(source, options, fault);
    CHECK(legacy.route == recovered.route &&
          legacy.target_checks == recovered.target_checks);
    CHECK(legacy.proof.verdict == recovered.proof.verdict);
    CHECK(
        !strcmp(legacy.proof.certificate_aag, recovered.proof.certificate_aag));
    tlsf_gr1_both_result_clear(&legacy);
    tlsf_gr1_both_result_clear(&recovered);
    tlsf_gr1_both_result_clear(&direct);
  }
}
static void fault_census(const std::string &unreal_source,
                         const char *fold_path) {
  std::ifstream file(fold_path, std::ios::binary);
  CHECK(file);
  const std::string fold_source(std::istreambuf_iterator<char>{file}, {});
  TlsfGr1LiftOptions fold_options{};
  fold_options.deadline_mono_ns = deadline(300);
  fold_options.cancelled = [](void *) { return 0; };
  fold_options.solver_nodes = fold_options.schema_nodes = 1u << 20;
  fold_options.checker_nodes = 1u << 18;
  fold_options.solver_cache = fold_options.schema_cache =
      fold_options.checker_cache = 1u << 16;
  fold_options.max_monitor_states = 1000;
  fold_options.max_artifact_bytes = 4u << 20;
  fold_options.disable_env_lift = 1;
  const ParamOverride param{"n", 9};
  TlsfGr1LiftTarget *fold_target = nullptr;
  TlsfGr1LiftError fold_error{};
  TlsfGr1BothResult baseline{};
  Observation baseline_state;
  const TlsfGr1BothObserverV1 baseline_observer{observe, &baseline_state};
  tlsf_gr1_lift_test_set_fault(0);
  CHECK(tlsf_gr1_lift_target_prepare(
            (const uint8_t *)fold_source.data(), fold_source.size(), &param, 1,
            &fold_options, &fold_target, &fold_error) == TLSF_GR1_LIFT_OK);
  CHECK(tlsf_gr1_both_from_target_v1(fold_target, &fold_options,
                                     &baseline_observer, &baseline,
                                     &fold_error) == TLSF_GR1_LIFT_OK);
  CHECK(baseline.route == TLSF_GR1_BOTH_REAL_LIFT);
  CHECK(baseline.proof.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  CHECK(tlsf_gr1_lift_target_matches(fold_target, &baseline.proof));
  tlsf_gr1_both_result_clear(&baseline);
  tlsf_gr1_lift_target_free(fold_target);

  TlsfGr1LiftOptions options{};
  for (const auto &fault : env_fault_cases) {
    if (fault.fault == 12) {
      check_late_binding_decline(unreal_source, 3);
      continue;
    }
    tlsf_gr1_env_rank_test_set_fault(fault.fault);
    Observation state;
    auto recovered = run(unreal_source, options, 0, &state);
    failed_fallback(state, TLSF_GR1_BOTH_EVENT_U, fault.stage, fault.cause,
                    fault.kind, fault.fault);
    CHECK(recovered.route == TLSF_GR1_BOTH_DIRECT &&
          recovered.target_checks >= 1);
    CHECK(recovered.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
    tlsf_gr1_both_result_clear(&recovered);
    tlsf_gr1_env_rank_test_set_fault(0);
  }
  for (const auto &fault : lift_fault_cases) {
    if (fault.fault >= 14)
      continue; // Exercised with its own parametric fixture below.
    if (fault.fault >= 9) {
      auto source = fold_source;
      if (fault.fault == 9) {
        const std::string width = "i < nbits(n)]";
        CHECK(source.find(width) != std::string::npos);
        source.replace(source.find(width), width.size(), "i < 1]");
        CHECK(source.find("DEFINITIONS {") != std::string::npos);
        source.insert(
            source.find("DEFINITIONS {") + strlen("DEFINITIONS {"),
            " observed(bus,i) = n < 9 : bus[i] otherwise : request[i];\n");
        const std::string repeat = "grant[i] <-> X grant[i]";
        CHECK(source.find(repeat) != std::string::npos);
        source.replace(source.find(repeat), repeat.size(),
                       "observed(grant,i) <-> X observed(grant,i)");
      }
      fold_options.deadline_mono_ns = deadline(300);
      fold_target = nullptr;
      CHECK(tlsf_gr1_lift_target_prepare(
                (const uint8_t *)source.data(), source.size(), &param, 1,
                &fold_options, &fold_target, &fold_error) == TLSF_GR1_LIFT_OK);
      tlsf_gr1_lift_test_set_fault(fault.fault);
      TlsfGr1BothResult result{};
      Observation state;
      const TlsfGr1BothObserverV1 observer{observe, &state};
      const auto status = tlsf_gr1_both_from_target_v1(
          fold_target, &fold_options, &observer, &result, &fold_error);
      if (fault.fault == 9) {
        CHECK(status == TLSF_GR1_LIFT_OK);
        failed_fallback(state, TLSF_GR1_BOTH_EVENT_R, fault.stage, fault.cause,
                        fault.kind, fault.fault);
        for (const auto &event : state.events)
          if (event.route == TLSF_GR1_BOTH_EVENT_R)
            CHECK(event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED);
        CHECK(result.route == TLSF_GR1_BOTH_DIRECT);
        CHECK(result.seed_checks == 5 && result.target_checks == 1);
        CHECK(strstr(
            result.decline_detail,
            "fold_seed_mismatch(stage=fold_seed_check,cause=applicability)"));
        CHECK(result.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
        CHECK(tlsf_gr1_lift_target_matches(fold_target, &result.proof));
      } else {
        CHECK(status == TLSF_GR1_LIFT_LIMIT && fold_error.status == status);
        CHECK(!strcmp(fold_error.stage, fault.stage));
        const auto route = fault.fault == 10 ? TLSF_GR1_BOTH_EVENT_SEEDS
                                             : TLSF_GR1_BOTH_EVENT_R;
        unsigned stops = 0;
        for (const auto &event : state.events) {
          CHECK(event.kind != TLSF_GR1_BOTH_EVENT_DECLINE &&
                event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED);
          CHECK(event.route != TLSF_GR1_BOTH_EVENT_DIRECT);
          if (event.kind == TLSF_GR1_BOTH_EVENT_STOPPED) {
            CHECK(event.route == route && event.kind == fault.kind);
            CHECK(event.stage == fault.stage && event.failure == fault.cause);
            CHECK(event.reason.find(result.decline_detail) !=
                  std::string::npos);
            ++stops;
          }
        }
        CHECK(stops == 1);
        CHECK(strstr(result.decline_detail, fault.fault == 10 ? "fold_discovery"
                                            : fault.fault == 11
                                                ? "fold_failed"
                                                : "fold_region_stopped"));
        CHECK(strstr(result.decline_detail, "cause=resource"));
        CHECK(!strstr(result.decline_detail, "cause=error"));
        CHECK(result.proof.verdict == TLSF_GR1_CHECK_UNKNOWN);
        CHECK(!result.proof.game_aag && !result.proof.certificate_aag &&
              !result.proof.certificate_json && !result.proof.policy_aag &&
              !result.proof.policy_json && !result.proof.check_json &&
              !result.proof.evidence_json);
        if (fault.fault == 13)
          CHECK(tlsf_gr1_lift_test_check_json_clears() == 1);
      }
      tlsf_gr1_both_result_clear(&result);
      tlsf_gr1_lift_test_set_fault(0);
      tlsf_gr1_lift_target_free(fold_target);
      continue;
    }
    if (fault.fault == 7) {
      auto solo_options = options;
      solo_options.deadline_mono_ns = deadline();
      solo_options.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
      TlsfGr1LiftStats stats{};
      solo_options.stats = &stats;
      TlsfGr1LiftTarget *target = nullptr;
      TlsfGr1LiftError error{};
      CHECK(tlsf_gr1_lift_target_prepare_exact(
                (const uint8_t *)real_source, strlen(real_source),
                &solo_options, &target, &error) == TLSF_GR1_LIFT_OK);
      tlsf_gr1_lift_test_set_fault(fault.fault);
      TlsfGr1LiftResult proof{};
      TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_OK;
      CHECK(tlsf_gr1_lift_from_target_v1(target, &solo_options, &proof, &error,
                                         &cause) == TLSF_GR1_LIFT_DECLINED);
      CHECK(fault.kind == TLSF_GR1_BOTH_EVENT_STOPPED && cause == fault.cause);
      CHECK(error.status == TLSF_GR1_LIFT_DECLINED &&
            !strcmp(error.stage, fault.stage));
      std::string message = "unverified candidate";
      if (proof.decline_detail[0])
        message += std::string(": ") + proof.decline_detail;
      CHECK(error.message == message);
      CHECK(stats.internal_checks == 1 && !proof.game_aag &&
            !proof.certificate_aag && !proof.evidence_json);
      tlsf_gr1_lift_result_clear(&proof);
      tlsf_gr1_lift_test_set_fault(0);
      tlsf_gr1_lift_target_free(target);
      continue;
    }
    Observation state;
    auto recovered = run(fault.fault == 8 ? unreal_source : real_source,
                         options, fault.fault, &state);
    if (fault.fault == 5) {
      CHECK(recovered.route == TLSF_GR1_BOTH_REAL_LIFT &&
            recovered.target_checks == 1);
      for (const auto &event : state.events)
        CHECK(event.kind != TLSF_GR1_BOTH_EVENT_DECLINE &&
              event.kind != TLSF_GR1_BOTH_EVENT_STOPPED);
      tlsf_gr1_both_result_clear(&recovered);
      continue;
    }
    const auto route =
        fault.fault == 8 ? TLSF_GR1_BOTH_EVENT_U : TLSF_GR1_BOTH_EVENT_R;
    failed_fallback(state, route, fault.stage, fault.cause, fault.kind,
                    fault.fault);
    CHECK(recovered.route == TLSF_GR1_BOTH_DIRECT &&
          recovered.target_checks >= 1);
    CHECK(recovered.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
    tlsf_gr1_both_result_clear(&recovered);
  }
  for (const auto &fault : seed_fault_cases) {
    tlsf_gr1_both_test_set_seed_fault(fault.fault);
    Observation state;
    if (fault.fault == 4) {
      TlsfGr1LiftTarget *target = nullptr;
      TlsfGr1LiftError error{};
      CHECK(tlsf_gr1_lift_target_prepare_exact(
                (const uint8_t *)real_source, strlen(real_source), &options,
                &target, &error) == TLSF_GR1_LIFT_OK);
      options.deadline_mono_ns = deadline() - 29900000000ull;
      const TlsfGr1BothObserverV1 observer{observe, &state};
      TlsfGr1BothResult result{};
      CHECK(tlsf_gr1_both_from_target_v1(target, &options, &observer, &result,
                                         &error) == TLSF_GR1_LIFT_DEADLINE);
      CHECK(result.target_checks == 0 && !result.proof.game_aag);
      CHECK(!state.events.empty() && state.events.back().kind == fault.kind &&
            state.events.back().failure == fault.cause);
      for (const auto &event : state.events)
        CHECK(event.kind != TLSF_GR1_BOTH_EVENT_DECLINE);
      tlsf_gr1_both_result_clear(&result);
      tlsf_gr1_lift_target_free(target);
      tlsf_gr1_both_test_set_seed_fault(0);
      options = {};
      continue;
    }
    auto recovered =
        run(fault.fault == 3 ? unreal_source : real_source, options, 0, &state);
    {
      failed_fallback(state,
                      fault.fault == 3 ? TLSF_GR1_BOTH_EVENT_U
                                       : TLSF_GR1_BOTH_EVENT_SEEDS,
                      fault.stage, fault.cause, fault.kind, fault.fault);
      CHECK(recovered.route == TLSF_GR1_BOTH_DIRECT);
    }
    CHECK(recovered.target_checks == 1);
    tlsf_gr1_both_result_clear(&recovered);
    tlsf_gr1_both_test_set_seed_fault(0);
  }
  for (int fault : binding_fault_cases)
    check_late_binding_decline(fault == 1 ? real_source : plain_source, fault);
}

static void routing_ablation(const std::string &unreal_source) {
  TlsfGr1LiftOptions options{};
  options.disable_env_lift = 1;
  auto legacy = run(real_source, options);
  auto enabled = run(real_source, options, 0, nullptr, TLSF_GR1_LIFT_OK, 0);
  CHECK(enabled.route == legacy.route &&
        enabled.seed_solves == legacy.seed_solves);
  CHECK(enabled.target_checks == legacy.target_checks);
  CHECK(!strcmp(enabled.proof.certificate_aag, legacy.proof.certificate_aag));
  CHECK(!strcmp(enabled.proof.game_aag, legacy.proof.game_aag));
  tlsf_gr1_both_result_clear(&legacy);
  tlsf_gr1_both_result_clear(&enabled);

  // Force an R capacity fallback with tiny caller solver/checker limits.
  // Direct still applies its incumbent caps, in both v1 and R-off v2.
  options.schema_nodes = 1;
  options.solver_nodes = options.solver_cache = 1;
  options.checker_nodes = options.checker_cache = 1;
  Observation on, off;
  auto fallback = run(real_source, options, 0, &on);
  auto bypass = run(real_source, options, 0, &off, TLSF_GR1_LIFT_OK, 1);
  CHECK(fallback.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(bypass.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(bypass.seed_probes == 0 && bypass.seed_reductions == 0);
  CHECK(bypass.seed_solves == 0 && bypass.seed_checks == 0);
  CHECK(bypass.target_checks == 1 && bypass.target_reductions == 1);
  CHECK(bypass.decline_stage[0] == 0);
  CHECK(!strcmp(fallback.proof.game_aag, bypass.proof.game_aag));
  CHECK(!strcmp(fallback.proof.certificate_aag, bypass.proof.certificate_aag));
  CHECK(
      !strcmp(fallback.proof.certificate_json, bypass.proof.certificate_json));
  CHECK(fallback.proof.verdict == bypass.proof.verdict);
  CHECK(off.events.size() == 4);
  for (const auto &event : off.events)
    CHECK(event.route == TLSF_GR1_BOTH_EVENT_DIRECT);
  tlsf_gr1_both_result_clear(&fallback);
  tlsf_gr1_both_result_clear(&bypass);

  // The independent switches leave U available to non-ablation callers.
  options = {};
  Observation u;
  auto unreal = run(unreal_source, options, 0, &u, TLSF_GR1_LIFT_OK, 1);
  CHECK(unreal.route == TLSF_GR1_BOTH_ENV_LIFT);
  CHECK(unreal.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  CHECK(std::none_of(u.events.begin(), u.events.end(), [](const Event &event) {
    return event.route == TLSF_GR1_BOTH_EVENT_R;
  }));
  tlsf_gr1_both_result_clear(&unreal);
}

static void seed_declines() {
  const char *width =
      "INFO { TITLE: \"width\" SEMANTICS: Mealy TARGET: Mealy }\n"
      "GLOBAL { PARAMETERS { span = 8; unused = 3; } DEFINITIONS { "
      "bits(x) = x <= 1 : 1 otherwise : 1 + bits(x / 2); } }\n"
      "MAIN { INPUTS { request[bits(span)]; } OUTPUTS { selector[bits(span)]; "
      "} "
      "GUARANTEES { G F selector[0]; } }\n";
  const char *arity =
      "INFO { TITLE: \"arity\" SEMANTICS: Mealy TARGET: Mealy }\n"
      "GLOBAL { PARAMETERS { span = 6; } DEFINITIONS { "
      "pattern(n) = n < 5 : grant[0] otherwise : "
      "(grant[0] && !grant[1] && grant[2] && !grant[3] && grant[4]); } }\n"
      "MAIN { INPUTS { req[span]; } OUTPUTS { grant[span]; } GUARANTEES { "
      "G F pattern(span); } }\n";
  struct Case {
    const char *source, *reason;
    unsigned max_arity, probes;
    TlsfGr1BothEventKind event;
    TlsfGr1LiftStatus cause;
  };
  for (const auto &test :
       {Case{width, "span[1]=encoding_width(stage=axis,cause=applicability)", 0,
             0, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED},
        Case{arity,
             "span=large_template(arity "
             "5>2)(stage=bus_schema,cause=applicability)",
             2, 0, TLSF_GR1_BOTH_EVENT_DECLINE, TLSF_GR1_LIFT_DECLINED},
        Case{real_source,
             "extent[2]=probe_failure(stage=seed_window,cause=resource):probe_"
             "budget_exhausted",
             0, 1, TLSF_GR1_BOTH_EVENT_STOPPED, TLSF_GR1_LIFT_LIMIT}}) {
    TlsfGr1LiftOptions options{};
    options.disable_env_lift = 1;
    options.max_predicate_arity = test.max_arity;
    options.phase_budget.max_seed_probes = test.probes;
    Observation state;
    auto result = run(test.source, options, 0, &state, TLSF_GR1_LIFT_OK, 0);
    CHECK(result.route == TLSF_GR1_BOTH_DIRECT);
    CHECK(result.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
    CHECK(strstr(result.decline_detail, test.reason));
    if (test.source == width)
      CHECK(strstr(result.decline_detail, "unused[1]=parameter_not_indexed"));
    bool observed = false;
    for (const auto &event : state.events)
      if (event.route == TLSF_GR1_BOTH_EVENT_SEEDS &&
          event.kind == test.event) {
        CHECK(event.failure == test.cause);
        CHECK(event.reason.find(test.reason) != std::string::npos);
        if (test.event == TLSF_GR1_BOTH_EVENT_DECLINE)
          CHECK(event.reason.find("no stable index axis: ") == 0);
        observed = true;
      }
    CHECK(observed);
    tlsf_gr1_both_result_clear(&result);
    CHECK(!result.decline_detail[0]);
  }
}

static void bounded_seed_declines() {
  std::string parameters = "GLOBAL { PARAMETERS { ";
  for (int i = 0; i < 12; ++i)
    parameters += "axis" + std::to_string(i) + std::string(200, 'x') + " = 3; ";
  parameters += "} }\n";
  std::string source(plain_source);
  source.insert(source.find("MAIN"), parameters);
  TlsfGr1LiftOptions options{};
  options.deadline_mono_ns = deadline();
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)source.data(),
                                           source.size(), &options, &target,
                                           &error) == TLSF_GR1_LIFT_OK);
  for (unsigned probes : {0u, 12u}) {
    options.phase_budget.max_seed_probes = probes;
    struct {
      uint64_t before = 0x123456789abcdef0ull;
      TlsfGr1BothResult result{};
      uint64_t after = 0xfedcba9876543210ull;
    } guarded;
    auto &result = guarded.result;
    Observation state;
    const TlsfGr1BothObserverV1 observer{observe, &state, nullptr};
    CHECK(tlsf_gr1_both_from_target_v1(target, &options, &observer, &result,
                                       &error) == TLSF_GR1_LIFT_OK);
    CHECK(guarded.before == 0x123456789abcdef0ull &&
          guarded.after == 0xfedcba9876543210ull);
    CHECK(memchr(result.decline_detail, '\0', sizeof result.decline_detail));
    const std::string detail = result.decline_detail;
    CHECK(detail.ends_with("; [truncated]"));
    CHECK(detail.find("[1]=parameter_not_indexed") != std::string::npos);
    CHECK(result.route == TLSF_GR1_BOTH_DIRECT);
    CHECK(result.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
    unsigned terminal = 0;
    for (const auto &event : state.events) {
      if (event.kind != TLSF_GR1_BOTH_EVENT_DECLINE &&
          event.kind != TLSF_GR1_BOTH_EVENT_STOPPED &&
          event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED)
        continue;
      CHECK(event.reason.size() < TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE + 512);
      CHECK(event.reason.ends_with(": " + detail));
      if (event.route == TLSF_GR1_BOTH_EVENT_SEEDS) {
        CHECK(event.kind == (probes ? TLSF_GR1_BOTH_EVENT_STOPPED
                                    : TLSF_GR1_BOTH_EVENT_DECLINE));
        CHECK(event.failure ==
              (probes ? TLSF_GR1_LIFT_LIMIT : TLSF_GR1_LIFT_DECLINED));
        CHECK(event.reason.starts_with(
            probes ? "probe_budget_exhausted: fixed seed probe budget "
                     "exhausted: "
                   : "no stable index axis: "));
      }
      ++terminal;
    }
    CHECK(terminal == 2);
    tlsf_gr1_both_result_clear(&result);
    CHECK(!result.decline_detail[0]);
  }
  tlsf_gr1_lift_target_free(target);
}

static void diagnostic_branches() {
  struct Case {
    const char *definitions, *inputs, *outputs, *goal, *reason;
    bool environment = false;
    unsigned max_sizes = 0;
  };
  for (const auto &test :
       {Case{"", "req;", "grant[(extent+1)/2];", "G F grant[0];",
             "extent[1..2]=members_not_growing"},
        Case{"", "req;", "grant[extent*(6-extent)+1];", "G F grant[0];",
             "extent[1..2]=target_not_larger"},
        // The extra safety conjunct exists only at confirmation size 4.
        Case{"", "req;", "grant[extent];",
             "&&[0 <= i < extent] G F grant[i]; "
             "&&[0 <= i < 1/((extent-4)*(extent-4)+1)] G req;",
             "extent[2..4]=structural_shape_mismatch"},
        Case{"", "req;", "grant[extent];", "G F grant[0];",
             "extent[1..3]=unstable_role_classes"},
        Case{"", "req[extent];", "grant[0..extent];", "G F grant[0];",
             "extent[1]=inconsistent_coordinates(stage=axis,cause="
             "applicability)"},
        Case{"", "req;", "grant[extent];", "G F grant[0];",
             "extent[3..5]:U=probe_unavailable", true, 4},
        Case{"", "req;", "grant[extent+1];", "G F grant[0];",
             "extent[3..5]:U=member_counts", true},
        Case{"", "req;", "grant[extent];",
             "&&[0 <= i < extent] G F grant[i]; "
             "&&[5 <= i < extent] G grant[i];",
             "extent[3..5]:U=unstable_role_classes", true}}) {
    const std::string source =
        std::string("INFO { TITLE: \"diagnostic branches\" SEMANTICS: Mealy "
                    "TARGET: Mealy }\n") +
        "GLOBAL { PARAMETERS { extent = 6; } DEFINITIONS { " +
        test.definitions + " } }\nMAIN { INPUTS { " + test.inputs +
        " } OUTPUTS { " + test.outputs + " } GUARANTEES { " + test.goal +
        " } }\n";
    TlsfGr1LiftOptions options{};
    options.max_sizes_per_axis = test.max_sizes;
    options.deadline_mono_ns = deadline();
    TlsfGr1LiftTarget *target = nullptr;
    TlsfGr1LiftError error{};
    CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)source.data(),
                                             source.size(), &options, &target,
                                             &error) == TLSF_GR1_LIFT_OK);
    if (!test.environment) {
      TlsfGr1LiftResult lifted{};
      const auto status =
          tlsf_gr1_lift_from_target(target, &options, &lifted, &error);
      CHECK(status == TLSF_GR1_LIFT_OK || status == TLSF_GR1_LIFT_DECLINED);
      if (!strstr(lifted.decline_detail, test.reason))
        std::fprintf(stderr, "expected %s; lift detail: %s\n", test.reason,
                     lifted.decline_detail);
      CHECK(strstr(lifted.decline_detail, test.reason));
      tlsf_gr1_lift_result_clear(&lifted);
    }
    TlsfGr1BothResult result{};
    Observation state;
    const TlsfGr1BothObserverV1 observer{observe, &state};
    const TlsfGr1BothOptionsV2 routing{&options, &observer,
                                       uint32_t(test.environment)};
    CHECK(tlsf_gr1_both_from_target_v2(target, &routing, &result, &error) ==
          TLSF_GR1_LIFT_OK);
    if (!strstr(result.decline_detail, test.reason))
      std::fprintf(stderr, "expected %s; both detail: %s\n", test.reason,
                   result.decline_detail);
    CHECK(strstr(result.decline_detail, test.reason));
    CHECK(result.proof.verdict == TLSF_GR1_CHECK_VERIFIED ||
          result.proof.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
    CHECK(state.events.back().kind == TLSF_GR1_BOTH_EVENT_VERIFIED);
    CHECK(state.events.back().reason.find(test.reason) != std::string::npos);
    tlsf_gr1_both_result_clear(&result);
    tlsf_gr1_lift_target_free(target);
  }
}

static std::string rejected_axis(std::string source) {
  source.insert(source.find("PARAMETERS {") + strlen("PARAMETERS {"),
                " aaa = 2;");
  return source;
}

static void late_diagnostic_propagation(const std::string &unreal_source) {
  for (int fault : {0, 1, 2, 3, 6, 8}) {
    const bool unreal = fault == 3 || fault == 8;
    const auto source = rejected_axis(unreal ? unreal_source : real_source);
    TlsfGr1LiftOptions options{};
    Observation state;
    tlsf_gr1_both_test_set_seed_fault(fault < 4 ? fault : 0);
    auto result = run(source, options, fault >= 6 ? fault : 0, &state);
    tlsf_gr1_both_test_set_seed_fault(0);
    CHECK(strstr(result.decline_detail, "aaa[1]=parameter_not_indexed"));
    unsigned terminal = 0;
    for (const auto &event : state.events)
      if (event.kind == TLSF_GR1_BOTH_EVENT_DECLINE ||
          event.kind == TLSF_GR1_BOTH_EVENT_STOPPED ||
          event.kind == TLSF_GR1_BOTH_EVENT_VERIFIED) {
        CHECK(event.reason.find(result.decline_detail) != std::string::npos);
        ++terminal;
      }
    CHECK(terminal == (fault == 0 ? 1u : 2u));
    CHECK(result.route ==
          (fault == 0 ? TLSF_GR1_BOTH_REAL_LIFT : TLSF_GR1_BOTH_DIRECT));
    if (fault == 0)
      CHECK(strstr(result.decline_detail, "extent[3..5]:U=insufficient_sizes"));
    tlsf_gr1_both_result_clear(&result);
  }
}

struct AllocationObservation {
  TlsfGr1BothEventRoute fail_route;
  bool stopped = false;
  char reason[TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE + 512]{};
};
static void allocation_event(void *context, TlsfGr1BothEventKind kind,
                             TlsfGr1BothEventRoute route, int, const char *,
                             const char *reason, TlsfGr1LiftStatus cause) {
  auto &state = *static_cast<AllocationObservation *>(context);
  if (kind == TLSF_GR1_BOTH_EVENT_SELECTED && route == state.fail_route &&
      route != TLSF_GR1_BOTH_EVENT_SEEDS)
    fail_cpp_allocations = true;
  if (kind == TLSF_GR1_BOTH_EVENT_STOPPED) {
    CHECK(cause == TLSF_GR1_LIFT_LIMIT);
    state.stopped = true;
    snprintf(state.reason, sizeof state.reason, "%s", reason);
  }
}
static void allocation_phase(void *context, const char *name, int entering,
                             const char *) {
  const auto &state = *static_cast<AllocationObservation *>(context);
  if (!entering && !strcmp(name, "native_r_discovery") &&
      state.fail_route == TLSF_GR1_BOTH_EVENT_SEEDS)
    fail_cpp_allocations = true;
}
static void allocation_stats(void *, TlsfGr1LiftStatsStage stage,
                             const TlsfGr1LiftStageStats *) {
  if (stage == TLSF_GR1_LIFT_STATS_SEED_WINDOW)
    fail_cpp_allocations = true;
}
static int allocation_cancel(void *) {
  fail_cpp_allocations = true;
  return 0;
}
struct AllocationCountdown {
  int allowed;
  bool armed = false;
};
static int countdown_cancel(void *context) {
  auto &state = *static_cast<AllocationCountdown *>(context);
  if (!state.armed) {
    allocations_until_failure = state.allowed;
    state.armed = true;
  }
  return 0;
}
static int terminal_allocation_count(const TlsfGr1LiftOptions &options,
                                     const char *stage) {
  gr1_lift_internal::Config cfg{};
  cfg.o = options;
  cfg.o.cancelled = nullptr;
  cfg.budget = &options.budget;
  // Measure in isolation: exception/string allocations vary across C++
  // libraries.
  allocations_until_failure = INT_MAX;
  try {
    cfg.check(stage, true);
  } catch (const gr1_lift_internal::Failure &e) {
    const int count = INT_MAX - allocations_until_failure;
    allocations_until_failure = -1;
    CHECK(e.status == (options.deadline_mono_ns ? TLSF_GR1_LIFT_DEADLINE
                                                : TLSF_GR1_LIFT_LIMIT));
    CHECK(e.stage == (options.deadline_mono_ns ? stage : "budget-memory"));
    return count;
  }
  allocations_until_failure = -1;
  CHECK(false);
  return 0;
}
static void countdown_allocation_diagnostics() {
  TlsfGr1LiftOptions options{};
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)real_source, strlen(real_source), &options,
            &target, &error) == TLSF_GR1_LIFT_OK);
  for (bool combined : {false, true}) {
    for (bool expired : {true, false}) {
      options = {};
      options.deadline_mono_ns = expired ? 1 : 0;
      options.budget.max_rss_bytes = expired ? 0 : 1;
      options.cancelled = countdown_cancel;
      // main constructs one DEADLINE or RSS LIMIT; both retries the RSS check.
      int terminal_allocations =
          terminal_allocation_count(options, "seed_window");
      if (combined && !expired)
        terminal_allocations +=
            terminal_allocation_count(options, "direct_solve");
      for (int allowed = 0; allowed <= terminal_allocations + 2; ++allowed) {
        AllocationCountdown state{allowed};
        options.cancel_ctx = &state;
        TlsfGr1LiftResult lifted{};
        TlsfGr1BothResult both{};
        const auto status =
            combined
                ? tlsf_gr1_both_from_target(target, &options, &both, &error)
                : tlsf_gr1_lift_from_target(target, &options, &lifted, &error);
        const int remaining = allocations_until_failure;
        allocations_until_failure = -1;
        const bool constructed = allowed >= terminal_allocations;
        const auto expected = constructed && expired ? TLSF_GR1_LIFT_DEADLINE
                                                     : TLSF_GR1_LIFT_LIMIT;
        const char *stage = !constructed ? "allocation"
                            : expired    ? "seed_window"
                                         : "budget-memory";
        if (status != expected || strcmp(error.stage, stage))
          std::fprintf(stderr,
                       "combined=%d expired=%d allowed=%d status=%d stage=%s "
                       "expected=%d/%s\n",
                       combined, expired, allowed, status, error.stage,
                       expected, stage);
        CHECK(status == expected && error.status == expected);
        CHECK(state.armed && !strcmp(error.stage, stage));
        CHECK(remaining == std::max(0, allowed - terminal_allocations));
        CHECK((combined ? both.proof.verdict : lifted.verdict) ==
              TLSF_GR1_CHECK_UNKNOWN);
        CHECK(!lifted.game_aag && !both.proof.game_aag);
        tlsf_gr1_lift_result_clear(&lifted);
        tlsf_gr1_both_result_clear(&both);
      }
    }
  }
  tlsf_gr1_lift_target_free(target);
}
static void allocation_diagnostics(const std::string &unreal_source) {
  for (const auto route : {TLSF_GR1_BOTH_EVENT_SEEDS, TLSF_GR1_BOTH_EVENT_R,
                           TLSF_GR1_BOTH_EVENT_U, TLSF_GR1_BOTH_EVENT_DIRECT}) {
    const auto source = rejected_axis(
        route == TLSF_GR1_BOTH_EVENT_U ? unreal_source : real_source);
    TlsfGr1LiftOptions options{};
    options.deadline_mono_ns = deadline();
    TlsfGr1LiftTarget *target = nullptr;
    TlsfGr1LiftError error{};
    CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)source.data(),
                                             source.size(), &options, &target,
                                             &error) == TLSF_GR1_LIFT_OK);
    // Persistent OOM after a successful window must survive result cleanup.
    TlsfGr1LiftStats stats{};
    options.stats = &stats;
    options.stats_callback = allocation_stats;
    TlsfGr1LiftResult lifted{};
    auto status = tlsf_gr1_lift_from_target(target, &options, &lifted, &error);
    fail_cpp_allocations = false;
    CHECK(status == TLSF_GR1_LIFT_LIMIT);
    CHECK(strstr(lifted.decline_detail, "aaa[1]=parameter_not_indexed"));
    CHECK(!lifted.game_aag && !lifted.certificate_aag && !lifted.evidence_json);
    tlsf_gr1_lift_result_clear(&lifted);
    options.stats = nullptr;
    options.stats_callback = nullptr;
    // Fail in discovery itself to check current-axis attribution.
    options.cancelled = allocation_cancel;
    status = tlsf_gr1_lift_from_target(target, &options, &lifted, &error);
    fail_cpp_allocations = false;
    CHECK(status == TLSF_GR1_LIFT_LIMIT);
    CHECK(strstr(lifted.decline_detail,
                 "aaa[1]=probe_failure(stage=allocation,cause=resource)"));
    tlsf_gr1_lift_result_clear(&lifted);
    options.cancelled = nullptr;
    if (route == TLSF_GR1_BOTH_EVENT_DIRECT)
      options.max_sizes_per_axis = 1;
    AllocationObservation state{route};
    const TlsfGr1BothObserverV1 observer{allocation_event, &state,
                                         allocation_phase};
    TlsfGr1BothResult result{};
    status = tlsf_gr1_both_from_target_v1(target, &options, &observer, &result,
                                          &error);
    fail_cpp_allocations = false;
    CHECK(status == TLSF_GR1_LIFT_LIMIT && state.stopped);
    CHECK(strstr(result.decline_detail, "aaa[1]=parameter_not_indexed"));
    CHECK(strstr(state.reason, result.decline_detail));
    CHECK(!result.proof.game_aag && !result.proof.certificate_aag);
    tlsf_gr1_both_result_clear(&result);
    // Terminal formatting must also be safe without an observer/error output.
    for (auto *output : {&error, static_cast<TlsfGr1LiftError *>(nullptr)}) {
      fail_cpp_allocations = true;
      status = tlsf_gr1_both_from_target(target, &options, &result, output);
      fail_cpp_allocations = false;
      CHECK(status == TLSF_GR1_LIFT_LIMIT && !result.proof.game_aag);
      tlsf_gr1_both_result_clear(&result);
    }
    tlsf_gr1_lift_target_free(target);
  }
}

#include "parametric_fold_test.hh"
static void parametric_panel(const char *path) {
  std::vector<std::pair<int, const char *>> faults;
  for (const auto &f : lift_fault_cases)
    if (f.fault >= 14)
      faults.emplace_back(f.fault, f.reason);
  CHECK(faults.size() == 13);
  parametric_regressions(
      path, true, faults, [](int fault, const std::vector<ParamEvent> &events) {
        const auto expected = std::find_if(
            std::begin(lift_fault_cases), std::end(lift_fault_cases),
            [fault](const FaultCase &f) { return f.fault == fault; });
        CHECK(expected != std::end(lift_fault_cases));
        const auto route = fault <= 15 || fault == 22 || fault == 26
                               ? TLSF_GR1_BOTH_EVENT_SEEDS
                               : TLSF_GR1_BOTH_EVENT_R;
        unsigned matches = 0;
        for (const auto &event : events) {
          CHECK(event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED);
          if (event.route == route &&
              (event.kind == TLSF_GR1_BOTH_EVENT_DECLINE ||
               event.kind == TLSF_GR1_BOTH_EVENT_STOPPED)) {
            if (event.kind != expected->kind ||
                event.cause != expected->cause ||
                event.stage != expected->stage)
              std::fprintf(stderr, "param fault=%d kind=%d cause=%d stage=%s\n",
                           fault, event.kind, event.cause, event.stage.c_str());
            CHECK(event.kind == expected->kind);
            CHECK(event.cause == expected->cause);
            CHECK(event.stage == expected->stage);
            ++matches;
          }
        }
        CHECK(matches == 1);
      });
}
int main(int argc, char **argv) {
  if (argc == 3 && !strcmp(argv[1], "--param-activation")) {
    parametric_activation_regressions(argv[2], true);
    return 0;
  }
  if (argc == 3 && !strcmp(argv[1], "--param-axes")) {
    parametric_axis_regressions(argv[2], true);
    return 0;
  }
  if (argc == 3 && !strcmp(argv[1], "--param")) {
    parametric_panel(argv[2]);
    return 0;
  }
  CHECK(argc >= 2 && argc <= 5);
  std::ifstream file(argv[1], std::ios::binary);
  CHECK(file);
  std::string unreal_source(std::istreambuf_iterator<char>{file}, {});
  if (argc >= 3) {
    if (!strcmp(argv[2], "--fault-census")) {
      CHECK(argc == 5);
      fault_census(unreal_source, argv[3]);
      parametric_panel(argv[4]);
    } else {
      CHECK(argc == 3);
      CHECK(!strcmp(argv[2], "--corruption-guards"));
      corruption_fallbacks(unreal_source);
    }
    return 0;
  }
  countdown_allocation_diagnostics();
  seed_declines();
  bounded_seed_declines();
  diagnostic_branches();
  late_diagnostic_propagation(unreal_source);
  allocation_diagnostics(unreal_source);
  routing_ablation(unreal_source);
  TlsfGr1LiftOptions options{};
  auto real = run(real_source, options);
  CHECK(real.seed_polarity == TLSF_GR1_SEEDS_REAL);
  CHECK(real.route == TLSF_GR1_BOTH_REAL_LIFT);
  CHECK(real.target_checks == 1);
  CHECK(real.proof.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
  tlsf_gr1_both_result_clear(&real);

  auto unreal = run(unreal_source, options);
  CHECK(unreal.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(unreal.route == TLSF_GR1_BOTH_ENV_LIFT);
  CHECK(unreal.target_checks == 1);
  CHECK(unreal.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_both_result_clear(&unreal);

  auto plain = run(plain_source, options);
  CHECK(plain.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(plain.seed_polarity == TLSF_GR1_SEEDS_NONE);
  CHECK(plain.target_checks == 1 && plain.seed_reductions == 0);
  tlsf_gr1_both_result_clear(&plain);

  std::string too_small = real_source;
  too_small.replace(too_small.find("extent = 5"), strlen("extent = 5"),
                    "extent = 2");
  auto no_window = run(too_small, options);
  CHECK(no_window.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(no_window.seed_polarity == TLSF_GR1_SEEDS_NONE);
  tlsf_gr1_both_result_clear(&no_window);

  tlsf_gr1_both_test_set_seed_fault(1);
  auto mixed = run(real_source, options);
  CHECK(mixed.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(mixed.seed_polarity == TLSF_GR1_SEEDS_MIXED);
  CHECK(mixed.target_checks == 1);
  tlsf_gr1_both_result_clear(&mixed);
  tlsf_gr1_both_test_set_seed_fault(0);

  tlsf_gr1_both_test_set_seed_fault(2);
  Observation unknown_state;
  auto unknown = run(real_source, options, 0, &unknown_state);
  unsigned unknown_stops = 0;
  for (const auto &event : unknown_state.events) {
    CHECK(event.kind != TLSF_GR1_BOTH_EVENT_DECLINE);
    if (event.kind == TLSF_GR1_BOTH_EVENT_STOPPED) {
      CHECK(event.failure == TLSF_GR1_LIFT_ERROR &&
            event.stage == "seed_error");
      ++unknown_stops;
    }
  }
  CHECK(unknown_stops == 1);
  CHECK(unknown.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(unknown.seed_polarity == TLSF_GR1_SEEDS_UNKNOWN);
  CHECK(unknown.target_checks == 1);
  tlsf_gr1_both_result_clear(&unknown);
  tlsf_gr1_both_test_set_seed_fault(0);

  for (int fault : {2, 13}) {
    tlsf_gr1_env_rank_test_set_fault(fault);
    Observation stopped;
    auto recovered = run(unreal_source, options, 0, &stopped);
    stopped_fallback(stopped, TLSF_GR1_BOTH_EVENT_U, "typed_alignment",
                     fault == 2 ? TLSF_GR1_LIFT_ERROR : TLSF_GR1_LIFT_LIMIT);
    CHECK(recovered.route == TLSF_GR1_BOTH_DIRECT &&
          recovered.target_checks == 1);
    tlsf_gr1_both_result_clear(&recovered);
    tlsf_gr1_env_rank_test_set_fault(0);
  }

  options.schema_nodes = 1;
  Observation real_stop;
  auto real_decline = run(real_source, options, 0, &real_stop);
  stopped_fallback(real_stop, TLSF_GR1_BOTH_EVENT_R, "schema_capacity");
  CHECK(real_decline.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(real_decline.seed_polarity == TLSF_GR1_SEEDS_REAL);
  CHECK(real_decline.decline_stage[0]);
  tlsf_gr1_both_result_clear(&real_decline);
  options = {};
  auto failed_check = run(real_source, options, 3);
  CHECK(failed_check.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(failed_check.target_checks == 2);
  CHECK(!strcmp(failed_check.decline_stage, "target_check"));
  tlsf_gr1_both_result_clear(&failed_check);
  options = {};
  options.env_budget.max_rss_bytes = resident_bytes() / 2;
  Observation memory_stop;
  auto memory_decline = run(unreal_source, options, 0, &memory_stop);
  stopped_fallback(memory_stop, TLSF_GR1_BOTH_EVENT_U, "budget-memory");
  CHECK(memory_decline.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(!strcmp(memory_decline.decline_stage, "budget-memory"));
  tlsf_gr1_both_result_clear(&memory_decline);

  // Match the worker's equal general and U budgets. U crosses the share,
  // releases its allocation, and the direct solve gets the current allowance.
  options = {};
  options.deadline_mono_ns = deadline();
  TlsfGr1LiftTarget *memory_target = nullptr;
  TlsfGr1LiftError memory_error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)unreal_source.data(), unreal_source.size(),
            &options, &memory_target, &memory_error) == TLSF_GR1_LIFT_OK);
  const uint64_t before_u = resident_bytes();
  options.budget.max_rss_bytes =
      std::max(before_u, peak_bytes()) + (128u << 20);
  options.env_budget.max_rss_bytes = options.budget.max_rss_bytes;
  TlsfGr1LiftStats memory_stats{};
  options.stats = &memory_stats;
  tlsf_gr1_both_test_set_env_rss_spike(options.budget.max_rss_bytes - before_u +
                                       (128u << 20));
  TlsfGr1BothResult equal_budget_fallback{};
  auto memory_status = tlsf_gr1_both_from_target(
      memory_target, &options, &equal_budget_fallback, &memory_error);
  if (memory_status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "equal budget status=%d stage=%s message=%s\n",
                 memory_status, memory_error.stage, memory_error.message);
  CHECK(memory_status == TLSF_GR1_LIFT_OK);
  CHECK(equal_budget_fallback.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(equal_budget_fallback.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(equal_budget_fallback.target_checks == 1);
  CHECK(!strcmp(equal_budget_fallback.decline_stage, "budget-memory"));
  CHECK(memory_stats.work.peak_rss_bytes > options.budget.max_rss_bytes);
  tlsf_gr1_both_result_clear(&equal_budget_fallback);
  tlsf_gr1_both_test_set_env_rss_spike(0);
  // When the general share is exhausted too, there is no verified fallback.
  options.budget.max_rss_bytes = resident_bytes() / 2;
  TlsfGr1BothResult limited{};
  CHECK(tlsf_gr1_both_from_target(memory_target, &options, &limited,
                                  &memory_error) == TLSF_GR1_LIFT_LIMIT);
  CHECK(!strcmp(memory_error.stage, "budget-memory"));
  CHECK(!limited.proof.game_aag && !limited.proof.certificate_aag);
  CHECK(limited.proof.verdict == TLSF_GR1_CHECK_UNKNOWN);
  tlsf_gr1_both_result_clear(&limited);
  tlsf_gr1_lift_target_free(memory_target);

  options = {};
  tlsf_gr1_both_test_set_candidate_ns(1);
  Observation allowance_stop;
  auto env_decline = run(unreal_source, options, 0, &allowance_stop);
  stopped_fallback(allowance_stop, TLSF_GR1_BOTH_EVENT_U,
                   "candidate_allowance");
  CHECK(env_decline.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(env_decline.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(env_decline.target_checks == 1);
  tlsf_gr1_both_result_clear(&env_decline);
  tlsf_gr1_both_test_set_candidate_ns(0);

  tlsf_gr1_both_test_set_seed_fault(3);
  Observation capacity_stop;
  auto capacity = run(unreal_source, options, 0, &capacity_stop);
  stopped_fallback(capacity_stop, TLSF_GR1_BOTH_EVENT_U, "schema_capacity");
  CHECK(capacity.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(capacity.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(!strcmp(capacity.decline_stage, "schema_capacity"));
  tlsf_gr1_both_result_clear(&capacity);
  tlsf_gr1_both_test_set_seed_fault(0);

  options = {};
  Observation real_checker_stop;
  auto real_checker = run(real_source, options, 2, &real_checker_stop);
  stopped_fallback(real_checker_stop, TLSF_GR1_BOTH_EVENT_R, "target_check");
  CHECK(real_checker.route == TLSF_GR1_BOTH_DIRECT &&
        real_checker.target_checks == 2);
  tlsf_gr1_both_result_clear(&real_checker);
  Observation env_checker_stop;
  env_checker_stop.limit_env_checker = true;
  auto env_checker = run(unreal_source, options, 0, &env_checker_stop);
  stopped_fallback(env_checker_stop, TLSF_GR1_BOTH_EVENT_U, "target_check");
  CHECK(env_checker.route == TLSF_GR1_BOTH_DIRECT &&
        env_checker.target_checks == 2);
  tlsf_gr1_both_result_clear(&env_checker);

  options = {};
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)real_source, strlen(real_source), &options,
            &target, &error) == TLSF_GR1_LIFT_OK);
  options.deadline_mono_ns = 1;
  TlsfGr1BothResult timed{};
  CHECK(tlsf_gr1_both_from_target(target, &options, &timed, &error) ==
        TLSF_GR1_LIFT_DEADLINE);
  CHECK(timed.target_checks == 0);
  tlsf_gr1_both_result_clear(&timed);
  tlsf_gr1_lift_target_free(target);
  target = nullptr;

  options = {};
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)real_source, strlen(real_source), &options,
            &target, &error) == TLSF_GR1_LIFT_OK);
  options.deadline_mono_ns = deadline() - 27000000000ull;
  tlsf_gr1_both_test_set_seed_fault(4);
  TlsfGr1BothResult midpass{};
  CHECK(tlsf_gr1_both_from_target(target, &options, &midpass, &error) ==
        TLSF_GR1_LIFT_DEADLINE);
  CHECK(midpass.seed_solves >= 1 && midpass.target_checks == 0);
  tlsf_gr1_both_result_clear(&midpass);
  tlsf_gr1_both_test_set_seed_fault(0);
  tlsf_gr1_lift_target_free(target);
  target = nullptr;

  options = {};
  TlsfGr1LiftTarget *other = nullptr;
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)real_source, strlen(real_source), &options,
            &target, &error) == TLSF_GR1_LIFT_OK);
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)unreal_source.data(), unreal_source.size(),
            &options, &other, &error) == TLSF_GR1_LIFT_OK);
  tlsf_gr1_env_test_swap_rehashed_game(target, other);
  TlsfGr1BothResult swapped{};
  Observation binding;
  const TlsfGr1BothObserverV1 binding_observer{observe, &binding};
  CHECK(tlsf_gr1_both_from_target_v1(target, &options, &binding_observer,
                                     &swapped,
                                     &error) == TLSF_GR1_LIFT_DECLINED);
  binding_error(binding);
  CHECK(!strcmp(error.stage, "target_binding") && swapped.target_checks == 0);
  tlsf_gr1_both_result_clear(&swapped);
  tlsf_gr1_lift_target_free(target);
  tlsf_gr1_lift_target_free(other);

  target = nullptr;
  CHECK(tlsf_gr1_lift_target_prepare_exact(
            (const uint8_t *)real_source, strlen(real_source), &options,
            &target, &error) == TLSF_GR1_LIFT_OK);
  tlsf_gr1_lift_test_set_fault(1);
  TlsfGr1LiftResult invalid_seed{};
  TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_OK;
  CHECK(tlsf_gr1_lift_from_target_v1(target, &options, &invalid_seed, &error,
                                     &cause) == TLSF_GR1_LIFT_DECLINED);
  CHECK(cause == TLSF_GR1_LIFT_ERROR && !strcmp(error.stage, "seed_window"));
  CHECK(!invalid_seed.game_aag && !invalid_seed.certificate_aag);
  tlsf_gr1_lift_test_set_fault(0);
  tlsf_gr1_lift_target_free(target);

  for (int fault : binding_fault_cases)
    check_late_binding_decline(fault == 1 ? real_source : plain_source, fault);
  check_late_binding_decline(unreal_source, 3);
}
