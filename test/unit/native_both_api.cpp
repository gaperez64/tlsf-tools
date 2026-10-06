#include "tlsf/gr1_lift.h"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>
#include <string>
#include <sys/resource.h>
#include <vector>

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      std::fprintf(stderr, "line %d: %s\n", __LINE__, #x);                     \
      std::abort();                                                            \
    }                                                                          \
  } while (false)

extern "C" void tlsf_gr1_lift_test_set_fault(int);
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
  std::string stage;
};
struct Observation {
  std::vector<Event> events;
  bool limit_env_checker = false;
  bool corrupt_env_binding = false;
};
static void observe(void *context, TlsfGr1BothEventKind kind,
                    TlsfGr1BothEventRoute route, int, const char *stage,
                    const char *, TlsfGr1LiftStatus failure) {
  auto &state = *static_cast<Observation *>(context);
  state.events.push_back({kind, route, failure, stage});
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

static uint64_t deadline() {
  auto now = std::chrono::steady_clock::now().time_since_epoch();
  return std::chrono::duration_cast<std::chrono::nanoseconds>(now).count() +
         30000000000ull;
}

static uint64_t resident_bytes() {
  FILE *file = std::fopen("/proc/self/status", "r");
  CHECK(file);
  char line[256];
  uint64_t bytes = 0;
  while (std::fgets(line, sizeof line, file)) {
    unsigned long long kb = 0;
    if (std::sscanf(line, "VmRSS: %llu kB", &kb) == 1) {
      bytes = kb * 1024u;
      break;
    }
  }
  std::fclose(file);
  CHECK(bytes);
  return bytes;
}

static uint64_t peak_bytes() {
  rusage usage{};
  CHECK(getrusage(RUSAGE_SELF, &usage) == 0);
  return uint64_t(usage.ru_maxrss) * 1024u;
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

static void fault_census(const std::string &unreal_source) {
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
    Observation state;
    auto recovered = run(real_source, options, fault.fault, &state);
    if (fault.fault == 5) {
      CHECK(recovered.route == TLSF_GR1_BOTH_REAL_LIFT &&
            recovered.target_checks == 1);
      for (const auto &event : state.events)
        CHECK(event.kind != TLSF_GR1_BOTH_EVENT_DECLINE &&
              event.kind != TLSF_GR1_BOTH_EVENT_STOPPED);
      tlsf_gr1_both_result_clear(&recovered);
      continue;
    }
    const auto route = TLSF_GR1_BOTH_EVENT_R;
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

int main(int argc, char **argv) {
  CHECK(argc == 2 || argc == 3);
  std::ifstream file(argv[1], std::ios::binary);
  CHECK(file);
  std::string unreal_source(std::istreambuf_iterator<char>{file}, {});
  if (argc == 3) {
    CHECK(!strcmp(argv[2], "--fault-census"));
    fault_census(unreal_source);
    return 0;
  }
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
  options.env_budget.max_rss_bytes = 1;
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
