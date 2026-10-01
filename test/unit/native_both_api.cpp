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
  CHECK(tlsf_gr1_both_from_target(target, &options, &result, &error) ==
        TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "target_binding"));
  CHECK(result.target_checks == 0);
  CHECK(!result.proof.game_aag && !result.proof.certificate_aag);
  CHECK(result.seed_polarity ==
        (fault == 1 ? TLSF_GR1_SEEDS_REAL : TLSF_GR1_SEEDS_NONE));
  tlsf_gr1_both_result_clear(&result);
  tlsf_gr1_both_test_set_check_fault(0);
  tlsf_gr1_lift_target_free(target);
}

static TlsfGr1BothResult run(const std::string &source,
                             TlsfGr1LiftOptions options, int check_fault = 0) {
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
  status = tlsf_gr1_both_from_target(target, &options, &result, &error);
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "both status=%d stage=%s message=%s\n", status,
                 error.stage, error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(result.target_reductions == 1);
  CHECK(tlsf_gr1_lift_test_reduction_calls() == 1 + result.seed_reductions);
  CHECK(tlsf_gr1_lift_target_matches(target, &result.proof));
  tlsf_gr1_lift_test_set_fault(0);
  tlsf_gr1_lift_target_free(target);
  return result;
}

int main(int argc, char **argv) {
  CHECK(argc == 2);
  std::ifstream file(argv[1], std::ios::binary);
  CHECK(file);
  std::string unreal_source(std::istreambuf_iterator<char>{file}, {});
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
  auto unknown = run(real_source, options);
  CHECK(unknown.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(unknown.seed_polarity == TLSF_GR1_SEEDS_UNKNOWN);
  CHECK(unknown.target_checks == 1);
  tlsf_gr1_both_result_clear(&unknown);
  tlsf_gr1_both_test_set_seed_fault(0);

  options.schema_nodes = 1;
  auto real_decline = run(real_source, options);
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
  auto memory_decline = run(unreal_source, options);
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
  auto env_decline = run(unreal_source, options);
  CHECK(env_decline.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(env_decline.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(env_decline.target_checks == 1);
  tlsf_gr1_both_result_clear(&env_decline);
  tlsf_gr1_both_test_set_candidate_ns(0);

  tlsf_gr1_both_test_set_seed_fault(3);
  auto capacity = run(unreal_source, options);
  CHECK(capacity.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(capacity.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(!strcmp(capacity.decline_stage, "schema_capacity"));
  tlsf_gr1_both_result_clear(&capacity);
  tlsf_gr1_both_test_set_seed_fault(0);

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
  CHECK(tlsf_gr1_both_from_target(target, &options, &swapped, &error) ==
        TLSF_GR1_LIFT_DECLINED);
  CHECK(!strcmp(error.stage, "target_binding") && swapped.target_checks == 0);
  tlsf_gr1_both_result_clear(&swapped);
  tlsf_gr1_lift_target_free(target);
  tlsf_gr1_lift_target_free(other);

  check_late_binding_decline(real_source, 1);
  check_late_binding_decline(plain_source, 2);
}
