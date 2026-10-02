#include "tlsf/gr1_lift.h"
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>
#include <string>

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      std::fprintf(stderr, "line %d: %s\n", __LINE__, #x);                     \
      std::abort();                                                            \
    }                                                                          \
  } while (false)

extern "C" void tlsf_gr1_lift_test_set_fault(int);
extern "C" uint64_t tlsf_gr1_lift_test_reduction_calls();

static const char *real_source =
    "INFO { TITLE: \"repeated liveness\" SEMANTICS: Mealy TARGET: Mealy }\n"
    "GLOBAL { PARAMETERS { extent = 5; } }\n"
    "MAIN { INPUTS { demand[extent]; } OUTPUTS { response[extent]; }\n"
    "GUARANTEES { &&[0 <= i < extent] G F response[i]; } }\n";
static const char *plain_source =
    "INFO { TITLE: \"plain\" SEMANTICS: Mealy TARGET: Mealy }\n"
    "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G F b; } }\n";

static TlsfGr1BothResult run(const std::string &source, bool force_decline) {
  TlsfGr1LiftOptions options{};
  options.disable_env_lift = 1;
  options.schema_nodes = force_decline ? 1 : 0;
  options.deadline_mono_ns =
      std::chrono::duration_cast<std::chrono::nanoseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count() +
      30000000000ull;
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  tlsf_gr1_lift_test_set_fault(0);
  auto status = tlsf_gr1_lift_target_prepare_exact(
      (const uint8_t *)source.data(), source.size(), &options, &target, &error);
  CHECK(status == TLSF_GR1_LIFT_OK);
  TlsfGr1BothResult result{};
  status = tlsf_gr1_both_from_target(target, &options, &result, &error);
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "status=%d stage=%s message=%s\n", status, error.stage,
                 error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(result.target_reductions == 1);
  CHECK(result.target_checks == 1);
  CHECK(result.seed_solves <= 3);
  CHECK(tlsf_gr1_lift_test_reduction_calls() == 1 + result.seed_reductions);
  CHECK(result.route != TLSF_GR1_BOTH_ENV_LIFT);
  CHECK(tlsf_gr1_lift_target_matches(target, &result.proof));
  tlsf_gr1_lift_target_free(target);
  return result;
}

int main(int argc, char **argv) {
  CHECK(argc == 2);
  std::ifstream file(argv[1], std::ios::binary);
  CHECK(file);
  std::string unreal_source(std::istreambuf_iterator<char>{file}, {});

  auto real = run(real_source, false);
  CHECK(real.seed_polarity == TLSF_GR1_SEEDS_REAL);
  CHECK(real.seed_solves >= 2);
  CHECK(real.route == TLSF_GR1_BOTH_REAL_LIFT);
  tlsf_gr1_both_result_clear(&real);

  auto unreal = run(unreal_source, false);
  CHECK(unreal.seed_polarity == TLSF_GR1_SEEDS_UNREAL);
  CHECK(unreal.seed_solves >= 2);
  CHECK(unreal.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(unreal.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_both_result_clear(&unreal);

  auto declined = run(real_source, true);
  CHECK(declined.seed_polarity == TLSF_GR1_SEEDS_REAL);
  CHECK(declined.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(declined.decline_stage[0]);
  tlsf_gr1_both_result_clear(&declined);

  auto plain = run(plain_source, false);
  CHECK(plain.seed_solves == 0);
  CHECK(plain.route == TLSF_GR1_BOTH_DIRECT);
  tlsf_gr1_both_result_clear(&plain);
}
