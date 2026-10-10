// Include the implementation to inspect the cause hidden by the legacy C API.
#include "../../src/lib/gr1_lift.cc"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <sstream>
#include <string>

#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #condition);     \
      std::abort();                                                            \
    }                                                                          \
  } while (0)

static std::string source(bool changed, bool renamed) {
  const std::string axis = renamed ? "extent" : "width";
  const std::string input = renamed ? "stimulus" : "req";
  const std::string output = renamed ? "response" : "ack";
  std::ostringstream result;
  result << "INFO { TITLE: \"" << (renamed ? "renamed control" : "REAL control")
         << "\" SEMANTICS: Mealy TARGET: Mealy }\n"
         << "GLOBAL { PARAMETERS { " << axis << " = 7; } }\n"
         << "MAIN { INPUTS { " << input << "[0.." << axis << "-1]; }\n"
         << "OUTPUTS { " << output << "[0.." << axis << "-1]; }\n"
         << "ASSUME { &&[0 <= i < " << axis << "] G F " << input << "[i]; }\n"
         << "GUARANTEE { &&[0 <= i < " << axis << "] G F " << output
         << "[i];\n";
  // Constant true outputs realize every valuation, including the seed window.
  // This extra source conjunct is present only beyond the seeds at 3, 4 and 5.
  if (changed)
    result << "&&[5 <= i < " << axis << "] G " << output << "[i];\n";
  result << "} }\n";
  return result.str();
}

static TlsfGr1LiftTarget *prepare(const std::string &bytes, const char *axis,
                                  int size, const TlsfGr1LiftOptions &options) {
  ParamOverride override{axis, size};
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  auto status = tlsf_gr1_lift_target_prepare(
      reinterpret_cast<const uint8_t *>(bytes.data()), bytes.size(), &override,
      1, &options, &target, &error);
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "prepare %d: %d %s %s\n", size, status, error.stage,
                 error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  return target;
}

static void real_event(void *context, TlsfGr1BothEventKind kind,
                       TlsfGr1BothEventRoute route, int unreal, const char *,
                       const char *, TlsfGr1LiftStatus) {
  if (kind == TLSF_GR1_BOTH_EVENT_CHECK_START) {
    CHECK(route == TLSF_GR1_BOTH_EVENT_DIRECT);
    CHECK(unreal == 0);
    ++*static_cast<unsigned *>(context);
  }
}

static void check_real(TlsfGr1LiftTarget *target, TlsfGr1LiftOptions options) {
  options.disable_env_lift = 1;
  unsigned checks = 0;
  TlsfGr1BothObserverV1 observer{real_event, &checks};
  TlsfGr1BothOptionsV2 routing{&options, &observer, 1};
  TlsfGr1BothResult result{};
  TlsfGr1LiftError error{};
  auto status = tlsf_gr1_both_from_target_v2(target, &routing, &result, &error);
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "direct: %d %s %s\n", status, error.stage,
                 error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(result.route == TLSF_GR1_BOTH_DIRECT);
  CHECK(result.seed_solves == 0);
  CHECK(result.target_checks == 1 && checks == 1);
  CHECK(result.proof.semantics == TLSF_GR1_EXACT);
  CHECK(result.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  CHECK(tlsf_gr1_lift_target_matches(target, &result.proof));
  tlsf_gr1_both_result_clear(&result);
}

int main() {
  TlsfGr1LiftOptions options{};
  options.solver_nodes = options.checker_nodes = 1u << 18;
  options.solver_cache = options.checker_cache = 1u << 16;
  for (bool changed : {false, true}) {
    for (bool renamed : {false, true}) {
      const auto bytes = source(changed, renamed);
      const char *axis = renamed ? "extent" : "width";
      for (int size : {3, 4, 5}) {
        auto *seed = prepare(bytes, axis, size, options);
        check_real(seed, options);
        tlsf_gr1_lift_target_free(seed);
      }
      for (int size : {7, 9}) {
        auto *target = prepare(bytes, axis, size, options);
        TlsfGr1EnvLiftResult result{};
        TlsfGr1LiftError error{};
        auto status =
            tlsf_gr1_env_lift_from_target(target, &options, &result, &error);
        const char *stage = changed ? "typed_alignment" : "seed_check";
        const char *reason = changed ? "target conjunct or role class missing"
                                     : "checked REAL seed is ineligible for U";
        // Pin the applicability cause, so limits, deadlines and errors cannot
        // pass.
        TlsfGr1EnvLiftResult typed{};
        typed.verdict = TLSF_GR1_CHECK_UNKNOWN;
        bool declined = false;
        try {
          auto cfg = env_candidate_config(&options);
          gr1_lift_internal::env_run(target->trusted, cfg, typed.rank, &typed);
          gr1_lift_internal::env_check(target->trusted, cfg, typed);
        } catch (const gr1_lift_internal::Failure &failure) {
          declined = true;
          CHECK(failure.cause ==
                gr1_lift_internal::FailureCause::applicability);
          CHECK(failure.failure_status == TLSF_GR1_LIFT_DECLINED);
          CHECK(failure.stage == stage);
          CHECK(std::strcmp(failure.what(), reason) == 0);
        }
        CHECK(declined);
        CHECK(typed.verdict != TLSF_GR1_CHECK_VERIFIED);
        CHECK(typed.target_checks == 0);
        tlsf_gr1_env_lift_result_clear(&typed);
        CHECK(status == TLSF_GR1_LIFT_DECLINED);
        CHECK(error.status == TLSF_GR1_LIFT_DECLINED);
        CHECK(std::strcmp(error.stage, stage) == 0);
        CHECK(std::strcmp(error.message, reason) == 0);
        CHECK(result.verdict != TLSF_GR1_CHECK_VERIFIED);
        CHECK(result.verdict == TLSF_GR1_CHECK_UNKNOWN);
        CHECK(result.target_checks == 0);
        CHECK(result.rank.seed_probes == 3 && result.rank.seed_reductions == 3);
        CHECK(result.rank.seed_solves == (changed ? 0u : 1u));
        CHECK(result.rank.seed_checks == (changed ? 0u : 1u));
        CHECK(!result.certificate_aag && !result.policy_aag &&
              !result.check_json);
        std::printf("size=%d renamed=%d cause=applicability stage=%s "
                    "target_checks=%llu\n",
                    size, renamed, error.stage,
                    static_cast<unsigned long long>(result.target_checks));
        tlsf_gr1_env_lift_result_clear(&result);
        check_real(target, options);
        tlsf_gr1_lift_target_free(target);
      }
    }
  }
}
