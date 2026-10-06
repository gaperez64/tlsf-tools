#include "gr1_shared.hh"
#include <tlsf/gr1_oxidd.h>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>

namespace gr1_lift_internal {
void solve_seed(Instance &, const Config &);
void env_solve_seed(Instance &, const Config &, TlsfGr1EnvRankResult &);
TlsfGr1SeedPolarity solve_shared_seed(Instance &, const Config &,
                                      TlsfGr1BothResult &);
FailureCause solver_failure_cause(OxiddFailureKind);
} // namespace gr1_lift_internal
using namespace gr1_lift_internal;

static void validators() {
  // All four game shape checks are invariants for trusted reductions.
  for (const char *aag : std::initializer_list<const char *>{
           nullptr, "aag 0 0 0 0 0\n", "aag 0 0 0 0 0 0 1 1 0\n0\n1\n0\n",
           "aag 0 0 0 0 0 0 0 1 0\n2\n0\n0\n",
           "aag 1 0 1 0 0 0 0 1 0\n2 2 2\n1\n0\n"}) {
    for (int caller = 0; caller != 3; ++caller) {
      Instance seed;
      if (aag) {
        auto stream = fmemopen(const_cast<char *>(aag), std::strlen(aag), "r");
        seed.r.game = aig_read_aag(stream);
        fclose(stream);
        assert(seed.r.game);
      }
      Config cfg{};
      TlsfGr1EnvRankResult env{};
      TlsfGr1BothResult both{};
      bool failed = false;
      try {
        if (caller == 0)
          solve_seed(seed, cfg);
        else if (caller == 1)
          env_solve_seed(seed, cfg, env);
        else
          solve_shared_seed(seed, cfg, both);
      } catch (const Failure &e) {
        failed = true;
        assert(e.status == TLSF_GR1_LIFT_DECLINED);
        assert(e.failure_status == TLSF_GR1_LIFT_ERROR);
        assert(e.cause == FailureCause::error && e.stage == "seed_solve");
      }
      assert(failed);
    }
  }
  // Assert every checker status/verdict pair, including invalid/inconclusive
  // OK.
  for (int status = TLSF_GR1_CHECK_OK; status <= TLSF_GR1_CHECK_ERROR; ++status)
    for (int verdict = TLSF_GR1_CHECK_VERIFIED;
         verdict <= TLSF_GR1_CHECK_INVALID; ++verdict) {
      auto expected =
          status == TLSF_GR1_CHECK_LIMIT       ? FailureCause::resource
          : status == TLSF_GR1_CHECK_DEADLINE  ? FailureCause::deadline
          : status == TLSF_GR1_CHECK_CANCELLED ? FailureCause::cancelled
          : status == TLSF_GR1_CHECK_OK &&
                  (verdict == TLSF_GR1_CHECK_CERT_FAILED ||
                   verdict == TLSF_GR1_CHECK_REFUTED)
              ? FailureCause::applicability
              : FailureCause::error;
      assert(check_failure_cause(static_cast<TlsfGr1CheckStatus>(status),
                                 static_cast<TlsfGr1CheckVerdict>(verdict)) ==
             expected);
    }
  for (int kind = OXIDD_FAILURE_NONE; kind <= OXIDD_FAILURE_ARTIFACT_LIMIT;
       ++kind) {
    auto k = static_cast<OxiddFailureKind>(kind);
    auto expected = k == OXIDD_FAILURE_BDD || k == OXIDD_FAILURE_HOST ||
                            k == OXIDD_FAILURE_ARTIFACT_LIMIT
                        ? FailureCause::resource
                    : k == OXIDD_FAILURE_DEADLINE  ? FailureCause::deadline
                    : k == OXIDD_FAILURE_CANCELLED ? FailureCause::cancelled
                                                   : FailureCause::error;
    assert(solver_failure_cause(k) == expected);
  }
}
int main(int argc, char **argv) {
  if (argc == 1) {
    validators();
    return 0;
  }
  assert(argc == 3);
  setenv("ACACIA_NATIVE_TEST_CONTRACT", argv[1], 1);
  std::ifstream file(argv[2]);
  std::string source(std::istreambuf_iterator<char>{file}, {});
  assert(!source.empty());
  bool recovered = !std::strcmp(argv[1], "provenance-recover");
  bool unsupported = !std::strcmp(argv[1], "unsupported-class");
  for (bool exact : {true, false}) {
    TlsfGr1LiftTarget *target = nullptr;
    TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_CANCELLED;
    TlsfGr1LiftError error{};
    TlsfGr1LiftOptions options{};
    options.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
    auto status = exact ? tlsf_gr1_lift_target_prepare_exact_v1(
                              (const uint8_t *)source.data(), source.size(),
                              &options, &target, &error, &cause)
                        : tlsf_gr1_lift_target_prepare_v1(
                              (const uint8_t *)source.data(), source.size(),
                              nullptr, 0, &options, &target, &error, &cause);
    assert(error.status == status);
    assert(status ==
           (!exact && recovered ? TLSF_GR1_LIFT_OK : TLSF_GR1_LIFT_DECLINED));
    assert(cause == (!exact && recovered ? TLSF_GR1_LIFT_OK
                     : unsupported       ? TLSF_GR1_LIFT_DECLINED
                                         : TLSF_GR1_LIFT_ERROR));
    assert(bool(target) == (!exact && recovered));
    tlsf_gr1_lift_target_free(target);
    target = nullptr;
    auto legacy =
        exact
            ? tlsf_gr1_lift_target_prepare_exact((const uint8_t *)source.data(),
                                                 source.size(), &options,
                                                 &target, nullptr)
            : tlsf_gr1_lift_target_prepare((const uint8_t *)source.data(),
                                           source.size(), nullptr, 0, &options,
                                           &target, nullptr);
    assert(legacy == status);
    tlsf_gr1_lift_target_free(target);
  }
  TlsfGr1LiftTarget *invalid = nullptr;
  TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_CANCELLED;
  assert(tlsf_gr1_lift_target_prepare_exact_v1(nullptr, 0, nullptr, &invalid,
                                               nullptr, &cause) ==
         TLSF_GR1_LIFT_INVALID);
  assert(cause == TLSF_GR1_LIFT_INVALID);
  assert(tlsf_gr1_lift_target_prepare_v1(nullptr, 0, nullptr, 0, nullptr,
                                         &invalid, nullptr,
                                         &cause) == TLSF_GR1_LIFT_INVALID);
  assert(cause == TLSF_GR1_LIFT_INVALID);
  // Exercise the reduction boundary independently of preparation.
  if (!std::strcmp(argv[1], "provenance-duplicate") ||
      !std::strcmp(argv[1], "provenance-retry") ||
      !std::strcmp(argv[1], "provenance-recover"))
    return 0;
  TlsfPipelineOptions po{};
  po.certify = true;
  po.template_mask = TPL_ALL;
  auto pipeline = tlsf_pipeline_load_bytes((const uint8_t *)source.data(),
                                           source.size(), &po);
  assert(pipeline);
  TlsfGr1ReductionOptions ro{};
  ro.max_artifact_bytes = 64u << 20;
  ro.max_monitor_states = 10000;
  TlsfGr1Reduction result{};
  TlsfGr1ReductionStatus diagnostic = TLSF_GR1_REDUCE_OK;
  assert(tlsf_gr1_reduce_v1(pipeline, &ro, &result, nullptr, &diagnostic) ==
         TLSF_GR1_REDUCE_UNSUPPORTED);
  assert(diagnostic ==
         (unsupported ? TLSF_GR1_REDUCE_UNSUPPORTED : TLSF_GR1_REDUCE_ERROR));
  assert(!result.game && !result.aag);
  assert(tlsf_gr1_reduce(pipeline, &ro, &result, nullptr) ==
         TLSF_GR1_REDUCE_UNSUPPORTED);
  tlsf_pipeline_free(pipeline);
}
