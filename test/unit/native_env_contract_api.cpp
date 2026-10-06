// Include the implementation to exercise internal contract validators directly.
#include "../../src/lib/gr1_env_lift.cc"
#include <cassert>
using namespace gr1_lift_internal;
int main() {
  for (bool system : {false, true}) {
    bool failed = false;
    try {
      env_check_skolem_support({7}, system ? std::set<int>{7} : std::set<int>{},
                               system ? std::set<int>{} : std::set<int>{7});
    } catch (const Failure &e) {
      failed = true;
      assert(e.status == TLSF_GR1_LIFT_DECLINED &&
             e.failure_status == TLSF_GR1_LIFT_ERROR);
      assert(e.cause == FailureCause::error && e.stage == "policy_reconstruct");
    }
    assert(failed);
  }
  env_check_skolem_support({8}, {7}, {6});
  for (int fault = 0; fault != 3; ++fault) {
    Instance instance;
    instance.r.game = aig_new();
    assert(instance.r.game);
    if (fault == 0)
      aig_latch(instance.r.game, 0, 0);
    if (fault == 2) {
      aig_add_bad(instance.r.game, 0, "bad");
      const uint32_t justice[] = {0, 1};
      aig_add_justice(instance.r.game, justice, 2, "justice");
    }
    Config cfg{};
    EnvBdd bdd(cfg);
    EnvView target{};
    target.instance = &instance;
    EnvView seed{};
    TlsfGr1EnvRankResult rank{};
    TlsfGr1EnvLiftResult candidate{};
    bool failed = false;
    try {
      if (fault == 0)
        env_emit_target_ranks(bdd, target, seed, {}, cfg, rank, nullptr);
      else
        env_candidate(bdd, target, seed, {}, cfg, candidate);
    } catch (const Failure &e) {
      failed = true;
      assert(e.status == TLSF_GR1_LIFT_DECLINED &&
             e.failure_status == TLSF_GR1_LIFT_ERROR);
      assert(e.cause == FailureCause::error);
      assert(std::string(e.what()) ==
             (fault == 0   ? "target latch is unnamed"
              : fault == 1 ? "target has no unique bad predicate"
                           : "justice is not a single predicate"));
    }
    tlsf_gr1_env_rank_result_clear(&rank);
    tlsf_gr1_env_lift_result_clear(&candidate);
    assert(failed);
  }
}
