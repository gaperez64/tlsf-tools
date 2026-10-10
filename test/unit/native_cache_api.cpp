#include "tlsf/gr1_lift.h"
#include "tlsf/gr1_oxidd.h"
#include "oxidd_common.h"
#include "yyjson_cpp.hh"
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      std::fprintf(stderr, "line %d: %s\n", __LINE__, #x);                     \
      std::abort();                                                            \
    }                                                                          \
  } while (false)

using namespace oxidd::capi;
struct Capacity {
  size_t nodes, cache;
};
static std::vector<Capacity> managers;
extern "C" oxidd_bdd_manager_t __real_oxidd_bdd_manager_new(size_t, size_t,
                                                            uint32_t);
extern "C" oxidd_bdd_manager_t
__wrap_oxidd_bdd_manager_new(size_t nodes, size_t cache, uint32_t threads) {
  managers.push_back({nodes, cache});
  return __real_oxidd_bdd_manager_new(nodes, cache, threads);
}

static TlsfGr1BothResult solve(const std::string &source, size_t cache) {
  TlsfGr1LiftOptions options{};
  options.disable_env_lift = 1;
  options.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  options.solver_cache = options.checker_cache = options.schema_cache = cache;
  options.deadline_mono_ns =
      std::chrono::duration_cast<std::chrono::nanoseconds>(
          std::chrono::steady_clock::now().time_since_epoch())
          .count() +
      30000000000ull;
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  managers.clear();
  auto status = tlsf_gr1_lift_target_prepare_exact(
      reinterpret_cast<const uint8_t *>(source.data()), source.size(), &options,
      &target, &error);
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(target);
  // Preparing and binding the trusted target must not start BDD threads or
  // allocate an apply cache. Unsupported native inputs decline before this.
  CHECK(managers.empty());
  TlsfGr1BothResult result{};
  status = tlsf_gr1_both_from_target(target, &options, &result, &error);
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "status=%d stage=%s message=%s\n", status, error.stage,
                 error.message);
  CHECK(status == TLSF_GR1_LIFT_OK);
  CHECK(!managers.empty());
  CHECK(result.target_reductions == 1);
  CHECK(result.target_checks >= 1);
  CHECK(tlsf_gr1_lift_target_matches(target, &result.proof));
  CHECK(result.proof.verdict == TLSF_GR1_CHECK_REGION_VERIFIED ||
        result.proof.verdict == TLSF_GR1_CHECK_VERIFIED);
  CHECK(tlsf_json::parse(std::string(result.proof.certificate_json,
                                     result.proof.certificate_json_size))
            .as_object()
            .at("side")
            .as_string() == "system");
  bool saw_seed = false, smaller_checker = false;
  for (const auto &manager : managers) {
    CHECK(manager.cache > 0);
    if (manager.nodes == TLSF_GR1_LIFT_DEFAULT_SOLVER_NODES ||
        manager.nodes == TLSF_GR1_LIFT_DEFAULT_CHECKER_NODES) {
      saw_seed = true;
      if (cache)
        CHECK(manager.cache == cache);
      else if (manager.nodes == TLSF_GR1_LIFT_DEFAULT_SOLVER_NODES)
        CHECK(manager.cache < TLSF_GR1_LIFT_DEFAULT_SOLVER_CACHE);
      else {
        CHECK(manager.cache <= TLSF_GR1_LIFT_DEFAULT_CHECKER_CACHE);
        smaller_checker |= manager.cache < TLSF_GR1_LIFT_DEFAULT_CHECKER_CACHE;
      }
    }
  }
  CHECK(saw_seed);
  CHECK(cache || smaller_checker);
  tlsf_gr1_lift_target_free(target);
  return result;
}

int main() {
  CHECK(oxidd_structural_cache_capacity(0, 1u << 23) == (1u << 10));
  CHECK(oxidd_structural_cache_capacity(5, 1u << 23) == (1u << 11));
  CHECK(oxidd_structural_cache_capacity(16, 1u << 23) == (1u << 22));
  CHECK(oxidd_structural_cache_capacity(17, 1u << 23) == (1u << 23));
  CHECK(oxidd_structural_cache_capacity(UINT64_MAX, 1u << 23) == (1u << 23));
  CHECK(oxidd_structural_cache_capacity(17, 1u << 20) == (1u << 20));

  Aig *game = aig_new();
  CHECK(game);
  for (int i = 0; i < 4; ++i) {
    auto name = "input" + std::to_string(i);
    aig_input(game, name.c_str());
  }
  aig_latch(game, 0, 0);
  aig_latch(game, 0, 0);
  uint32_t predicate = 1;
  aig_add_justice(game, &predicate, 1, "goal");
  // Eight graph elements request the 1024-entry floor. Renaming and adding
  // a next-state variable copy are not inputs to the sizing rule.
  CHECK(tlsf_gr1_cache_capacity(game, 1u << 23) == (1u << 10));
  for (int i = 0; i < 10; ++i) {
    auto name = "additional" + std::to_string(i);
    aig_input(game, name.c_str());
  }
  CHECK(tlsf_gr1_cache_capacity(game, 1u << 23) == (1u << 11));

  aig_free(game);

  const std::string source =
      "INFO { TITLE: \"generated\" SEMANTICS: Mealy TARGET: Mealy }\n"
      "GLOBAL { PARAMETERS { width = 4; } }\n"
      "MAIN { INPUTS { request[width]; } OUTPUTS { response[width]; }\n"
      "GUARANTEES { &&[0 <= j < width] G F response[j]; } }\n";
  auto automatic = solve(source, 0);
  auto explicit_small = solve(source, 4096);
  auto previous = solve(source, TLSF_GR1_LIFT_DEFAULT_SOLVER_CACHE);
  for (const auto *result : {&explicit_small, &previous}) {
    CHECK(result->route == automatic.route);
    CHECK(result->proof.method == automatic.proof.method);
    CHECK(result->seed_polarity == automatic.seed_polarity);
    CHECK(result->seed_solves == automatic.seed_solves);
    CHECK(result->target_checks == automatic.target_checks);
    CHECK(result->proof.certificate_size == automatic.proof.certificate_size);
    CHECK(std::memcmp(result->proof.certificate_aag,
                      automatic.proof.certificate_aag,
                      automatic.proof.certificate_size) == 0);
  }
  tlsf_gr1_both_result_clear(&automatic);
  tlsf_gr1_both_result_clear(&explicit_small);
  tlsf_gr1_both_result_clear(&previous);
}
