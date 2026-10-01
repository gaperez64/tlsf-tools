#include "tlsf/gr1_lift.h"

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>
#ifdef TLSF_GR1_LIFT_TEST_FAULT
extern "C" void tlsf_gr1_env_rank_test_set_fault(int);
extern "C" int tlsf_gr1_env_rank_test_alignment();
#endif

int main(int argc, char **argv) {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (argc == 2 && std::string(argv[1]) == "--alignment-selftest")
    return tlsf_gr1_env_rank_test_alignment() ? 0 : 1;
#endif
  if (argc != 3
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      && argc != 4
#endif
  )
    return 2;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (argc == 4)
    tlsf_gr1_env_rank_test_set_fault(std::atoi(argv[3]));
#endif
  std::ifstream source(argv[1], std::ios::binary);
  if (!source)
    return 2;
  std::string bytes(std::istreambuf_iterator<char>{source}, {});
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  auto status = tlsf_gr1_lift_target_prepare(
      reinterpret_cast<const uint8_t *>(bytes.data()), bytes.size(), nullptr, 0,
      nullptr, &target, &error);
  TlsfGr1EnvRankResult result{};
  if (status == TLSF_GR1_LIFT_OK)
    status = tlsf_gr1_env_rank_from_target(target, nullptr, &result, &error);
  if (status == TLSF_GR1_LIFT_OK) {
    std::ofstream out(argv[2], std::ios::binary);
    out.write(result.rank_aag, result.rank_size);
    if (!out)
      status = TLSF_GR1_LIFT_ERROR;
    std::ofstream trace(std::string(argv[2]) + ".classes.json",
                        std::ios::binary);
    trace.write(result.class_trace_json, result.class_trace_size);
    if (!trace)
      status = TLSF_GR1_LIFT_ERROR;
  }
  std::printf("status=%d stage=%s probes=%llu reductions=%llu solves=%llu "
              "checks=%llu classes=%llu projection=%llu summary=%llu "
              "anchor_free=%llu previous=%llu nodes=%llu applies=%llu "
              "cache=%llu accounted_bytes=%llu\n",
              int(status), error.stage,
              static_cast<unsigned long long>(result.seed_probes),
              static_cast<unsigned long long>(result.seed_reductions),
              static_cast<unsigned long long>(result.seed_solves),
              static_cast<unsigned long long>(result.seed_checks),
              static_cast<unsigned long long>(result.rank_classes),
              static_cast<unsigned long long>(result.projection_classes),
              static_cast<unsigned long long>(result.summary_classes),
              static_cast<unsigned long long>(result.anchor_free_classes),
              static_cast<unsigned long long>(result.previous_classes),
              static_cast<unsigned long long>(result.rank_nodes),
              static_cast<unsigned long long>(result.rank_applies),
              static_cast<unsigned long long>(result.rank_cache_entries),
              static_cast<unsigned long long>(result.rank_accounted_bytes));
  if (status != TLSF_GR1_LIFT_OK)
    std::fprintf(stderr, "%s\n", error.message);
  tlsf_gr1_env_rank_result_clear(&result);
  tlsf_gr1_lift_target_free(target);
  return status == TLSF_GR1_LIFT_OK ? 0 : 1;
}
