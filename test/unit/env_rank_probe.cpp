#include "tlsf/gr1_lift.h"

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>
#include <cstdlib>
#ifdef TLSF_GR1_LIFT_TEST_FAULT
extern "C" void tlsf_gr1_env_rank_test_set_fault(int);
extern "C" int tlsf_gr1_env_rank_test_alignment();
extern "C" void tlsf_gr1_lift_test_corrupt_prepared_game(TlsfGr1LiftTarget *);
extern "C" void tlsf_gr1_env_test_swap_rehashed_game(TlsfGr1LiftTarget *,
                                                     TlsfGr1LiftTarget *);
#endif

int main(int argc, char **argv) {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (argc == 2 && std::string(argv[1]) == "--alignment-selftest")
    return tlsf_gr1_env_rank_test_alignment() ? 0 : 1;
#endif
  std::string mode = argc >= 4 ? argv[3] : "";
  bool lift = mode == "--lift" || mode == "--candidate" ||
              mode.starts_with("--lift-fault=") || mode == "--deadline" ||
              mode == "--allowance" || mode == "--corrupt-game" ||
              mode == "--rss" || mode.starts_with("--swap-source=");
  bool checked = lift && mode != "--candidate";
  if (argc != 3 && !lift
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      && argc != 4
#endif
  )
    return 2;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (argc == 4 && (!lift || mode.starts_with("--lift-fault=")))
    tlsf_gr1_env_rank_test_set_fault(std::atoi(
        mode.starts_with("--lift-fault=") ? mode.c_str() + 13 : mode.c_str()));
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
  TlsfGr1LiftTarget *other = nullptr;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (status == TLSF_GR1_LIFT_OK && mode == "--corrupt-game")
    tlsf_gr1_lift_test_corrupt_prepared_game(target);
  if (status == TLSF_GR1_LIFT_OK && mode.starts_with("--swap-source=")) {
    std::ifstream second(mode.substr(14), std::ios::binary);
    if (!second)
      return 2;
    std::string data(std::istreambuf_iterator<char>{second}, {});
    status = tlsf_gr1_lift_target_prepare(
        reinterpret_cast<const uint8_t *>(data.data()), data.size(), nullptr, 0,
        nullptr, &other, &error);
    if (status == TLSF_GR1_LIFT_OK)
      tlsf_gr1_env_test_swap_rehashed_game(target, other);
  }
#endif
  TlsfGr1EnvRankResult result{};
  TlsfGr1EnvLiftResult lifted{};
  TlsfGr1LiftOptions options{};
  if (mode == "--deadline")
    options.deadline_mono_ns = 1;
  if (mode == "--allowance")
    options.env_candidate_ns = 1;
  if (mode == "--rss")
    options.env_budget.max_rss_bytes = 1;
  const TlsfGr1LiftOptions *selected_options =
      mode == "--deadline" || mode == "--allowance" || mode == "--rss"
          ? &options
          : nullptr;
  if (status == TLSF_GR1_LIFT_OK && lift)
    status = checked ? tlsf_gr1_env_lift_from_target(target, selected_options,
                                                     &lifted, &error)
                     : tlsf_gr1_env_candidate_from_target(
                           target, selected_options, &lifted, &error);
  else if (status == TLSF_GR1_LIFT_OK)
    status = tlsf_gr1_env_rank_from_target(target, nullptr, &result, &error);
  if (lift && status == TLSF_GR1_LIFT_OK) {
    auto write = [&](const std::string &suffix, const char *data, size_t size) {
      std::ofstream file(std::string(argv[2]) + suffix, std::ios::binary);
      file.write(data, size);
      return bool(file);
    };
    if (!write(".cert.aag", lifted.certificate_aag, lifted.certificate_size) ||
        !write(".cert.aag.json", lifted.certificate_json,
               lifted.certificate_json_size) ||
        !write(".policy.aag", lifted.policy_aag, lifted.policy_size) ||
        !write(".policy.aag.json", lifted.policy_json, lifted.policy_json_size))
      status = TLSF_GR1_LIFT_ERROR;
  }
  if (status == TLSF_GR1_LIFT_OK && !lift) {
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
  if (lift)
    std::printf("status=%d stage=%s checks=%llu nodes=%llu applies=%llu "
                "verdict=%d seed_ns=%llu preflight_ns=%llu rank_ns=%llu "
                "policy_ns=%llu check_ns=%llu\n",
                int(status), error.stage,
                static_cast<unsigned long long>(lifted.target_checks),
                static_cast<unsigned long long>(lifted.policy_nodes),
                static_cast<unsigned long long>(lifted.policy_applies),
                int(lifted.verdict),
                static_cast<unsigned long long>(lifted.seed_ns),
                static_cast<unsigned long long>(lifted.preflight_ns),
                static_cast<unsigned long long>(lifted.rank_ns),
                static_cast<unsigned long long>(lifted.policy_ns),
                static_cast<unsigned long long>(lifted.check_ns));
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
  tlsf_gr1_env_lift_result_clear(&lifted);
  tlsf_gr1_lift_target_free(other);
  tlsf_gr1_lift_target_free(target);
  return status == TLSF_GR1_LIFT_OK ? 0 : 1;
}
