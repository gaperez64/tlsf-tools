#include <tlsf/gr1_lift.h>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      std::fprintf(stderr, "line %d: %s\n", __LINE__, #x);                     \
      std::abort();                                                            \
    }                                                                          \
  } while (false)

static TlsfGr1LiftOptions options() {
  TlsfGr1LiftOptions result{};
  result.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
  result.disable_env_lift = 1;
  result.solver_nodes = result.checker_nodes = result.schema_nodes = 1u << 18;
  result.solver_cache = result.checker_cache = result.schema_cache = 1u << 16;
  result.max_artifact_bytes = 4u << 20;
  result.max_monitor_states = 1000;
  return result;
}

static void write(const std::filesystem::path &path, const char *bytes,
                  size_t size) {
  CHECK(bytes || !size);
  std::ofstream output(path, std::ios::binary);
  if (size)
    output.write(bytes, size);
  CHECK(output.good());
}

static void dump(const std::filesystem::path &directory,
                 const TlsfGr1LiftResult &result) {
  std::filesystem::create_directories(directory);
  write(directory / "game.aag", result.game_aag, result.game_size);
  write(directory / "certificate.aag", result.certificate_aag,
        result.certificate_size);
  write(directory / "certificate.json", result.certificate_json,
        result.certificate_json_size);
  write(directory / "policy.aag", result.policy_aag, result.policy_size);
  write(directory / "policy.json", result.policy_json, result.policy_json_size);
  write(directory / "check.json", result.check_json, result.check_json_size);
  write(directory / "evidence.json", result.evidence_json,
        result.evidence_size);
  auto record = std::to_string(result.method) + " " +
                std::to_string(result.verdict) + "\n";
  write(directory / "record.txt", record.data(), record.size());
}

static void run(const std::string &source, const std::filesystem::path &root,
                bool unreal) {
  auto opts = options();
  opts.disable_env_lift = !unreal;
  TlsfGr1LiftTarget *target = nullptr;
  TlsfGr1LiftError error{};
  CHECK(tlsf_gr1_lift_target_prepare_exact((const uint8_t *)source.data(),
                                           source.size(), &opts, &target,
                                           &error) == TLSF_GR1_LIFT_OK);
  // Compile this same public-API client against the incumbent without v2.
  const char *apis[] = {
      "legacy",
      "v1",
#ifdef TLSF_TYPED_ROLES_API
      "v2-null",
      "v2-off",
#endif
  };
  for (size_t api = 0; api < sizeof(apis) / sizeof(*apis); api++) {
#ifdef TLSF_TYPED_ROLES_API
    TlsfGr1TypedRolesV1 off{};
#endif
    if (!unreal) {
      TlsfGr1LiftResult result{};
      TlsfGr1LiftStatus cause{};
      auto status = TLSF_GR1_LIFT_INVALID;
      if (api == 0)
        status = tlsf_gr1_lift_from_target(target, &opts, &result, &error);
      else if (api == 1)
        status = tlsf_gr1_lift_from_target_v1(target, &opts, &result, &error,
                                              &cause);
#ifdef TLSF_TYPED_ROLES_API
      else
        status = tlsf_gr1_lift_from_target_v2(
            target, &opts, &result, &error, &cause, api == 2 ? nullptr : &off);
#endif
      CHECK(status == TLSF_GR1_LIFT_OK && cause == TLSF_GR1_LIFT_OK);
      CHECK(result.method == TLSF_GR1_CHECK_REGION);
      CHECK(result.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
      CHECK(tlsf_gr1_lift_target_matches(target, &result));
      dump(root / "pure-R" / apis[api], result);
      tlsf_gr1_lift_result_clear(&result);
    }
    TlsfGr1BothResult both{};
    auto status = TLSF_GR1_LIFT_INVALID;
    if (api == 0)
      status = tlsf_gr1_both_from_target(target, &opts, &both, &error);
    else if (api == 1)
      status =
          tlsf_gr1_both_from_target_v1(target, &opts, nullptr, &both, &error);
#ifdef TLSF_TYPED_ROLES_API
    else
      status = tlsf_gr1_both_from_target_v2(target, &opts, nullptr, &both,
                                            &error, api == 2 ? nullptr : &off);
#endif
    CHECK(status == TLSF_GR1_LIFT_OK);
    CHECK(both.route ==
          (unreal ? TLSF_GR1_BOTH_ENV_LIFT : TLSF_GR1_BOTH_REAL_LIFT));
    CHECK(both.target_checks == 1 && both.target_reductions == 1);
    CHECK(both.proof.verdict ==
          (unreal ? TLSF_GR1_CHECK_VERIFIED : TLSF_GR1_CHECK_REGION_VERIFIED));
    CHECK(tlsf_gr1_lift_target_matches(target, &both.proof));
    dump(root / (unreal ? "combined-U" : "combined-R") / apis[api], both.proof);
    tlsf_gr1_both_result_clear(&both);
  }
  tlsf_gr1_lift_target_free(target);
}

int main(int argc, char **argv) {
  CHECK(argc == 3);
  const std::string real =
      "INFO { TITLE: \"artifact control\" SEMANTICS: Mealy TARGET: Mealy }\n"
      "GLOBAL { PARAMETERS { width = 5; } }\n"
      "MAIN { INPUTS { request[width]; } OUTPUTS { response[width]; } "
      "GUARANTEES { &&[0 <= i < width] G F response[i]; } }\n";
  run(real, argv[1], false);
  std::ifstream fixture(argv[2]);
  CHECK(fixture.good());
  std::string unreal((std::istreambuf_iterator<char>(fixture)), {});
  CHECK(!unreal.empty());
  run(unreal, argv[1], true);
}
