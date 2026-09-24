#include "tlsf/native.h"

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

int main() {
  const std::string source =
      "INFO { TITLE: \"small\" DESCRIPTION: \"small\" SEMANTICS: Mealy "
      "TARGET: Mealy }\n"
      "MAIN { INPUTS { a; } OUTPUTS { b; } GUARANTEES { G b; } }\n";
  char hash[65];
  assert(tlsf_pipeline_source_sha256(source.data(), source.size(), hash));
  assert(std::strlen(hash) == 64);
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes_v2(
      reinterpret_cast<const uint8_t *>(source.data()), source.size(), nullptr);
  assert(pipeline);
  tlsf_pipeline_free(pipeline);
  TlsfGr1CheckResult result{};
  assert(tlsf_gr1_check(nullptr, nullptr, &result) ==
         TLSF_GR1_CHECK_BAD_ARGUMENT);
  tlsf_gr1_check_result_clear(&result);

  const std::string game_text =
      "aag 3 2 1 1 0 0 0 1 0\n"
      "2\n4\n6 6 1\n0\n1\n6\n"
      "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n";
  FILE *input =
      fmemopen(const_cast<char *>(game_text.data()), game_text.size(), "r");
  assert(input);
  Aig *game = aig_read_aag(input);
  std::fclose(input);
  assert(game);
  char reason[128];
  assert(tlsf_gr1_validate_game(game, reason, sizeof reason));
  OxiddSolveOptionsV2 solve_options = oxidd_solve_options_default_v2();
  solve_options.node_cap = solve_options.cache_cap = 1u << 16;
  char *certificate = nullptr;
  size_t certificate_size = 0;
  Gr1CertificateOptionsV2 export_options{};
  export_options.abi_version = TLSF_GR1_CERTIFICATE_OPTIONS_ABI_VERSION;
  export_options.struct_size = sizeof export_options;
  export_options.aag_bytes = &certificate;
  export_options.aag_size = &certificate_size;
  export_options.max_artifact_bytes = 1u << 20;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd_ex_with_certificate_v2(
      game, &unreal, &solve_options, &export_options);
  assert(strategy && !unreal && !export_options.failed);
  assert(certificate_size > 0);
  aig_free(strategy);
  std::free(certificate);
}
