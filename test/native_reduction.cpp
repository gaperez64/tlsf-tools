#include "tlsf/native.h"

#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>

static bool write(const std::string &path, const char *data, size_t size) {
  std::ofstream out(path, std::ios::binary);
  out.write(data, static_cast<std::streamsize>(size));
  return bool(out);
}

int main(int argc, char **argv) {
  if ((argc != 4 && argc != 5) ||
      (std::string(argv[2]) != "exact" && std::string(argv[2]) != "strict")) {
    std::cerr
        << "usage: native_reduction INPUT.tlsf exact|strict OUTPUT-PREFIX "
           "[MAX-MONITOR-STATES]\n";
    return 2;
  }
  std::ifstream in(argv[1], std::ios::binary);
  if (!in) {
    std::cerr << "cannot open input\n";
    return 2;
  }
  std::string bytes((std::istreambuf_iterator<char>(in)),
                    std::istreambuf_iterator<char>());
  TlsfPipelineError pipeline_error{};
  TlsfPipelineOptionsV2 pipeline_options{};
  pipeline_options.abi_version = TLSF_PIPELINE_OPTIONS_ABI_VERSION;
  pipeline_options.struct_size = sizeof pipeline_options;
  pipeline_options.certify = true;
  pipeline_options.template_mask = TPL_ALL;
  pipeline_options.error = &pipeline_error;
  TlsfPipeline *pipeline = tlsf_pipeline_load_bytes_v2(
      reinterpret_cast<const uint8_t *>(bytes.data()), bytes.size(),
      &pipeline_options);
  if (!pipeline) {
    std::cerr << "pipeline: " << pipeline_error.stage << ": "
              << pipeline_error.message << '\n';
    return 2;
  }
  TlsfGr1ReductionOptions options{};
  options.abi_version = TLSF_GR1_REDUCTION_ABI_VERSION;
  options.struct_size = sizeof options;
  options.semantics =
      std::string(argv[2]) == "exact" ? TLSF_GR1_EXACT : TLSF_GR1_STRICT;
  options.max_artifact_bytes = 16 * 1024 * 1024;
  options.max_monitor_states = argc == 5 ? std::stoul(argv[4]) : 10000;
  TlsfGr1Reduction result{};
  TlsfGr1ReductionError error{};
  auto status = tlsf_gr1_reduce_v1(pipeline, &options, &result, &error);
  tlsf_pipeline_free(pipeline);
  if (status != TLSF_GR1_REDUCE_OK) {
    std::cerr << "reduce status " << status << ": " << error.stage << ": "
              << error.message << '\n';
    return status == TLSF_GR1_REDUCE_UNSUPPORTED ? 3 : 2;
  }
  std::string prefix = argv[3];
  bool ok =
      write(prefix + ".aag", result.aag, result.aag_size) &&
      write(prefix + ".json", result.provenance_json, result.provenance_size) &&
      write(prefix + ".symbols", result.symbol_map, result.symbol_map_size) &&
      write(prefix + ".metadata.json", result.metadata_json,
            result.metadata_size);
  tlsf_gr1_reduction_clear(&result);
  if (!ok)
    return 2;
  return 0;
}
