// native_reduction.cpp plus TlsfPipelineOptions.source_sha256, which makes
// the pipeline capture frontend expansion provenance. With it, gr1_reduction's
// provenance JSON gives every monitor a source_origin (source conjunct and
// generator lane) and records source_parameters; without it, monitors fall
// back to "suffix-heuristic" provenance. Used by
// test/oracle/test_gr1_environment_provenance.py.
#include "tlsf/pipeline.h"
#include "tlsf/gr1_reduction.h"

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
    std::cerr << "usage: gr1_environment_reduce INPUT.tlsf exact|strict "
                 "OUTPUT-PREFIX [FRONTEND-JSON-OVERRIDE]\n";
    return 2;
  }
  std::ifstream in(argv[1], std::ios::binary);
  if (!in) {
    std::cerr << "cannot open input\n";
    return 2;
  }
  std::string bytes((std::istreambuf_iterator<char>(in)),
                    std::istreambuf_iterator<char>());
  char source_sha256[65];
  if (!tlsf_pipeline_source_sha256(bytes.data(), bytes.size(), source_sha256)) {
    std::cerr << "cannot hash source\n";
    return 2;
  }
  TlsfPipelineError pipeline_error{};
  TlsfPipelineOptions pipeline_options{};
  pipeline_options.certify = true;
  pipeline_options.template_mask = TPL_ALL;
  pipeline_options.source_sha256 = source_sha256;
  pipeline_options.require_unambiguous_origin = true;
  pipeline_options.error = &pipeline_error;
  TlsfPipeline *pipeline =
      tlsf_pipeline_load_bytes(reinterpret_cast<const uint8_t *>(bytes.data()),
                               bytes.size(), &pipeline_options);
  if (!pipeline) {
    std::cerr << "pipeline: " << pipeline_error.stage << ": "
              << pipeline_error.message << '\n';
    return 2;
  }
  // Test seam: replace only the frontend inventory. The reducer still builds
  // its monitors from the original TLSF snapshot.
  std::string frontend_override;
  char *original_frontend = pipeline->frontend_provenance_json;
  if (argc == 5) {
    std::ifstream override_file(argv[4], std::ios::binary);
    if (!override_file) {
      tlsf_pipeline_free(pipeline);
      std::cerr << "cannot open frontend override\n";
      return 2;
    }
    frontend_override.assign(std::istreambuf_iterator<char>(override_file),
                             std::istreambuf_iterator<char>());
    pipeline->frontend_provenance_json = frontend_override.data();
  }
  TlsfGr1ReductionOptions options{};
  options.semantics =
      std::string(argv[2]) == "exact" ? TLSF_GR1_EXACT : TLSF_GR1_STRICT;
  options.max_artifact_bytes = 16 * 1024 * 1024;
  options.max_monitor_states = 10000;
  TlsfGr1Reduction result{};
  TlsfGr1ReductionError error{};
  auto status = tlsf_gr1_reduce(pipeline, &options, &result, &error);
  pipeline->frontend_provenance_json = original_frontend;
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
