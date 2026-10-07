#include <tlsf/gr1_reduction.h>
#include <cstdio>
#include <fstream>
#include <iterator>
#include <memory>
#include <string>

static bool write(const std::string &path, const char *data, size_t size) {
  if (!data)
    return true;
  std::ofstream out(path, std::ios::binary);
  out.write(data, std::streamsize(size));
  return bool(out);
}
int main(int argc, char **argv) {
  if (argc < 3 || argc > 4)
    return 2;
  std::ifstream in(argv[1]);
  std::string bytes((std::istreambuf_iterator<char>(in)), {});
  if (!in || bytes.empty())
    return 2;
  char hash[65];
  if (!tlsf_pipeline_source_sha256(bytes.data(), bytes.size(), hash))
    return 2;
  TlsfPipelineOptions load{};
  load.certify = true;
  load.template_mask = TPL_ALL;
  load.source_sha256 = hash;
  load.require_unambiguous_origin = true;
  std::unique_ptr<TlsfPipeline, decltype(&tlsf_pipeline_free)> pipeline(
      tlsf_pipeline_load_bytes(reinterpret_cast<const uint8_t *>(bytes.data()),
                               bytes.size(), &load),
      tlsf_pipeline_free);
  if (!pipeline)
    return 2;
  TlsfGr1ReductionOptions options{};
  const std::string mode = argc == 4 ? argv[3] : "exact";
  options.semantics = mode == "strict" ? TLSF_GR1_STRICT : TLSF_GR1_EXACT;
  options.max_artifact_bytes = 1024 * 1024;
  options.max_monitor_states = 128;
  if (mode == "structure")
    options.budget.max_formula_nodes = 1;
  if (mode == "monitor")
    options.max_monitor_states = 1;
  if (mode == "deadline")
    options.deadline_mono_ns = 1;
  if (mode == "cancel")
    options.cancelled = [](void *) { return 1; };
  if (mode == "snapshot")
    const_cast<uint8_t *>(pipeline->source_bytes)[0] ^= 1;
  TlsfGr1DualRecognitionV1 result{};
  TlsfGr1ReductionError error{};
  TlsfGr1ReductionStatus cause{};
  int constructed = 0;
  const TlsfGr1DualObserverV1 observer{
      [](void *ctx, const char *, size_t) { ++*static_cast<int *>(ctx); },
      &constructed};
  auto status = tlsf_gr1_recognize_dual_v1(pipeline.get(), &options, &observer,
                                           &result, &error, &cause);
  printf("{\"status\":%d,\"cause\":%d,\"stage\":\"%s\",\"constructed\":%d}\n",
         int(status), int(cause), error.stage, constructed);
  const std::string prefix(argv[2]);
  bool ok =
      write(prefix + ".construction.json", result.construction_json,
            result.construction_size) &&
      write(prefix + ".aag", result.reduction.aag, result.reduction.aag_size) &&
      write(prefix + ".provenance.json", result.reduction.provenance_json,
            result.reduction.provenance_size) &&
      write(prefix + ".metadata.json", result.reduction.metadata_json,
            result.reduction.metadata_size);
  // Reuse of an owned result must fail without changing it.
  if (result.construction_json || result.reduction.game) {
    auto *saved = result.construction_json;
    auto *game = result.reduction.game;
    auto again = tlsf_gr1_recognize_dual_v1(pipeline.get(), &options, nullptr,
                                            &result, &error, &cause);
    ok &= again == TLSF_GR1_REDUCE_INVALID &&
          saved == result.construction_json && game == result.reduction.game;
  }
  tlsf_gr1_dual_recognition_clear_v1(&result);
  tlsf_gr1_dual_recognition_clear_v1(&result);
  return ok ? 0 : 2;
}
