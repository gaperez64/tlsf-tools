#ifndef TLSF_DECOMPOSE_HPP
#define TLSF_DECOMPOSE_HPP

#include "tlsf/decompose.h"

#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace tlsf {

enum class Format {
  Ltlxba = TLSF_DECOMPOSE_FORMAT_LTLXBA,
  Ltl = TLSF_DECOMPOSE_FORMAT_LTL,
};

enum class Verdict {
  Unknown = TLSF_DECOMPOSE_VERDICT_UNKNOWN,
  Realizable = TLSF_DECOMPOSE_VERDICT_REALIZABLE,
  Unrealizable = TLSF_DECOMPOSE_VERDICT_UNREALIZABLE,
};

enum class Trust {
  None = TLSF_DECOMPOSE_TRUST_NONE,
  Exact = TLSF_DECOMPOSE_TRUST_EXACT,
  Under = TLSF_DECOMPOSE_TRUST_UNDER,
  Over = TLSF_DECOMPOSE_TRUST_OVER,
};

struct Options {
  bool split = false;
  bool lowercase = false;
  Format format = Format::Ltlxba;
  std::string overwrite_semantics;
  std::string overwrite_target;
};

struct Cluster {
  std::string ltl;
  std::vector<std::string> inputs;
  std::vector<std::string> outputs;
};

struct Result {
  std::vector<Cluster> clusters;
  std::string preprocessed_ltl;
  std::vector<std::string> inputs;
  std::vector<std::string> outputs;
  std::string semantics;
  std::string target;
  int gr_level = -1;
  Verdict verdict = Verdict::Unknown;
  Trust verdict_trust = Trust::None;
  Trust residual_trust = Trust::None;
};

namespace detail {
struct ResultDeleter {
  void operator()(TlsfDecomposeResult *r) const {
    tlsf_decompose_result_free(r);
  }
};

inline std::vector<std::string> copy_strings(char **items, uint32_t count) {
  std::vector<std::string> out;
  out.reserve(count);
  for (uint32_t i = 0; i < count; ++i)
    out.emplace_back(items[i] ? items[i] : "");
  return out;
}
} // namespace detail

inline Result decompose(const std::string &spec, const Options &options = {}) {
  TlsfDecomposeOptions c_options = {};
  c_options.split = options.split;
  c_options.lowercase = options.lowercase;
  c_options.format = static_cast<TlsfDecomposeFormat>(options.format);
  c_options.overwrite_semantics =
      options.overwrite_semantics.empty() ? nullptr
                                          : options.overwrite_semantics.c_str();
  c_options.overwrite_target =
      options.overwrite_target.empty() ? nullptr : options.overwrite_target.c_str();

  std::unique_ptr<TlsfDecomposeResult, detail::ResultDeleter> raw(
      tlsf_decompose_string(spec.c_str(), &c_options));
  if (!raw)
    throw std::runtime_error("tlsf decomposition failed");

  Result out;
  out.preprocessed_ltl = raw->preprocessed_ltl ? raw->preprocessed_ltl : "";
  out.inputs = detail::copy_strings(raw->inputs, raw->n_inputs);
  out.outputs = detail::copy_strings(raw->outputs, raw->n_outputs);
  out.semantics = raw->semantics ? raw->semantics : "";
  out.target = raw->target ? raw->target : "";
  out.gr_level = raw->gr_level;
  out.verdict = static_cast<Verdict>(raw->verdict);
  out.verdict_trust = static_cast<Trust>(raw->verdict_trust);
  out.residual_trust = static_cast<Trust>(raw->residual_trust);

  out.clusters.reserve(raw->n_clusters);
  for (uint32_t i = 0; i < raw->n_clusters; ++i) {
    const TlsfDecomposeCluster &c = raw->clusters[i];
    Cluster cluster;
    cluster.ltl = c.ltl ? c.ltl : "";
    cluster.inputs = detail::copy_strings(c.inputs, c.n_inputs);
    cluster.outputs = detail::copy_strings(c.outputs, c.n_outputs);
    out.clusters.push_back(std::move(cluster));
  }
  return out;
}

} // namespace tlsf

#endif // TLSF_DECOMPOSE_HPP
