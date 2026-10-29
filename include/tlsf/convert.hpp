#ifndef TLSF_CONVERT_HPP
#define TLSF_CONVERT_HPP

#include "tlsf/convert.h"
#include "tlsf/decompose.hpp"
#include <memory>
#include <utility>

namespace tlsf {
struct Conversion {
  std::string preprocessed_ltl;
  std::vector<std::string> inputs;
  std::vector<std::string> outputs;
  std::vector<IndexedFamily> indexed_families;
  bool has_indexed_conjunction = false;
  std::string semantics;
  std::string original_target;
  std::string effective_target;
  int gr_level = -1;
  std::shared_ptr<TlsfAst> ast;
};

inline Conversion convert(const std::string &spec,
                          const char *effective_target) {
  std::unique_ptr<TlsfConversionResult, decltype(&tlsf_conversion_result_free)>
      raw(tlsf_convert(spec.c_str(), effective_target),
          tlsf_conversion_result_free);
  if (!raw)
    throw std::runtime_error("tlsf conversion failed");
  Conversion out;
  out.preprocessed_ltl = raw->preprocessed_ltl;
  out.inputs = detail::copy_strings(raw->inputs, raw->n_inputs);
  out.outputs = detail::copy_strings(raw->outputs, raw->n_outputs);
  out.indexed_families.reserve(raw->n_indexed_families);
  for (uint32_t i = 0; i < raw->n_indexed_families; ++i) {
    const auto &f = raw->indexed_families[i];
    out.indexed_families.push_back(
        {f.origin_name, detail::copy_strings(f.members, f.n_members), f.lo,
         f.hi, f.is_output, f.is_enum});
  }
  out.has_indexed_conjunction = raw->has_indexed_conjunction;
  out.semantics = raw->semantics;
  out.original_target = raw->original_target;
  out.effective_target = raw->effective_target;
  out.gr_level = raw->gr_level;
  out.ast =
      std::shared_ptr<TlsfAst>(std::exchange(raw->ast, nullptr), tlsf_ast_free);
  return out;
}
} // namespace tlsf
#endif
