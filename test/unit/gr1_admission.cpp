// Corpus measurement only: compare proved and research component admission.
extern "C" {
#include "classify.h"
#include "dpa_buchi.h"
#include "print_ltlxba.h"
#include "tlsf/pipeline.h"
}
#include "gr1_formula.hh"
#include <chrono>
#include <fstream>
#include <iostream>
#include <iterator>
using gr1_formula::Formula;
using gr1_formula::Op;
static void split(Formula f, std::vector<Formula> &out) {
  if (f.kind() == Op::And) {
    for (auto child : f)
      split(child, out);
  } else if (f.kind() == Op::G && f[0].kind() == Op::And) {
    for (auto child : f[0])
      split(Formula::G(child), out);
  } else if (!f.is_tt())
    out.push_back(f);
}
int main(int argc, char **argv) {
  std::cout << "source\tmode\tstatus\treason\tstates\n";
  for (int i = 1; i < argc; ++i) {
    std::ifstream in(argv[i]);
    std::string text(std::istreambuf_iterator<char>{in}, {});
    TlsfPipelineOptions options{};
    options.certify = true;
    options.template_mask = TPL_ALL;
    auto *pipeline = tlsf_pipeline_load_bytes(
        reinterpret_cast<const uint8_t *>(text.data()), text.size(), &options);
    if (!pipeline) {
      std::cout << argv[i] << "\tinvalid\t2\t0\t0\n";
      continue;
    }
    std::unique_ptr<TlsfPipeline, decltype(&tlsf_pipeline_free)> owned(
        pipeline, tlsf_pipeline_free);
    auto *spec = pipeline->spec;
    if (spec->info.semantics != SEM_MEALY ||
        spec->info.target != TARGET_MEALY) {
      std::cout << argv[i] << "\tsemantics\t1\t1\t0\n";
      continue;
    }
    auto *classes = classify_spec(spec);
    auto f =
        gr1_formula::from_node(build_spec_formula(spec, classes, PRINT_ALL));
    std::vector<Formula> conjuncts;
    if (f.kind() == Op::Implies) {
      split(f[0], conjuncts);
      split(f[1], conjuncts);
    } else
      split(f, conjuncts);
    std::vector<const char *> names;
    for (uint32_t j = 0; j < spec->input_count; ++j)
      names.push_back(spec->inputs[j].name);
    for (uint32_t j = 0; j < spec->output_count; ++j)
      names.push_back(spec->outputs[j].name);
    for (bool research : {false, true}) {
      size_t states = 0;
      TlsfDpaStatus status{};
      TlsfDpaBudget budget{};
      budget.allow_unproved = research;
      budget.deadline_mono_ns =
          uint64_t(std::chrono::duration_cast<std::chrono::nanoseconds>(
                       std::chrono::steady_clock::now().time_since_epoch())
                       .count()) +
          20000000000ull;
      for (auto item : conjuncts) {
        if (states >= 10000) {
          status = {TLSF_DPA_DECLINED, TLSF_DPA_STATE_LIMIT};
          break;
        }
        budget.max_states = 10000 - states;
        TlsfDpa *ctx = nullptr;
        char klass = 0;
        status = dpa_buchi_create(
            reinterpret_cast<const TlsfAstNode *>(item.node()), names.data(),
            uint32_t(names.size()), &budget, &ctx, &klass);
        if (status.code == TLSF_DPA_OK)
          status = tlsf_dpa_expand(ctx);
        states += tlsf_dpa_state_count(ctx);
        tlsf_dpa_free(ctx);
        if (status.code != TLSF_DPA_OK)
          break;
      }
      std::cout << argv[i] << '\t' << (research ? "research" : "default")
                << '\t' << status.code << '\t' << status.reason << '\t'
                << states << std::endl;
    }
  }
}
