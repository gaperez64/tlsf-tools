// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L

#include "decompose_internal.h"

#include "classify.h"
#include "conversion_internal.h"
#include "gr.h"
#include "tlsf/pipeline.h"
#include "print_ltlxba.h"
#include "residual.h"

#include "precheck_unreal.h"

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

static LtlFormat decompose_format(const TlsfDecomposeOptions *opts) {
  if (opts && opts->format == TLSF_DECOMPOSE_FORMAT_LTL)
    return LTL_FMT_LTL;
  return LTL_FMT_LTLXBA;
}

static bool fill_preprocessed(TlsfDecomposeResult *r, TlsfSpec *spec,
                              LtlFormat fmt, bool lower) {
  ClassifiedSpec *cs = classify_spec(spec);
  if (!cs)
    return false;
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  r->preprocessed_ltl = conversion_render_ltl(
      root, fmt, semantics_is_finite(spec->info.semantics), lower);
  return r->preprocessed_ltl != nullptr;
}

static void fill_verdict(TlsfDecomposeResult *r, ConstraintCover *cov) {
  r->verdict = TLSF_DECOMPOSE_VERDICT_UNKNOWN;
  r->verdict_trust = TLSF_DECOMPOSE_TRUST_NONE;
  if (precheck_trivially_unreal(cov)) {
    r->verdict = TLSF_DECOMPOSE_VERDICT_UNREALIZABLE;
    r->verdict_trust = TLSF_DECOMPOSE_TRUST_OVER;
  } else if (precheck_trivially_real(cov)) {
    r->verdict = TLSF_DECOMPOSE_VERDICT_REALIZABLE;
    r->verdict_trust = TLSF_DECOMPOSE_TRUST_UNDER;
  }
}

TlsfDecomposeResult *
tlsf_decompose_result_from_plan(TlsfSpec *spec, ConstraintCover *cov,
                                const Csnf *csnf, const CsnfComposition *comp,
                                const ResidualPlan *rplan,
                                const TlsfDecomposeOptions *opts) {
  (void)csnf;
  (void)comp;
  if (!spec || !cov || !rplan)
    return nullptr;

  LtlFormat fmt = decompose_format(opts);
  bool lower = opts && opts->lowercase;
  bool finite = semantics_is_finite(spec->info.semantics);
  if (lower && !spec_validate_lowercase_signals(spec, "tlsf-decompose"))
    return nullptr;
  if (fmt == LTL_FMT_LTLXBA &&
      !spec_validate_ltlxba_atoms(spec, "tlsf-decompose"))
    return nullptr;

  TlsfDecomposeResult *r = calloc(1, sizeof *r);
  if (!r)
    return nullptr;
  r->residual_trust = TLSF_DECOMPOSE_TRUST_EXACT;
  r->semantics =
      conversion_dup_cstr(conversion_semantics_name(spec->info.semantics));
  r->target = conversion_dup_cstr(conversion_target_name(spec->info.target));
  r->gr_level = gr_level(spec);
  if (!r->semantics || !r->target)
    goto fail;
  if (opts && opts->precheck)
    fill_verdict(r, cov);
  if (!fill_preprocessed(r, spec, fmt, lower))
    goto fail;
  if (!conversion_collect_signals(&cov->aps, nullptr, AP_FLAG_INPUT, lower,
                                  &r->inputs, &r->n_inputs) ||
      !conversion_collect_signals(&cov->aps, nullptr, AP_FLAG_OUTPUT, lower,
                                  &r->outputs, &r->n_outputs) ||
      !conversion_collect_families(&r->indexed_families, &r->n_indexed_families,
                                   spec, lower))
    goto fail;

  r->n_clusters = rplan->nclusters;
  if (r->n_clusters) {
    r->clusters = calloc(r->n_clusters, sizeof *r->clusters);
    if (!r->clusters)
      goto fail;
  }

  bool *seen = calloc(cov->aps.count ? cov->aps.count : 1, sizeof *seen);
  if (!seen)
    goto fail;
  for (uint32_t k = 0; k < rplan->nclusters; k++) {
    bool output_free = rplan->keys[k] == cov->aps.count;
    Node *root = residual_plan_build_cluster(spec, cov, rplan, rplan->keys[k],
                                             /*all=*/false,
                                             /*prune=*/!output_free, seen);
    if (!root) {
      free(seen);
      goto fail;
    }
    TlsfDecomposeCluster *c = &r->clusters[k];
    c->ltl = conversion_render_ltl(root, fmt, finite, lower);
    if (!c->ltl ||
        !conversion_collect_signals(&cov->aps, seen, AP_FLAG_INPUT, lower,
                                    &c->inputs, &c->n_inputs) ||
        !conversion_collect_signals(&cov->aps, seen, AP_FLAG_OUTPUT, lower,
                                    &c->outputs, &c->n_outputs)) {
      free(seen);
      goto fail;
    }
  }
  free(seen);
  return r;

fail:
  tlsf_decompose_result_free(r);
  return nullptr;
}

TlsfDecomposeResult *tlsf_decompose_file(FILE *fp,
                                         const TlsfDecomposeOptions *opts) {
  if (!fp)
    return nullptr;
  TlsfPipelineOptions popts = {
      .split = opts && opts->split,
      .certify = true,
      .template_mask = TPL_ALL,
      .overwrite_semantics = opts ? opts->overwrite_semantics : nullptr,
      .overwrite_target = opts ? opts->overwrite_target : nullptr,
      .tool_name = "tlsf-decompose",
  };
  TlsfPipeline *p = tlsf_pipeline_load(fp, &popts);
  if (!p)
    return nullptr;
  ResidualPlanOptions ropts = {.skip_local_aiger = false,
                               .simplify_weak = true};
  ResidualPlan *rplan =
      residual_plan_build(p->spec, p->cover, p->csnf, p->composition, ropts);
  TlsfDecomposeResult *r =
      rplan ? tlsf_decompose_result_from_plan(p->spec, p->cover, p->csnf,
                                              p->composition, rplan, opts)
            : nullptr;
  residual_plan_free(rplan);
  tlsf_pipeline_free(p);
  return r;
}

TlsfDecomposeResult *tlsf_decompose_string(const char *spec_text,
                                           const TlsfDecomposeOptions *opts) {
  if (!spec_text)
    return nullptr;
  FILE *fp = fmemopen((void *)spec_text, strlen(spec_text), "r");
  if (!fp)
    return nullptr;
  TlsfDecomposeResult *r = tlsf_decompose_file(fp, opts);
  fclose(fp);
  return r;
}

void tlsf_decompose_result_free(TlsfDecomposeResult *r) {
  if (!r)
    return;
  for (uint32_t i = 0; i < r->n_clusters; i++) {
    free(r->clusters[i].ltl);
    conversion_free_strings(r->clusters[i].inputs, r->clusters[i].n_inputs);
    conversion_free_strings(r->clusters[i].outputs, r->clusters[i].n_outputs);
  }
  free(r->clusters);
  free(r->preprocessed_ltl);
  conversion_free_strings(r->inputs, r->n_inputs);
  conversion_free_strings(r->outputs, r->n_outputs);
  for (uint32_t i = 0; i < r->n_indexed_families; i++) {
    free(r->indexed_families[i].origin_name);
    conversion_free_strings(r->indexed_families[i].members,
                            r->indexed_families[i].n_members);
  }
  free(r->indexed_families);
  free(r->semantics);
  free(r->target);
  free(r);
}
