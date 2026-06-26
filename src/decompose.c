// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L

#include "decompose_internal.h"

#include "tlsf/classify.h"
#include "tlsf/gr.h"
#include "tlsf/pipeline.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/residual.h"

#ifdef HAVE_OXIDD
#include "tlsf/precheck_unreal.h"
#endif

#include <ctype.h>
#include <stdlib.h>
#include <string.h>

static LtlFormat decompose_format(const TlsfDecomposeOptions *opts) {
  if (opts && opts->format == TLSF_DECOMPOSE_FORMAT_LTL)
    return LTL_FMT_LTL;
  return LTL_FMT_LTLXBA;
}

static const char *semantics_name(Semantics s) {
  switch (s) {
  case SEM_MEALY:
    return "Mealy";
  case SEM_MOORE:
    return "Moore";
  case SEM_MEALY_STRICT:
    return "Strict,Mealy";
  case SEM_MOORE_STRICT:
    return "Strict,Moore";
  case SEM_MEALY_FINITE:
    return "Finite,Mealy";
  case SEM_MOORE_FINITE:
    return "Finite,Moore";
  }
  return "Mealy";
}

static const char *target_name(Target t) {
  return t == TARGET_MOORE ? "Moore" : "Mealy";
}

static char *dup_cstr(const char *s) {
  if (!s)
    s = "";
  size_t n = strlen(s);
  char *out = malloc(n + 1);
  if (!out)
    return nullptr;
  memcpy(out, s, n + 1);
  return out;
}

static char *dup_maybe_lower(const char *s, bool lower) {
  char *out = dup_cstr(s);
  if (!out || !lower)
    return out;
  for (char *p = out; *p; p++)
    *p = (char)tolower((unsigned char)*p);
  return out;
}

static void free_string_array(char **items, uint32_t count) {
  if (!items)
    return;
  for (uint32_t i = 0; i < count; i++)
    free(items[i]);
  free(items);
}

static bool push_signal(char ***items, uint32_t *count, const char *name,
                        bool lower) {
  char **grown = realloc(*items, (*count + 1) * sizeof **items);
  if (!grown)
    return false;
  *items = grown;
  (*items)[*count] = dup_maybe_lower(name, lower);
  if (!(*items)[*count])
    return false;
  (*count)++;
  return true;
}

static bool collect_signals(ConstraintCover *cov, const bool *seen,
                            uint8_t flag, bool lower, char ***items,
                            uint32_t *count) {
  *items = nullptr;
  *count = 0;
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (seen && !seen[a])
      continue;
    if (!residual_signal_matches(cov, a, flag))
      continue;
    if (!push_signal(items, count, ap_table_name(&cov->aps, a), lower)) {
      free_string_array(*items, *count);
      *items = nullptr;
      *count = 0;
      return false;
    }
  }
  return true;
}

static char *render_ltl(const Node *root, LtlFormat fmt, bool finite,
                        bool lower) {
  char *buf = nullptr;
  size_t len = 0;
  FILE *ms = open_memstream(&buf, &len);
  if (!ms)
    return nullptr;
  print_ltl(ms, root, fmt, /*full_parens=*/false, finite, lower);
  fclose(ms);
  if (len && buf[len - 1] == '\n')
    buf[len - 1] = '\0';
  return buf;
}

static bool fill_preprocessed(TlsfDecomposeResult *r, TlsfSpec *spec,
                              LtlFormat fmt, bool lower) {
  ClassifiedSpec *cs = classify_spec(spec);
  if (!cs)
    return false;
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  r->preprocessed_ltl =
      render_ltl(root, fmt, semantics_is_finite(spec->info.semantics), lower);
  return r->preprocessed_ltl != nullptr;
}

static void fill_verdict(TlsfDecomposeResult *r, ConstraintCover *cov) {
  r->verdict = TLSF_DECOMPOSE_VERDICT_UNKNOWN;
  r->verdict_trust = TLSF_DECOMPOSE_TRUST_NONE;
#ifdef HAVE_OXIDD
  if (precheck_trivially_unreal(cov)) {
    r->verdict = TLSF_DECOMPOSE_VERDICT_UNREALIZABLE;
    r->verdict_trust = TLSF_DECOMPOSE_TRUST_OVER;
  } else if (precheck_trivially_real(cov)) {
    r->verdict = TLSF_DECOMPOSE_VERDICT_REALIZABLE;
    r->verdict_trust = TLSF_DECOMPOSE_TRUST_UNDER;
  }
#endif
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

  TlsfDecomposeResult *r = calloc(1, sizeof *r);
  if (!r)
    return nullptr;

  LtlFormat fmt = decompose_format(opts);
  bool lower = opts && opts->lowercase;
  bool finite = semantics_is_finite(spec->info.semantics);
  r->residual_trust = TLSF_DECOMPOSE_TRUST_EXACT;
  r->semantics = dup_cstr(semantics_name(spec->info.semantics));
  r->target = dup_cstr(target_name(spec->info.target));
  r->gr_level = gr_level(spec);
  if (!r->semantics || !r->target)
    goto fail;
  fill_verdict(r, cov);
  if (!fill_preprocessed(r, spec, fmt, lower))
    goto fail;
  if (!collect_signals(cov, nullptr, AP_FLAG_INPUT, lower, &r->inputs,
                       &r->n_inputs) ||
      !collect_signals(cov, nullptr, AP_FLAG_OUTPUT, lower, &r->outputs,
                       &r->n_outputs))
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
    c->ltl = render_ltl(root, fmt, finite, lower);
    if (!c->ltl ||
        !collect_signals(cov, seen, AP_FLAG_INPUT, lower, &c->inputs,
                         &c->n_inputs) ||
        !collect_signals(cov, seen, AP_FLAG_OUTPUT, lower, &c->outputs,
                         &c->n_outputs)) {
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
    free_string_array(r->clusters[i].inputs, r->clusters[i].n_inputs);
    free_string_array(r->clusters[i].outputs, r->clusters[i].n_outputs);
  }
  free(r->clusters);
  free(r->preprocessed_ltl);
  free_string_array(r->inputs, r->n_inputs);
  free_string_array(r->outputs, r->n_outputs);
  free(r->semantics);
  free(r->target);
  free(r);
}
