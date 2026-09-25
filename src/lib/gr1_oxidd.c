#define _GNU_SOURCE
// gr1_oxidd.c — in-process GR(1) game solver on OxiDD BDDs.
//
// Implements the Piterman-Pnueli-Sa'ar (PPS) tri-nested fixpoint:
//
//   W* = νZ. ⋀_j [ μY. ⋃_i νX.
//                         cpre( (Z ∩ goal_j) ∪ Y ∪ (X ∩ ¬fair_i) ) ]
//
// The game is in the standard AbsSynthe AIGER format (see safety_oxidd.c for
// conventions); the only difference is that the Aig also carries justice[]
// (system Büchi goals) and fair[] (environment fairness assumptions) records.
//
// Strategy: the output AIG adds m one-hot goal-counter latches curr[0..m-1]
// (reset curr[0]=1, rest 0).  At each step the system picks controllables to
// make progress toward the current goal, and advances the counter when the
// current game state satisfies that goal and the state is in the winning
// region.

#include "tlsf/gr1_oxidd.h"

#include "oxidd_common.h"
#include "yyjson_builder.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#ifdef __GLIBC__
typedef struct {
  char **output;
  size_t *output_size;
  char *data;
  size_t size, capacity, limit;
  bool failed;
  const OxiddSolveOptions *options;
} CappedExport;

static ssize_t capped_export_write(void *opaque, const char *bytes,
                                   size_t count) {
  CappedExport *export = opaque;
  if (export->failed || count > export->limit - export->size ||
      count == SIZE_MAX - export->size) {
    export->failed = true;
    oxidd_record_failure(export->options, OXIDD_FAILURE_ARTIFACT_LIMIT,
                         "export", "artifact_cap", 0, 0);
    errno = EFBIG;
    return 0;
  }
  size_t needed = export->size + count + 1;
  if (needed > export->capacity) {
    size_t maximum = export->limit == SIZE_MAX ? SIZE_MAX : export->limit + 1;
    size_t capacity = export->capacity ? export->capacity : 256;
    if (capacity > maximum)
      capacity = maximum;
    while (capacity < needed)
      capacity = capacity > maximum / 2 ? maximum : capacity * 2;
    char *data = realloc(export->data, capacity);
    if (!data) {
      export->failed = true;
      errno = ENOMEM;
      return 0;
    }
    export->data = data;
    export->capacity = capacity;
  }
  memcpy(export->data + export->size, bytes, count);
  export->size += count;
  return (ssize_t)count;
}

static int capped_export_close(void *opaque) {
  CappedExport *export = opaque;
  if (export->failed) {
    free(export->data);
    free(export);
    return -1;
  }
  if (!export->data) {
    export->data = malloc(1);
    if (!export->data) {
      free(export);
      return -1;
    }
  }
  export->data[export->size] = '\0';
  *export->output = export->data;
  *export->output_size = export->size;
  free(export);
  return 0;
}
#endif

static FILE *open_export_memstream(const OxiddRun *run,
                                   const Gr1CertificateOptions *options,
                                   char **output, size_t *size) {
  size_t limit = options->max_artifact_bytes ? options->max_artifact_bytes
                                             : run->options->max_artifact_bytes;
  *output = nullptr;
  *size = 0;
#ifdef __GLIBC__
  if (limit) {
    CappedExport *export = oxidd_host_calloc(1, sizeof *export);
    if (!export)
      return nullptr;
    export->output = output;
    export->output_size = size;
    export->limit = limit;
    export->options = run->options;
    cookie_io_functions_t io = {.write = capped_export_write,
                                .close = capped_export_close};
    FILE *stream = fopencookie(export, "w", io);
    if (!stream) {
      free(export);
      return nullptr;
    }
    setvbuf(stream, nullptr, _IONBF, 0);
    return stream;
  }
#endif
#ifndef __GLIBC__
  (void)limit;
#endif
  return open_memstream(output, size);
}

// ---------------------------------------------------------------------------
// Dynamic array of BDD references (for μ-fixpoint Y-levels)
// ---------------------------------------------------------------------------

typedef struct {
  Bdd *arr;
  uint32_t n, cap;
} BddVec;

typedef struct {
  Bdd z;
  Bdd *y;
  BddVec *x;
} DualLevel;

typedef struct {
  DualLevel *arr;
  uint32_t n, cap;
} DualVec;

static bool bddvec_push_ref(OxiddRun *run, BddVec *v, Bdd b) {
  if (v->n == v->cap) {
    uint32_t nc = v->cap ? v->cap * 2 : 4;
    Bdd *narr = oxidd_host_realloc(v->arr, nc * sizeof *narr);
    if (!narr) {
      oxidd_record_failure(run->options, OXIDD_FAILURE_HOST, run->phase,
                           "realloc", run->operations, run->index);
      return false;
    }
    v->arr = narr;
    v->cap = nc;
  }
  v->arr[v->n++] = oxidd_bdd_ref(b);
  return true;
}

// Build all GR(1) roots in one pass so oxidd_build_roots can retain main's
// operation accounting, allocation-failure recording, and early map release.
// Unlike the shared safety-oriented helper, this accepts every literal in an
// AIGER justice record as a separate generalized-Buchi goal.
static bool build_gr1_roots(OxiddRun *run, const Aig *game, Bdd *map,
                            uint32_t maxvar, uint32_t m_goals, Bdd *bad,
                            Bdd *next, Bdd *goals, Bdd *fair) {
  uint32_t nl = aig_num_latches(game);
  uint32_t nj = aig_num_justice(game);
  uint32_t nf = aig_num_fairness(game);
  bool typed =
      run->options->safety_objective == OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR;
  uint32_t nb = typed ? aig_num_bad(game) : 1;
  size_t count = (size_t)nb + nl + m_goals + nf;
  uint32_t *lits = calloc(count, sizeof *lits);
  Bdd *roots = calloc(count, sizeof *roots);
  if (!lits || !roots) {
    oxidd_record_failure(run->options, OXIDD_FAILURE_HOST, "construction",
                         "calloc", run->operations, run->index);
    free(lits);
    free(roots);
    return false;
  }

  size_t k = 0;
  for (uint32_t i = 0; i < nb; i++) {
    if (typed) {
      aig_bad_at(game, i, &lits[k++]);
    } else if (run->options->safety_output_index < aig_num_outputs(game)) {
      aig_output_at(game, run->options->safety_output_index, &lits[k++]);
    } else {
      free(lits);
      free(roots);
      return false;
    }
  }
  for (uint32_t i = 0; i < nl; i++)
    aig_latch_at(game, i, nullptr, &lits[k++], nullptr);
  for (uint32_t j = 0; j < nj; j++) {
    const uint32_t *record;
    uint32_t n;
    aig_justice_at(game, j, &record, &n);
    if (n == 0) {
      lits[k++] = AIG_TRUE;
    } else {
      for (uint32_t i = 0; i < n; i++)
        lits[k++] = record[i];
    }
  }
  for (uint32_t i = 0; i < nf; i++)
    lits[k++] = aig_fairness_at(game, i);

  bool ok = k == count &&
            oxidd_build_roots(run, game, map, maxvar, lits, roots, count);
  if (ok) {
    *bad = oxidd_bdd_false(run->manager);
    for (uint32_t i = 0; i < nb; i++) {
      Bdd combined = oxidd_run_or(run, *bad, roots[i]);
      oxidd_bdd_unref(*bad);
      *bad = combined;
    }
    ok = !bdd_invalid(*bad);
    k = nb;
  }
  if (ok) {
    for (uint32_t i = 0; i < nl; i++, k++) {
      next[i] = roots[k];
      roots[k] = (Bdd){0};
    }
    for (uint32_t i = 0; i < m_goals; i++, k++) {
      goals[i] = roots[k];
      roots[k] = (Bdd){0};
    }
    for (uint32_t i = 0; i < nf; i++, k++) {
      fair[i] = roots[k];
      roots[k] = (Bdd){0};
    }
  }
  for (size_t i = 0; i < count; i++)
    oxidd_bdd_unref(roots[i]);
  free(roots);
  free(lits);
  return ok;
}

static void bddvec_free_all(BddVec *v) {
  for (uint32_t i = 0; i < v->n; i++)
    oxidd_bdd_unref(v->arr[i]);
  free(v->arr);
  *v = (BddVec){0};
}

static void dual_level_free(DualLevel *level, uint32_t goals,
                            uint32_t fairness) {
  oxidd_bdd_unref(level->z);
  if (level->y)
    for (uint32_t j = 0; j < goals; j++)
      oxidd_bdd_unref(level->y[j]);
  if (level->x)
    for (uint32_t j = 0; j < goals; j++)
      for (uint32_t i = 0; i < fairness; i++)
        bddvec_free_all(&level->x[j * fairness + i]);
  free(level->y);
  free(level->x);
  *level = (DualLevel){0};
}

static void dualvec_free_all(DualVec *levels, uint32_t goals,
                             uint32_t fairness) {
  for (uint32_t k = 0; k < levels->n; k++)
    dual_level_free(&levels->arr[k], goals, fairness);
  free(levels->arr);
  *levels = (DualVec){0};
}

static bool dualvec_push_take(OxiddRun *run, DualVec *levels,
                              DualLevel *level) {
  if (levels->n == levels->cap) {
    uint32_t cap = levels->cap ? levels->cap * 2 : 4;
    DualLevel *next =
        oxidd_host_realloc(levels->arr, cap * sizeof *levels->arr);
    if (!next) {
      oxidd_record_failure(run->options, OXIDD_FAILURE_HOST, run->phase,
                           "dual_level_realloc", run->operations, run->index);
      return false;
    }
    levels->arr = next;
    levels->cap = cap;
  }
  levels->arr[levels->n++] = *level;
  *level = (DualLevel){0};
  return true;
}

// ---------------------------------------------------------------------------
// Certificate export
// ---------------------------------------------------------------------------

static void certificate_error(Gr1CertificateOptions *options,
                              const char *message, const char *path) {
  options->failed = true;
  if (path)
    snprintf(options->error, sizeof options->error, "%s '%s': %s", message,
             path, strerror(errno));
  else
    snprintf(options->error, sizeof options->error, "%s", message);
}

static void json_predicate(JsonBuilder *builder, yyjson_mut_val *outputs,
                           const char *name, const char *kind, int goal,
                           int level, int fairness) {
  yyjson_mut_val *row = jb_obj(builder);
  jb_push(builder, outputs, row);
  JB_STR(builder, row, "name", name);
  JB_STR(builder, row, "kind", kind);
  if (goal >= 0)
    JB_SINT(builder, row, "goal", goal);
  if (level >= 0)
    JB_SINT(builder, row, "level", level);
  if (fairness >= 0)
    JB_SINT(builder, row, "fairness", fairness);
}

static bool write_certificate_json(
    FILE *out, const Aig *certificate, const Aig *game, const char *aag_path,
    bool unreal, Gr1CertificateSemantics semantics, uint32_t original_nlat,
    uint32_t m_goal_records, uint32_t m_goals, uint32_t m_fair,
    uint32_t n_fair_disj, const uint32_t *goal_record,
    const uint32_t *goal_member, const BddVec *y_levels, size_t artifact_cap) {
  uint32_t nin = aig_num_inputs(game);
  uint32_t nlat = aig_num_latches(game);
  uint32_t nu = 0, nc = 0;
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (is_controllable(name))
      nc++;
    else
      nu++;
  }
  JsonBuilder builder = jb_new_bounded(artifact_cap);
  yyjson_mut_val *root = jb_obj(&builder);
  JB_STR(&builder, root, "format", "tlsf-gr1-certificate-v1");
  JB_STR(&builder, root, "status", unreal ? "unrealizable" : "realizable");
  JB_STR(&builder, root, "side", unreal ? "environment" : "system");
  JB_STR(&builder, root, "reduction_semantics",
         semantics == GR1_CERTIFICATE_SEMANTICS_EXACT ? "exact" : "strict");
  yyjson_mut_val *circuit = jb_obj(&builder);
  JB_STR(&builder, circuit, "path", aag_path);
  JB_STR(&builder, circuit, "kind", "ASCII AIGER combinational");
  jb_put(&builder, root, "circuit", circuit);
  JB_STR(&builder, root, "fixpoint",
         "Z = nu Z. AND_j mu Y. OR_i nu X. "
         "cpre((Z & goal_j) | Y | (X & !fair_i))");
  yyjson_mut_val *counts = jb_obj(&builder);
  JB_UINT(&builder, counts, "goals", m_goals);
  JB_UINT(&builder, counts, "justice_records", m_goal_records);
  JB_UINT(&builder, counts, "fairness_assumptions", m_fair);
  JB_UINT(&builder, counts, "state_variables", nlat);
  JB_UINT(&builder, counts, "original_game_latches", original_nlat);
  JB_UINT(&builder, counts, "sampling_latches", nlat - original_nlat);
  JB_UINT(&builder, counts, "uncontrollable_inputs", nu);
  JB_UINT(&builder, counts, "controllable_inputs", nc);
  JB_UINT(&builder, counts, "predicates", aig_num_outputs(certificate));
  JB_UINT(&builder, counts, "aig_inputs", aig_num_inputs(certificate));
  JB_UINT(&builder, counts, "aig_latches", aig_num_latches(certificate));
  JB_UINT(&builder, counts, "aig_ands", aig_num_ands(certificate));
  yyjson_mut_val *levels = jb_arr(&builder);
  for (uint32_t j = 0; j < m_goals; j++)
    jb_push(&builder, levels, jb_uint(&builder, y_levels[j].n));
  jb_put(&builder, counts, "levels_per_goal", levels);
  jb_put(&builder, root, "counts", counts);
  yyjson_mut_val *outputs = jb_arr(&builder);
  json_predicate(&builder, outputs, "inv", "winning_region", -1, -1, -1);
  if (unreal)
    json_predicate(&builder, outputs, "losing", "nonwinning_region", -1, -1,
                   -1);
  char name[96];
  for (uint32_t j = 0; j < m_goals; j++) {
    snprintf(name, sizeof name, "goal_%u", j);
    json_predicate(&builder, outputs, name, "goal", (int)j, -1, -1);
  }
  for (uint32_t j = 0; j < m_goals; j++)
    for (uint32_t k = 0; k < y_levels[j].n; k++) {
      snprintf(name, sizeof name, "y_%u_%u", j, k);
      json_predicate(&builder, outputs, name, "mu_level", (int)j, (int)k, -1);
    }
  for (uint32_t j = 0; j < m_goals; j++)
    for (uint32_t k = 0; k < y_levels[j].n; k++)
      for (uint32_t i = 0; i < n_fair_disj; i++) {
        snprintf(name, sizeof name, "x_%u_%u_%u", j, k, i);
        json_predicate(&builder, outputs, name, "nu_level", (int)j, (int)k,
                       (int)i);
      }
  if (!unreal)
    for (uint32_t j = 0; j < m_goals; j++) {
      snprintf(name, sizeof name, "move_%u", j);
      json_predicate(&builder, outputs, name, "move_relation", (int)j, -1, -1);
    }
  jb_put(&builder, root, "outputs", outputs);
  yyjson_mut_val *goals = jb_arr(&builder);
  for (uint32_t j = 0; j < m_goals; j++) {
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, goals, row);
    JB_UINT(&builder, row, "goal", j);
    JB_UINT(&builder, row, "justice_record", goal_record[j]);
    JB_UINT(&builder, row, "record_member", goal_member[j]);
  }
  jb_put(&builder, root, "goals", goals);
  yyjson_mut_val *variables = jb_obj(&builder);
  yyjson_mut_val *state = jb_arr(&builder);
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur, next, reset;
    aig_latch_at(game, j, &cur, &next, &reset);
    const char *latch_name = aig_latch_name(game, j);
    char fallback[32];
    if (!latch_name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      latch_name = fallback;
    }
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, state, row);
    JB_UINT(&builder, row, "certificate_input", j);
    JB_STR(&builder, row, "name", latch_name);
    JB_UINT(&builder, row, "game_latch", j);
    JB_UINT(&builder, row, "game_literal", cur);
    JB_UINT(&builder, row, "next_game_literal", next);
    JB_UINT(&builder, row, "reset", reset);
    JB_BOOL(&builder, row, "solver_added", j >= original_nlat);
    if (j >= original_nlat) {
      yyjson_mut_val *source = nullptr;
      for (uint32_t r = 0; r < m_goal_records && !source; r++) {
        const uint32_t *lits;
        uint32_t count;
        aig_justice_at(game, r, &lits, &count);
        for (uint32_t k = 0; k < count; k++)
          if (lits[k] == cur) {
            source = jb_obj(&builder);
            JB_STR(&builder, source, "kind", "justice");
            JB_UINT(&builder, source, "record", r);
            JB_UINT(&builder, source, "member", k);
            break;
          }
      }
      for (uint32_t i = 0; i < m_fair && !source; i++)
        if (aig_fairness_at(game, i) == cur) {
          source = jb_obj(&builder);
          JB_STR(&builder, source, "kind", "fairness");
          JB_UINT(&builder, source, "index", i);
        }
      jb_put(&builder, row, "source", source ? source : jb_null(&builder));
    }
  }
  jb_put(&builder, variables, "state", state);
  yyjson_mut_val *uncontrollable = jb_arr(&builder);
  yyjson_mut_val *controllable = jb_arr(&builder);
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *input_name = aig_input_name(game, p, &lit);
    bool control = is_controllable(input_name);
    char fallback[32];
    input_name = oxidd_input_name_or_synthetic(input_name, p, fallback);
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, control ? controllable : uncontrollable, row);
    JB_UINT(&builder, row, "certificate_input", nlat + p);
    JB_UINT(&builder, row, "game_input", p);
    JB_UINT(&builder, row, "game_literal", lit);
    JB_STR(&builder, row, "name", input_name);
  }
  jb_put(&builder, variables, "uncontrollable", uncontrollable);
  jb_put(&builder, variables, "controllable", controllable);
  jb_put(&builder, root, "variables", variables);
  JB_STR(&builder, root, "sampling_semantics",
         "Each solver-added reset-0 latch stores the preceding letter's "
         "input-dependent acceptance literal: next(sample)=source. "
         "The corresponding GF predicate is replaced by sample because "
         "GF p iff GF X p.");
  yyjson_mut_val *counters = jb_arr(&builder);
  for (uint32_t j = 0; j < m_goals; j++) {
    char counter_name[64];
    snprintf(counter_name, sizeof counter_name, "__tlsf_gr1_goal_counter_%u",
             j);
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, counters, row);
    JB_UINT(&builder, row, "strategy_latch", nlat + j);
    JB_STR(&builder, row, "name", counter_name);
    JB_UINT(&builder, row, "goal", j);
    JB_UINT(&builder, row, "reset", 0);
    JB_BOOL(&builder, row, "effective_initial", j == 0);
    JB_UINT(&builder, row, "advance_to_goal", (j + 1) % m_goals);
  }
  jb_put(&builder, root, "goal_counter_latches", counters);
  JB_STR(&builder, root, "goal_counter_semantics",
         "Strategy latches after the game/sampling latches are one-hot "
         "goal counters. All reset to 0; all-zero is interpreted as "
         "goal 0, then goal j advances to (j+1) mod goals exactly when "
         "inv & goal_j holds.");
  JB_STR(&builder, root, "rank_semantics",
         "For goal j the selected rank is the least lexicographic (k,i) "
         "whose x_j_k_i contains the state; y_j_k is the union of the "
         "fairness disjuncts at mu level k.");
  JB_STR(&builder, root, "move_semantics",
         "move_j is the pre-Skolem most-permissive relation over state, "
         "uncontrollable inputs and controllable inputs: advance safely "
         "inside inv at goal_j; otherwise move to goal/lower rank or "
         "stay in the selected x_j_k_i while fair_i is false.");
  if (unreal)
    JB_BOOL(&builder, root, "environment_counter_strategy_exported", false);
  return jb_write(&builder, root, out);
}

static bool export_certificate(
    OxiddRun *run, Aig *game, Gr1CertificateOptions *options, bool unreal,
    uint32_t original_nlat, uint32_t m_goal_records, uint32_t m_goals,
    uint32_t m_fair, uint32_t n_fair_disj, uint32_t nin, uint32_t nlat,
    uint32_t nvars, uint32_t var_base, const uint32_t *goal_record,
    const uint32_t *goal_member, const Bdd *goal_bdd, const BddVec *y_levels,
    const BddVec *x_levels, const Bdd *move_bdd, Bdd W) {
  Aig *certificate = aig_new();
  uint32_t *var2lit = malloc(nvars * sizeof *var2lit);
  if (!certificate || !var2lit) {
    oxidd_record_failure(run->options, OXIDD_FAILURE_HOST, run->phase,
                         "certificate_allocation", run->operations, run->index);
    aig_free(certificate);
    free(var2lit);
    certificate_error(options, "cannot allocate GR(1) certificate", nullptr);
    return false;
  }
  for (uint32_t v = 0; v < nvars; v++)
    var2lit[v] = UINT32_MAX;

  // The public circuit orders solver state first, followed by game inputs.
  // The BDD layout has the reverse blocks; var2lit performs that permutation.
  for (uint32_t j = 0; j < nlat; j++) {
    const char *name = aig_latch_name(game, j);
    char fallback[32];
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    var2lit[nin + j] = aig_input(certificate, name);
  }
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    char fallback[32];
    name = oxidd_input_name_or_synthetic(name, p, fallback);
    var2lit[p] = aig_input(certificate, name);
  }

  Bdd2Aig ctx = {certificate, var2lit, var_base, nvars, {0}, false, run, 0};
  aig_set_output(certificate, "inv", bdd2aig(&ctx, W));
  if (unreal) {
    Bdd losing = oxidd_run_not(run, W);
    aig_set_output(certificate, "losing", bdd2aig(&ctx, losing));
    oxidd_bdd_unref(losing);
  }
  char name[96];
  for (uint32_t j = 0; j < m_goals; j++) {
    snprintf(name, sizeof name, "goal_%u", j);
    aig_set_output(certificate, name, bdd2aig(&ctx, goal_bdd[j]));
  }
  for (uint32_t j = 0; j < m_goals; j++)
    for (uint32_t k = 0; k < y_levels[j].n; k++) {
      snprintf(name, sizeof name, "y_%u_%u", j, k);
      aig_set_output(certificate, name, bdd2aig(&ctx, y_levels[j].arr[k]));
    }
  for (uint32_t j = 0; j < m_goals; j++)
    for (uint32_t k = 0; k < y_levels[j].n; k++)
      for (uint32_t i = 0; i < n_fair_disj; i++) {
        snprintf(name, sizeof name, "x_%u_%u_%u", j, k, i);
        aig_set_output(certificate, name,
                       bdd2aig(&ctx, x_levels[j * n_fair_disj + i].arr[k]));
      }
  if (!unreal)
    for (uint32_t j = 0; j < m_goals; j++) {
      snprintf(name, sizeof name, "move_%u", j);
      aig_set_output(certificate, name, bdd2aig(&ctx, move_bdd[j]));
    }
  memo_free(&ctx.memo);
  free(var2lit);
  if (ctx.error) {
    if (!run->stopped)
      oxidd_record_failure(run->options, OXIDD_FAILURE_CONVERSION, run->phase,
                           "certificate_bdd2aig", run->operations, run->index);
    aig_free(certificate);
    certificate_error(options, "BDD-to-AIG certificate conversion failed",
                      nullptr);
    return false;
  }

  FILE *aag = options->aag_bytes
                  ? open_export_memstream(run, options, options->aag_bytes,
                                          options->aag_size)
                  : fopen(options->aag_path, "w");
  if (!aag) {
    aig_free(certificate);
    certificate_error(options, "cannot open certificate", options->aag_path);
    return false;
  }
  aig_write_aag(aag, certificate);
  bool aag_ok = !ferror(aag);
  if (fclose(aag) != 0)
    aag_ok = false;
  if (!aag_ok) {
    aig_free(certificate);
    certificate_error(options, "cannot write certificate", options->aag_path);
    return false;
  }

  if (options->json_path || options->json_bytes) {
    FILE *json = options->json_bytes
                     ? open_export_memstream(run, options, options->json_bytes,
                                             options->json_size)
                     : fopen(options->json_path, "w");
    if (!json) {
      aig_free(certificate);
      certificate_error(options, "cannot open certificate sidecar",
                        options->json_path);
      return false;
    }
    bool json_ok = write_certificate_json(
        json, certificate, game,
        options->aag_path ? options->aag_path : "memory", unreal,
        options->semantics, original_nlat, m_goal_records, m_goals, m_fair,
        n_fair_disj, goal_record, goal_member, y_levels,
        options->max_artifact_bytes);
    if (fclose(json) != 0)
      json_ok = false;
    if (!json_ok) {
      aig_free(certificate);
      certificate_error(options, "cannot write certificate sidecar",
                        options->json_path);
      return false;
    }
  }
  aig_free(certificate);
  return true;
}

static bool write_policy_json(FILE *out, const Aig *policy, const Aig *game,
                              const char *aag_path, uint32_t original_nlat,
                              uint32_t m_goals,
                              Gr1CertificateSemantics semantics,
                              size_t artifact_cap) {
  uint32_t nin = aig_num_inputs(game), nlat = aig_num_latches(game);
  uint32_t nu = 0, nc = 0;
  for (uint32_t p = 0; p < nin; p++) {
    if (is_controllable(aig_input_name(game, p, nullptr)))
      nc++;
    else
      nu++;
  }
  JsonBuilder builder = jb_new_bounded(artifact_cap);
  yyjson_mut_val *root = jb_obj(&builder);
  JB_STR(&builder, root, "format", "tlsf-gr1-policy-v1");
  JB_STR(&builder, root, "side", "system");
  JB_STR(&builder, root, "reduction_semantics",
         semantics == GR1_CERTIFICATE_SEMANTICS_EXACT ? "exact" : "strict");
  yyjson_mut_val *circuit = jb_obj(&builder);
  JB_STR(&builder, circuit, "path", aag_path);
  JB_STR(&builder, circuit, "kind", "ASCII AIGER combinational");
  jb_put(&builder, root, "circuit", circuit);
  yyjson_mut_val *counts = jb_obj(&builder);
  JB_UINT(&builder, counts, "game_state_variables", nlat);
  JB_UINT(&builder, counts, "original_game_latches", original_nlat);
  JB_UINT(&builder, counts, "sampling_latches", nlat - original_nlat);
  JB_UINT(&builder, counts, "goals", m_goals);
  JB_UINT(&builder, counts, "uncontrollable_inputs", nu);
  JB_UINT(&builder, counts, "controllable_outputs", nc);
  JB_UINT(&builder, counts, "aig_inputs", aig_num_inputs(policy));
  JB_UINT(&builder, counts, "aig_outputs", aig_num_outputs(policy));
  JB_UINT(&builder, counts, "aig_ands", aig_num_ands(policy));
  jb_put(&builder, root, "counts", counts);
  yyjson_mut_val *inputs = jb_obj(&builder);
  yyjson_mut_val *state = jb_arr(&builder);
  for (uint32_t j = 0; j < nlat; j++) {
    const char *name = aig_latch_name(game, j);
    char fallback[32];
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, state, row);
    JB_UINT(&builder, row, "policy_input", j);
    JB_UINT(&builder, row, "game_latch", j);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, inputs, "state", state);
  yyjson_mut_val *counter = jb_arr(&builder);
  for (uint32_t j = 0; j < m_goals; j++) {
    char name[64];
    snprintf(name, sizeof name, "curr_%u", j);
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, counter, row);
    JB_UINT(&builder, row, "policy_input", nlat + j);
    JB_UINT(&builder, row, "goal", j);
    JB_STR(&builder, row, "name", name);
    JB_UINT(&builder, row, "reset", 0);
    JB_BOOL(&builder, row, "effective_initial", j == 0);
  }
  jb_put(&builder, inputs, "counter", counter);
  yyjson_mut_val *uncontrollable = jb_arr(&builder);
  uint32_t policy_input = nlat + m_goals;
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (is_controllable(name))
      continue;
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, uncontrollable, row);
    JB_UINT(&builder, row, "policy_input", policy_input++);
    JB_UINT(&builder, row, "game_input", p);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, inputs, "uncontrollable", uncontrollable);
  jb_put(&builder, root, "inputs", inputs);
  yyjson_mut_val *outputs = jb_obj(&builder);
  yyjson_mut_val *controllable = jb_arr(&builder);
  uint32_t policy_output = 0;
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (!is_controllable(name))
      continue;
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, controllable, row);
    JB_UINT(&builder, row, "policy_output", policy_output++);
    JB_UINT(&builder, row, "game_input", p);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, outputs, "controllable", controllable);
  yyjson_mut_val *next = jb_arr(&builder);
  for (uint32_t j = 0; j < m_goals; j++) {
    char name[64];
    snprintf(name, sizeof name, "curr_next_%u", j);
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, next, row);
    JB_UINT(&builder, row, "policy_output", policy_output + j);
    JB_UINT(&builder, row, "goal", j);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, outputs, "counter_next", next);
  jb_put(&builder, root, "outputs", outputs);
  JB_STR(&builder, root, "counter_semantics",
         "All curr bits reset to zero; all-zero is interpreted as curr_0. "
         "Every transition produces exactly one hot next bit, advancing "
         "from j to (j+1) mod goals iff goal_j holds, otherwise staying.");
  return jb_write(&builder, root, out);
}

static bool export_policy(OxiddRun *run, const Aig *game,
                          Gr1CertificateOptions *options,
                          uint32_t original_nlat, uint32_t m_goals,
                          uint32_t nin, uint32_t nlat, uint32_t nvars,
                          uint32_t var_base, const uint32_t *cinput,
                          uint32_t ncv, const Bdd *strat_f,
                          const Bdd *next_curr) {
  Aig *policy = aig_new();
  uint32_t *var2lit = malloc(nvars * sizeof *var2lit);
  if (!policy || !var2lit) {
    oxidd_record_failure(run->options, OXIDD_FAILURE_HOST, run->phase,
                         "policy_allocation", run->operations, run->index);
    aig_free(policy);
    free(var2lit);
    certificate_error(options, "cannot allocate GR(1) policy", nullptr);
    return false;
  }
  for (uint32_t v = 0; v < nvars; v++)
    var2lit[v] = UINT32_MAX;

  for (uint32_t j = 0; j < nlat; j++) {
    const char *name = aig_latch_name(game, j);
    char fallback[32];
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    var2lit[nin + j] = aig_input(policy, name);
  }
  char name[96];
  for (uint32_t j = 0; j < m_goals; j++) {
    snprintf(name, sizeof name, "curr_%u", j);
    var2lit[nin + nlat + j] = aig_input(policy, name);
  }
  for (uint32_t p = 0; p < nin; p++) {
    const char *input_name = aig_input_name(game, p, nullptr);
    if (!is_controllable(input_name))
      var2lit[p] = aig_input(policy, input_name);
  }

  Bdd2Aig ctx = {policy, var2lit, var_base, nvars, {0}, false, run, 0};
  for (uint32_t k = 0; k < ncv; k++) {
    const char *output_name = aig_input_name(game, cinput[k], nullptr);
    aig_set_output(policy, output_name, bdd2aig(&ctx, strat_f[k]));
  }
  for (uint32_t j = 0; j < m_goals; j++) {
    snprintf(name, sizeof name, "curr_next_%u", j);
    aig_set_output(policy, name, bdd2aig(&ctx, next_curr[j]));
  }
  memo_free(&ctx.memo);
  free(var2lit);
  if (ctx.error) {
    if (!run->stopped)
      oxidd_record_failure(run->options, OXIDD_FAILURE_CONVERSION, run->phase,
                           "policy_bdd2aig", run->operations, run->index);
    aig_free(policy);
    certificate_error(options, "BDD-to-AIG policy conversion failed", nullptr);
    return false;
  }

  FILE *aag =
      options->policy_aag_bytes
          ? open_export_memstream(run, options, options->policy_aag_bytes,
                                  options->policy_aag_size)
          : fopen(options->policy_aag_path, "w");
  if (!aag) {
    aig_free(policy);
    certificate_error(options, "cannot open policy", options->policy_aag_path);
    return false;
  }
  aig_write_aag(aag, policy);
  bool ok = !ferror(aag);
  if (fclose(aag) != 0)
    ok = false;
  if (!ok) {
    aig_free(policy);
    certificate_error(options, "cannot write policy", options->policy_aag_path);
    return false;
  }

  FILE *json =
      options->policy_json_bytes
          ? open_export_memstream(run, options, options->policy_json_bytes,
                                  options->policy_json_size)
          : fopen(options->policy_json_path, "w");
  if (!json) {
    aig_free(policy);
    certificate_error(options, "cannot open policy sidecar",
                      options->policy_json_path);
    return false;
  }
  ok = write_policy_json(
      json, policy, game,
      options->policy_aag_path ? options->policy_aag_path : "memory",
      original_nlat, m_goals, options->semantics, options->max_artifact_bytes);
  if (fclose(json) != 0)
    ok = false;
  aig_free(policy);
  if (!ok) {
    certificate_error(options, "cannot write policy sidecar",
                      options->policy_json_path);
    return false;
  }
  return true;
}

static bool write_environment_policy_json(FILE *out, const Aig *policy,
                                          const Aig *game, const char *aag_path,
                                          uint32_t original_nlat,
                                          uint32_t goals,
                                          uint32_t fairness_counters,
                                          size_t artifact_cap) {
  uint32_t nin = aig_num_inputs(game), nlat = aig_num_latches(game);
  uint32_t nu = 0, nc = 0;
  for (uint32_t p = 0; p < nin; p++) {
    if (is_controllable(aig_input_name(game, p, nullptr)))
      nc++;
    else
      nu++;
  }
  JsonBuilder builder = jb_new_bounded(artifact_cap);
  yyjson_mut_val *root = jb_obj(&builder);
  JB_STR(&builder, root, "format", "tlsf-gr1-policy-v1");
  JB_STR(&builder, root, "side", "environment");
  JB_STR(&builder, root, "reduction_semantics", "exact");
  JB_STR(&builder, root, "system_strategy_semantics", "mealy");
  JB_STR(&builder, root, "strategy_semantics", "moore");
  JB_UINT(&builder, root, "duality_delay_steps", 1);
  yyjson_mut_val *circuit = jb_obj(&builder);
  JB_STR(&builder, circuit, "path", aag_path);
  JB_STR(&builder, circuit, "kind", "ASCII AIGER combinational");
  jb_put(&builder, root, "circuit", circuit);
  yyjson_mut_val *counts = jb_obj(&builder);
  JB_UINT(&builder, counts, "game_state_variables", nlat);
  JB_UINT(&builder, counts, "original_game_latches", original_nlat);
  JB_UINT(&builder, counts, "sampling_latches", nlat - original_nlat);
  JB_UINT(&builder, counts, "goals", goals);
  JB_UINT(&builder, counts, "fairness_counters", fairness_counters);
  JB_UINT(&builder, counts, "controllable_inputs", nc);
  JB_UINT(&builder, counts, "uncontrollable_outputs", nu);
  JB_UINT(&builder, counts, "aig_inputs", aig_num_inputs(policy));
  JB_UINT(&builder, counts, "aig_outputs", aig_num_outputs(policy));
  JB_UINT(&builder, counts, "aig_ands", aig_num_ands(policy));
  jb_put(&builder, root, "counts", counts);
  yyjson_mut_val *inputs = jb_obj(&builder);
  yyjson_mut_val *state = jb_arr(&builder);
  for (uint32_t j = 0; j < nlat; j++) {
    char fallback[32];
    const char *name = aig_latch_name(game, j);
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, state, row);
    JB_UINT(&builder, row, "policy_input", j);
    JB_UINT(&builder, row, "game_latch", j);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, inputs, "state", state);
  yyjson_mut_val *counter = jb_arr(&builder);
  for (uint32_t i = 0; i < fairness_counters; i++) {
    char name[64];
    snprintf(name, sizeof name, "curr_%u", i);
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, counter, row);
    JB_UINT(&builder, row, "policy_input", nlat + i);
    JB_UINT(&builder, row, "fairness", i);
    JB_STR(&builder, row, "name", name);
    JB_UINT(&builder, row, "reset", 0);
    JB_BOOL(&builder, row, "effective_initial", i == 0);
  }
  jb_put(&builder, inputs, "counter", counter);
  jb_put(&builder, inputs, "controllable", jb_arr(&builder));
  jb_put(&builder, root, "inputs", inputs);
  yyjson_mut_val *outputs = jb_obj(&builder);
  yyjson_mut_val *uncontrollable = jb_arr(&builder);
  uint32_t output = 0;
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (is_controllable(name))
      continue;
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, uncontrollable, row);
    JB_UINT(&builder, row, "policy_output", output++);
    JB_UINT(&builder, row, "game_input", p);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, outputs, "uncontrollable", uncontrollable);
  yyjson_mut_val *next = jb_arr(&builder);
  for (uint32_t i = 0; i < fairness_counters; i++) {
    char name[64];
    snprintf(name, sizeof name, "curr_next_%u", i);
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, next, row);
    JB_UINT(&builder, row, "policy_output", output + i);
    JB_UINT(&builder, row, "fairness", i);
    JB_STR(&builder, row, "name", name);
  }
  jb_put(&builder, outputs, "counter_next", next);
  jb_put(&builder, root, "outputs", outputs);
  JB_STR(&builder, root, "counter_semantics",
         "The all-zero state means fairness counter 0. At a state where "
         "fair_i holds the counter advances to (i+1) modulo the number "
         "of fairness assumptions. The uncontrollable outputs do not "
         "read the current controllable letter.");
  return jb_write(&builder, root, out);
}

static bool export_environment_policy(OxiddRun *run, const Aig *game,
                                      Gr1CertificateOptions *options,
                                      uint32_t original_nlat, uint32_t goals,
                                      uint32_t fairness_counters, uint32_t nin,
                                      uint32_t nlat, uint32_t nvars,
                                      uint32_t var_base, const uint32_t *uinput,
                                      uint32_t nuv, const Bdd *strategy,
                                      const Bdd *next_curr) {
  Aig *policy = aig_new();
  uint32_t *var2lit = malloc(nvars * sizeof *var2lit);
  if (!policy || !var2lit) {
    aig_free(policy);
    free(var2lit);
    certificate_error(options, "cannot allocate environment policy", nullptr);
    return false;
  }
  for (uint32_t v = 0; v < nvars; v++)
    var2lit[v] = UINT32_MAX;
  for (uint32_t j = 0; j < nlat; j++) {
    char fallback[32];
    const char *name = aig_latch_name(game, j);
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    var2lit[nin + j] = aig_input(policy, name);
  }
  char name[96];
  for (uint32_t i = 0; i < fairness_counters; i++) {
    snprintf(name, sizeof name, "curr_%u", i);
    var2lit[nin + nlat + i] = aig_input(policy, name);
  }
  Bdd2Aig conversion = {policy, var2lit, var_base, nvars, {0}, false, run, 0};
  for (uint32_t i = 0; i < nuv; i++)
    aig_set_output(policy, aig_input_name(game, uinput[i], nullptr),
                   bdd2aig(&conversion, strategy[i]));
  for (uint32_t i = 0; i < fairness_counters; i++) {
    snprintf(name, sizeof name, "curr_next_%u", i);
    aig_set_output(policy, name, bdd2aig(&conversion, next_curr[i]));
  }
  memo_free(&conversion.memo);
  free(var2lit);
  if (conversion.error) {
    aig_free(policy);
    certificate_error(options, "BDD-to-AIG environment policy failed", nullptr);
    return false;
  }
  FILE *aag =
      options->policy_aag_bytes
          ? open_export_memstream(run, options, options->policy_aag_bytes,
                                  options->policy_aag_size)
          : fopen(options->policy_aag_path, "w");
  if (!aag) {
    aig_free(policy);
    certificate_error(options, "cannot open policy", options->policy_aag_path);
    return false;
  }
  aig_write_aag(aag, policy);
  bool ok = !ferror(aag);
  if (fclose(aag) != 0)
    ok = false;
  if (!ok) {
    aig_free(policy);
    certificate_error(options, "cannot write policy", options->policy_aag_path);
    return false;
  }
  FILE *json =
      options->policy_json_bytes
          ? open_export_memstream(run, options, options->policy_json_bytes,
                                  options->policy_json_size)
          : fopen(options->policy_json_path, "w");
  if (!json) {
    aig_free(policy);
    certificate_error(options, "cannot open policy sidecar",
                      options->policy_json_path);
    return false;
  }
  ok = write_environment_policy_json(
      json, policy, game,
      options->policy_aag_path ? options->policy_aag_path : "memory",
      original_nlat, goals, fairness_counters, options->max_artifact_bytes);
  if (fclose(json) != 0)
    ok = false;
  aig_free(policy);
  if (!ok)
    certificate_error(options, "cannot write policy sidecar",
                      options->policy_json_path);
  return ok;
}

static bool write_environment_certificate_json(
    FILE *out, const Aig *certificate, const Aig *game, const char *aag_path,
    uint32_t original_nlat, uint32_t goals, uint32_t fairness,
    uint32_t fairness_counters, const DualVec *levels, size_t artifact_cap) {
  uint32_t nin = aig_num_inputs(game), nlat = aig_num_latches(game);
  uint32_t nu = 0, nc = 0;
  for (uint32_t p = 0; p < nin; p++) {
    if (is_controllable(aig_input_name(game, p, nullptr)))
      nc++;
    else
      nu++;
  }
  JsonBuilder builder = jb_new_bounded(artifact_cap);
  yyjson_mut_val *root = jb_obj(&builder);
  JB_STR(&builder, root, "format", "tlsf-gr1-certificate-v1");
  JB_STR(&builder, root, "status", "unrealizable");
  JB_STR(&builder, root, "side", "environment");
  JB_STR(&builder, root, "reduction_semantics", "exact");
  JB_STR(&builder, root, "system_strategy_semantics", "mealy");
  JB_STR(&builder, root, "strategy_semantics", "moore");
  JB_UINT(&builder, root, "duality_delay_steps", 1);
  JB_BOOL(&builder, root, "environment_counter_strategy_exported", true);
  JB_STR(&builder, root, "witness_condition",
         "nonempty intersection of the delayed environment counter-strategy "
         "language with the specification complement");
  yyjson_mut_val *circuit = jb_obj(&builder);
  JB_STR(&builder, circuit, "path", aag_path);
  JB_STR(&builder, circuit, "kind", "ASCII AIGER combinational");
  jb_put(&builder, root, "circuit", circuit);
  JB_STR(&builder, root, "fixpoint",
         "L = mu Z. OR_j nu Y. AND_i mu X. "
         "dpre((Z | !goal_j) & Y & (X | fair_i))");
  yyjson_mut_val *counts = jb_obj(&builder);
  JB_UINT(&builder, counts, "goals", goals);
  JB_UINT(&builder, counts, "fairness_assumptions", fairness);
  JB_UINT(&builder, counts, "fairness_counters", fairness_counters);
  JB_UINT(&builder, counts, "state_variables", nlat);
  JB_UINT(&builder, counts, "original_game_latches", original_nlat);
  JB_UINT(&builder, counts, "sampling_latches", nlat - original_nlat);
  JB_UINT(&builder, counts, "uncontrollable_inputs", nu);
  JB_UINT(&builder, counts, "controllable_inputs", nc);
  JB_UINT(&builder, counts, "outer_levels", levels->n);
  JB_UINT(&builder, counts, "predicates", aig_num_outputs(certificate));
  JB_UINT(&builder, counts, "aig_inputs", aig_num_inputs(certificate));
  JB_UINT(&builder, counts, "aig_latches", aig_num_latches(certificate));
  JB_UINT(&builder, counts, "aig_ands", aig_num_ands(certificate));
  jb_put(&builder, root, "counts", counts);
  JB_STR(&builder, root, "rank_semantics",
         "The least outer level and least goal identify the co-Buchi "
         "goal. For the active fairness counter, the least inner X level "
         "must decrease until fair_i holds. Outer-rank decreases permit "
         "only finitely many goal changes.");
  JB_STR(&builder, root, "move_semantics",
         "move_i is the pre-Skolem relation bad | target(next). The "
         "exported uncontrollable policy is Skolemized only after "
         "universal quantification of every current controllable input.");
  return jb_write(&builder, root, out);
}

static bool export_environment_certificate(
    OxiddRun *run, const Aig *game, Gr1CertificateOptions *options,
    uint32_t original_nlat, uint32_t goals, uint32_t fairness,
    uint32_t fairness_counters, uint32_t nin, uint32_t nlat, uint32_t nvars,
    uint32_t var_base, const Bdd *goal_bdd, const Bdd *fair_bdd,
    const DualVec *levels, const Bdd *move, Bdd losing) {
  Aig *certificate = aig_new();
  uint32_t *var2lit = malloc(nvars * sizeof *var2lit);
  if (!certificate || !var2lit) {
    aig_free(certificate);
    free(var2lit);
    certificate_error(options, "cannot allocate environment certificate",
                      nullptr);
    return false;
  }
  for (uint32_t v = 0; v < nvars; v++)
    var2lit[v] = UINT32_MAX;
  for (uint32_t j = 0; j < nlat; j++) {
    char fallback[32];
    const char *name = aig_latch_name(game, j);
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    var2lit[nin + j] = aig_input(certificate, name);
  }
  for (uint32_t p = 0; p < nin; p++) {
    char fallback[32];
    const char *name = oxidd_input_name_or_synthetic(
        aig_input_name(game, p, nullptr), p, fallback);
    var2lit[p] = aig_input(certificate, name);
  }
  Bdd2Aig conversion = {certificate, var2lit, var_base, nvars,
                        {0},         false,   run,      0};
  aig_set_output(certificate, "inv", bdd2aig(&conversion, losing));
  Bdd system_winning = oxidd_run_not(run, losing);
  aig_set_output(certificate, "system_winning",
                 bdd2aig(&conversion, system_winning));
  oxidd_bdd_unref(system_winning);
  char name[128];
  for (uint32_t j = 0; j < goals; j++) {
    snprintf(name, sizeof name, "goal_%u", j);
    aig_set_output(certificate, name, bdd2aig(&conversion, goal_bdd[j]));
  }
  for (uint32_t i = 0; i < fairness; i++) {
    snprintf(name, sizeof name, "fair_%u", i);
    aig_set_output(certificate, name, bdd2aig(&conversion, fair_bdd[i]));
  }
  for (uint32_t k = 0; k < levels->n; k++) {
    const DualLevel *level = &levels->arr[k];
    snprintf(name, sizeof name, "z_%u", k);
    aig_set_output(certificate, name, bdd2aig(&conversion, level->z));
    for (uint32_t j = 0; j < goals; j++) {
      snprintf(name, sizeof name, "y_%u_%u", k, j);
      aig_set_output(certificate, name, bdd2aig(&conversion, level->y[j]));
      for (uint32_t i = 0; i < fairness_counters; i++) {
        const BddVec *inner = &level->x[j * fairness_counters + i];
        for (uint32_t l = 0; l < inner->n; l++) {
          snprintf(name, sizeof name, "x_%u_%u_%u_%u", k, j, i, l);
          aig_set_output(certificate, name,
                         bdd2aig(&conversion, inner->arr[l]));
        }
      }
    }
  }
  for (uint32_t i = 0; i < fairness_counters; i++) {
    snprintf(name, sizeof name, "move_%u", i);
    aig_set_output(certificate, name, bdd2aig(&conversion, move[i]));
  }
  memo_free(&conversion.memo);
  free(var2lit);
  if (conversion.error) {
    aig_free(certificate);
    certificate_error(options, "BDD-to-AIG environment certificate failed",
                      nullptr);
    return false;
  }
  FILE *aag = options->aag_bytes
                  ? open_export_memstream(run, options, options->aag_bytes,
                                          options->aag_size)
                  : fopen(options->aag_path, "w");
  if (!aag) {
    aig_free(certificate);
    certificate_error(options, "cannot open certificate", options->aag_path);
    return false;
  }
  aig_write_aag(aag, certificate);
  bool ok = !ferror(aag);
  if (fclose(aag) != 0)
    ok = false;
  if (!ok) {
    aig_free(certificate);
    certificate_error(options, "cannot write certificate", options->aag_path);
    return false;
  }
  if (options->json_path || options->json_bytes) {
    FILE *json = options->json_bytes
                     ? open_export_memstream(run, options, options->json_bytes,
                                             options->json_size)
                     : fopen(options->json_path, "w");
    if (!json) {
      aig_free(certificate);
      certificate_error(options, "cannot open certificate sidecar",
                        options->json_path);
      return false;
    }
    ok = write_environment_certificate_json(
        json, certificate, game,
        options->aag_path ? options->aag_path : "memory", original_nlat, goals,
        fairness, fairness_counters, levels, options->max_artifact_bytes);
    if (fclose(json) != 0)
      ok = false;
  }
  aig_free(certificate);
  if (!ok)
    certificate_error(options, "cannot write certificate sidecar",
                      options->json_path);
  return ok;
}

// ---------------------------------------------------------------------------
// cpre helpers
// ---------------------------------------------------------------------------

// Full cpre: ∀u ∃c [¬bad ∧ T[s:=next]]  — T is a state predicate, result too.
static Bdd cpre_full(OxiddRun *run, Bdd T, oxidd_bdd_substitution_t *sub_lat,
                     Bdd notbad, Bdd ctrl_cube, Bdd unc_cube) {
  Bdd img = oxidd_run_substitute(run, T, sub_lat);
  Bdd ec = oxidd_run_apply_exists(run, OXIDD_BOOLEAN_OPERATOR_AND, notbad, img,
                                  ctrl_cube);
  Bdd result = oxidd_run_forall(run, ec, unc_cube);
  oxidd_bdd_unref(img);
  oxidd_bdd_unref(ec);
  return result; // new ref; UINT32_MAX on error → caller checks bdd_invalid
}

// Unquantified cpre: ¬bad ∧ T[s:=next]  — result is over (s, u, c).
static Bdd cpre_unquantified(OxiddRun *run, Bdd T,
                             oxidd_bdd_substitution_t *sub_lat, Bdd notbad) {
  Bdd img = oxidd_run_substitute(run, T, sub_lat);
  Bdd result = oxidd_run_and(run, notbad, img);
  oxidd_bdd_unref(img);
  return result;
}

// Environment dual predecessor:
//   exists u. forall c. [bad | T[s := next]].
// The environment chooses the uncontrollable letter before the system chooses
// its current controllable letter, which is the Moore dual of this Mealy game.
static Bdd dpre_full(OxiddRun *run, Bdd target,
                     oxidd_bdd_substitution_t *sub_lat, Bdd bad, Bdd ctrl_cube,
                     Bdd unc_cube) {
  Bdd image = oxidd_run_substitute(run, target, sub_lat);
  Bdd reaches = oxidd_run_or(run, bad, image);
  Bdd all_control = oxidd_run_forall(run, reaches, ctrl_cube);
  Bdd result = oxidd_run_exists(run, all_control, unc_cube);
  oxidd_bdd_unref(image);
  oxidd_bdd_unref(reaches);
  oxidd_bdd_unref(all_control);
  return result;
}

static Bdd dpre_unquantified(OxiddRun *run, Bdd target,
                             oxidd_bdd_substitution_t *sub_lat, Bdd bad) {
  Bdd image = oxidd_run_substitute(run, target, sub_lat);
  Bdd result = oxidd_run_or(run, bad, image);
  oxidd_bdd_unref(image);
  return result;
}

// Complement of the system PPS fixpoint:
//
//   L = mu Z. OR_j nu Y. AND_i mu X.
//         dpre((Z | !goal_j) & Y & (X | fair_i)).
//
// Every strict outer level and the converged inner-X levels are retained.  A
// counter-strategy can therefore decrease the outer rank finitely often,
// settle on one missed system goal, and cycle through all environment fairness
// assumptions using the inner rank.
static bool compute_dual_fixpoint(OxiddRun *run, uint32_t goals,
                                  uint32_t fairness, const Bdd *goal_bdd,
                                  const Bdd *fair_bdd,
                                  oxidd_bdd_substitution_t *sub_lat, Bdd bad,
                                  Bdd ctrl_cube, Bdd unc_cube, DualVec *levels,
                                  Bdd *losing) {
  oxidd_bdd_manager_t manager = run->manager;
  Bdd z = oxidd_bdd_false(manager);
  bool ok = true;

  for (;;) {
    DualLevel level = {
        .y = calloc(goals, sizeof *level.y),
        .x = calloc((size_t)goals * fairness, sizeof *level.x),
    };
    if (!level.y || !level.x) {
      oxidd_record_failure(run->options, OXIDD_FAILURE_HOST, run->phase,
                           "dual_level_allocation", run->operations,
                           run->index);
      dual_level_free(&level, goals, fairness);
      ok = false;
      break;
    }
    Bdd z_new = oxidd_bdd_false(manager);

    for (uint32_t j = 0; j < goals && ok; j++) {
      Bdd not_goal = oxidd_run_not(run, goal_bdd[j]);
      Bdd z_or_not_goal = oxidd_run_or(run, z, not_goal);
      oxidd_bdd_unref(not_goal);
      Bdd y = oxidd_bdd_true(manager);

      for (;;) {
        Bdd y_new = oxidd_bdd_true(manager);
        for (uint32_t i = 0; i < fairness && ok; i++) {
          BddVec *x_levels = &level.x[j * fairness + i];
          bddvec_free_all(x_levels);
          Bdd x = oxidd_bdd_false(manager);
          Bdd fair =
              fair_bdd ? oxidd_bdd_ref(fair_bdd[i]) : oxidd_bdd_true(manager);

          for (;;) {
            run->index++;
            Bdd x_or_fair = oxidd_run_or(run, x, fair);
            Bdd base = oxidd_run_and(run, z_or_not_goal, y);
            Bdd target = oxidd_run_and(run, base, x_or_fair);
            oxidd_bdd_unref(x_or_fair);
            oxidd_bdd_unref(base);
            Bdd x_new =
                dpre_full(run, target, sub_lat, bad, ctrl_cube, unc_cube);
            oxidd_bdd_unref(target);
            if (bdd_invalid(x_new) || !bddvec_push_ref(run, x_levels, x_new)) {
              oxidd_bdd_unref(x_new);
              ok = false;
              break;
            }
            bool converged = bdd_eq(x_new, x);
            oxidd_bdd_unref(x);
            x = x_new;
            if (converged)
              break;
          }
          oxidd_bdd_unref(fair);
          if (!ok) {
            oxidd_bdd_unref(x);
            break;
          }
          Bdd intersection = oxidd_run_and(run, y_new, x);
          oxidd_bdd_unref(y_new);
          oxidd_bdd_unref(x);
          y_new = intersection;
          if (bdd_invalid(y_new))
            ok = false;
        }
        if (!ok) {
          oxidd_bdd_unref(y_new);
          break;
        }
        bool converged = bdd_eq(y_new, y);
        oxidd_bdd_unref(y);
        y = y_new;
        if (converged)
          break;
      }
      oxidd_bdd_unref(z_or_not_goal);
      if (!ok) {
        oxidd_bdd_unref(y);
        break;
      }
      level.y[j] = oxidd_bdd_ref(y);
      Bdd union_y = oxidd_run_or(run, z_new, y);
      oxidd_bdd_unref(z_new);
      oxidd_bdd_unref(y);
      z_new = union_y;
      if (bdd_invalid(z_new))
        ok = false;
    }

    if (!ok) {
      oxidd_bdd_unref(z_new);
      dual_level_free(&level, goals, fairness);
      break;
    }
    bool converged = bdd_eq(z_new, z);
    if (converged) {
      oxidd_bdd_unref(z);
      z = z_new;
      dual_level_free(&level, goals, fairness);
      break;
    }
    level.z = oxidd_bdd_ref(z_new);
    if (!dualvec_push_take(run, levels, &level)) {
      oxidd_bdd_unref(z_new);
      dual_level_free(&level, goals, fairness);
      ok = false;
      break;
    }
    oxidd_bdd_unref(z);
    z = z_new;
    oxidd_pressure_gc_checkpoint(run);
  }

  if (ok)
    *losing = z;
  else
    oxidd_bdd_unref(z);
  return ok;
}

static bool extract_environment_counterstrategy(
    OxiddRun *run, uint32_t goals, uint32_t fairness, const Bdd *goal_bdd,
    const Bdd *fair_bdd, const DualVec *levels, const Bdd *counter,
    oxidd_bdd_substitution_t *sub_lat, Bdd bad, Bdd ctrl_cube,
    const uint32_t *uvars, uint32_t nuv, Bdd **move_out, Bdd **strategy_out,
    Bdd **next_counter_out) {
  oxidd_bdd_manager_t manager = run->manager;
  Bdd *move = calloc(fairness, sizeof *move);
  Bdd *strategy = nuv ? calloc(nuv, sizeof *strategy) : nullptr;
  Bdd *next_counter = calloc(fairness, sizeof *next_counter);
  Bdd *phase = calloc(fairness, sizeof *phase);
  Bdd *effective = calloc(fairness, sizeof *effective);
  if (!move || (nuv && !strategy) || !next_counter || !phase || !effective) {
    free(move);
    free(strategy);
    free(next_counter);
    free(phase);
    free(effective);
    return false;
  }
  bool ok = true;

  for (uint32_t i = 0; i < fairness && ok; i++) {
    Bdd relation = oxidd_bdd_false(manager);
    for (uint32_t k = 0; k < levels->n && ok; k++) {
      const DualLevel *outer = &levels->arr[k];
      Bdd lower_z =
          k ? oxidd_bdd_ref(levels->arr[k - 1].z) : oxidd_bdd_false(manager);
      Bdd not_lower_z = oxidd_run_not(run, lower_z);
      Bdd outer_layer = oxidd_run_and(run, outer->z, not_lower_z);
      oxidd_bdd_unref(not_lower_z);
      Bdd earlier_goal = oxidd_bdd_false(manager);

      for (uint32_t j = 0; j < goals && ok; j++) {
        Bdd not_earlier = oxidd_run_not(run, earlier_goal);
        Bdd selected0 = oxidd_run_and(run, outer_layer, outer->y[j]);
        Bdd selected = oxidd_run_and(run, selected0, not_earlier);
        oxidd_bdd_unref(selected0);
        oxidd_bdd_unref(not_earlier);
        Bdd covered_x = oxidd_bdd_false(manager);
        const BddVec *inner = &outer->x[j * fairness + i];

        for (uint32_t l = 0; l < inner->n && ok; l++) {
          Bdd not_covered = oxidd_run_not(run, covered_x);
          Bdd rank0 = oxidd_run_and(run, inner->arr[l], not_covered);
          Bdd rank = oxidd_run_and(run, selected, rank0);
          oxidd_bdd_unref(not_covered);
          oxidd_bdd_unref(rank0);

          Bdd not_goal = oxidd_run_not(run, goal_bdd[j]);
          Bdd outer_progress = oxidd_run_or(run, lower_z, not_goal);
          oxidd_bdd_unref(not_goal);
          Bdd base = oxidd_run_and(run, outer_progress, outer->y[j]);
          oxidd_bdd_unref(outer_progress);
          Bdd fair =
              fair_bdd ? oxidd_bdd_ref(fair_bdd[i]) : oxidd_bdd_true(manager);
          Bdd inner_progress = l ? oxidd_run_or(run, inner->arr[l - 1], fair)
                                 : oxidd_bdd_ref(fair);
          oxidd_bdd_unref(fair);
          Bdd target = oxidd_run_and(run, base, inner_progress);
          oxidd_bdd_unref(base);
          oxidd_bdd_unref(inner_progress);
          Bdd step = dpre_unquantified(run, target, sub_lat, bad);
          oxidd_bdd_unref(target);
          Bdd ranked_step = oxidd_run_and(run, rank, step);
          oxidd_bdd_unref(rank);
          oxidd_bdd_unref(step);
          Bdd expanded = oxidd_run_or(run, relation, ranked_step);
          oxidd_bdd_unref(relation);
          oxidd_bdd_unref(ranked_step);
          relation = expanded;

          Bdd new_covered = oxidd_run_or(run, covered_x, inner->arr[l]);
          oxidd_bdd_unref(covered_x);
          covered_x = new_covered;
          if (bdd_invalid(relation) || bdd_invalid(covered_x))
            ok = false;
        }
        oxidd_bdd_unref(covered_x);
        oxidd_bdd_unref(selected);
        Bdd more_goals = oxidd_run_or(run, earlier_goal, outer->y[j]);
        oxidd_bdd_unref(earlier_goal);
        earlier_goal = more_goals;
        if (bdd_invalid(earlier_goal))
          ok = false;
      }
      oxidd_bdd_unref(earlier_goal);
      oxidd_bdd_unref(outer_layer);
      oxidd_bdd_unref(lower_z);
    }
    move[i] = relation;
  }

  if (ok) {
    Bdd any = oxidd_bdd_false(manager);
    for (uint32_t i = 0; i < fairness; i++) {
      phase[i] = oxidd_bdd_false(manager);
      Bdd more = oxidd_run_or(run, any, counter[i]);
      oxidd_bdd_unref(any);
      any = more;
    }
    Bdd none = oxidd_run_not(run, any);
    effective[0] = oxidd_run_or(run, counter[0], none);
    oxidd_bdd_unref(none);
    for (uint32_t i = 1; i < fairness; i++)
      effective[i] = oxidd_bdd_ref(counter[i]);
    oxidd_bdd_unref(any);

    for (uint32_t i = 0; i < fairness && ok; i++) {
      uint32_t next = (i + 1) % fairness;
      Bdd fair =
          fair_bdd ? oxidd_bdd_ref(fair_bdd[i]) : oxidd_bdd_true(manager);
      Bdd advance = oxidd_run_and(run, effective[i], fair);
      Bdd not_fair = oxidd_run_not(run, fair);
      Bdd stay = oxidd_run_and(run, effective[i], not_fair);
      oxidd_bdd_unref(fair);
      oxidd_bdd_unref(not_fair);
      Bdd new_stay = oxidd_run_or(run, phase[i], stay);
      oxidd_bdd_unref(phase[i]);
      oxidd_bdd_unref(stay);
      phase[i] = new_stay;
      Bdd new_advance = oxidd_run_or(run, phase[next], advance);
      oxidd_bdd_unref(phase[next]);
      oxidd_bdd_unref(advance);
      phase[next] = new_advance;
      if (bdd_invalid(phase[i]) || bdd_invalid(phase[next]))
        ok = false;
    }
  }

  Bdd total = oxidd_bdd_false(manager);
  if (ok) {
    for (uint32_t i = 0; i < fairness; i++) {
      next_counter[i] = oxidd_bdd_ref(phase[i]);
      Bdd active = oxidd_run_and(run, phase[i], move[i]);
      Bdd expanded = oxidd_run_or(run, total, active);
      oxidd_bdd_unref(total);
      oxidd_bdd_unref(active);
      total = expanded;
      if (bdd_invalid(total)) {
        ok = false;
        break;
      }
    }
  }

  if (ok) {
    Bdd relation = oxidd_run_forall(run, total, ctrl_cube);
    for (uint32_t i = 0; i < nuv && ok; i++) {
      run->index = i;
      Bdd positive = oxidd_run_var(run, uvars[i]);
      Bdd with_one = oxidd_run_restrict(run, relation, positive);
      Bdd remaining = oxidd_run_cube(run, uvars + i + 1, nuv - i - 1);
      Bdd choice = oxidd_run_exists(run, with_one, remaining);
      oxidd_bdd_unref(positive);
      oxidd_bdd_unref(with_one);
      oxidd_bdd_unref(remaining);
      if (bdd_invalid(choice)) {
        oxidd_bdd_unref(choice);
        ok = false;
        break;
      }
      strategy[i] = choice;
      oxidd_bdd_substitution_t *sub = oxidd_bdd_substitution_new(1);
      if (!sub) {
        ok = false;
        break;
      }
      oxidd_bdd_substitution_add_pair(sub, uvars[i], choice);
      Bdd next_relation = oxidd_run_substitute(run, relation, sub);
      oxidd_bdd_substitution_free(sub);
      oxidd_bdd_unref(relation);
      relation = next_relation;
      if (bdd_invalid(relation))
        ok = false;
    }
    oxidd_bdd_unref(relation);
  }
  oxidd_bdd_unref(total);
  for (uint32_t i = 0; i < fairness; i++) {
    oxidd_bdd_unref(phase[i]);
    oxidd_bdd_unref(effective[i]);
  }
  free(phase);
  free(effective);

  if (!ok) {
    for (uint32_t i = 0; i < fairness; i++) {
      oxidd_bdd_unref(move[i]);
      oxidd_bdd_unref(next_counter[i]);
    }
    for (uint32_t i = 0; i < nuv; i++)
      oxidd_bdd_unref(strategy[i]);
    free(move);
    free(strategy);
    free(next_counter);
    return false;
  }
  *move_out = move;
  *strategy_out = strategy;
  *next_counter_out = next_counter;
  return true;
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

static Aig *solve_gr1_oxidd_impl(Aig *game, int *unreal,
                                 const OxiddSolveOptions *user_opts,
                                 Gr1CertificateOptions *certificate) {
  OxiddSolveOptions defaults = oxidd_solve_options_default();
  const OxiddSolveOptions *opts = user_opts ? user_opts : &defaults;
  if (opts->failure)
    *opts->failure = (OxiddFailure){0};
  if (!unreal) {
    oxidd_record_failure(opts, OXIDD_FAILURE_INVALID, "configuration",
                         "null_verdict_output", 0, 0);
    aig_free(game);
    return nullptr;
  }
  *unreal = 0;
  if (!game)
    return nullptr;
  if (opts->demand_transitions || opts->realizability_only) {
    oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "configuration",
                         "safety_only_option", 0, 0);
    aig_free(game);
    return nullptr;
  }

  bool want_certificate =
      certificate && (certificate->aag_path || certificate->aag_bytes);
  bool want_certificate_json =
      want_certificate && (certificate->json_path || certificate->json_bytes);
  bool want_policy = certificate && (certificate->policy_aag_path ||
                                     certificate->policy_aag_bytes);
  if (certificate) {
    certificate->failed = false;
    certificate->error[0] = '\0';
    if ((certificate->aag_bytes && !certificate->aag_size) ||
        (certificate->json_bytes && !certificate->json_size) ||
        (certificate->policy_aag_bytes && !certificate->policy_aag_size) ||
        (certificate->policy_json_bytes && !certificate->policy_json_size) ||
        (want_policy && !certificate->policy_json_path &&
         !certificate->policy_json_bytes)) {
      certificate_error(certificate, "invalid in-memory export buffers",
                        nullptr);
      oxidd_record_failure(opts, OXIDD_FAILURE_INVALID, "configuration",
                           "export_buffers", 0, 0);
      aig_free(game);
      return nullptr;
    }
  }

  uint32_t original_nlat = aig_num_latches(game);
  aig_sample_input_dependent_acceptance(game);

  uint32_t m_goal_records = aig_num_justice(game);
  uint32_t m_fair = aig_num_fairness(game);

  // An AIGER justice property is a set of literals that must each recur.
  // Flatten each non-empty record into GR(1) system goals.  Preserve an empty
  // record as one vacuous (true) goal so the record remains semantically inert.
  uint32_t m_goals = 0;
  for (uint32_t r = 0; r < m_goal_records; r++) {
    uint32_t n;
    aig_justice_at(game, r, nullptr, &n);
    m_goals += n ? n : 1;
  }

  // A GR(1) game must have at least one justice goal.  If none, the game is
  // pure safety and should go through solve_safety_oxidd instead.
  if (m_goal_records == 0) {
    aig_free(game);
    return nullptr;
  }

  uint32_t nin = aig_num_inputs(game);
  uint32_t nlat = aig_num_latches(game);
  uint32_t nand = aig_num_ands(game);
  uint32_t n_fair_disj = m_fair ? m_fair : 1;

  // Highest AIG variable index, to size the literal -> BDD map.
  uint32_t maxvar = oxidd_max_aig_var(game);

  // Allocations.
  // BDD var layout: 0..nin-1 = inputs, nin..nin+nlat-1 = latches,
  //                 nin+nlat..nin+nlat+m_goals-1 = goal counter curr[j].
  uint32_t auxiliary_vars = m_goals;
  if ((want_certificate || want_policy) && n_fair_disj > auxiliary_vars)
    auxiliary_vars = n_fair_disj;
  uint32_t nvars = nin + nlat + auxiliary_vars;

  // Manager: reuse session manager when active; otherwise right-size a fresh
  // one.
  bool own_mgr = (oxidd_session_get()._p == NULL);
  oxidd_bdd_manager_t m;
  uint32_t var_base;
  size_t node_cap = 0, cache_cap = 0;
  OxiddResolvedOrder order = {0};
  if (own_mgr) {
    if (!oxidd_resolve_var_order(game, opts, auxiliary_vars, &order)) {
      aig_free(game);
      return nullptr;
    }
    size_t default_cap = oxidd_default_capacity(nvars, 6);
    // Dual extraction retains both fixpoint ranks and universally quantified
    // move relations.  The ordinary 2^22 ceiling is enough for solving but is
    // too tight for the named n=7 export regression.
    if ((want_certificate || want_policy) && default_cap < (size_t)1 << 23)
      default_cap = (size_t)1 << 23;
    node_cap = opts->node_cap ? opts->node_cap : default_cap;
    cache_cap = opts->cache_cap ? opts->cache_cap : default_cap;
    oxidd_trace(opts, "manager_create", "begin",
                ",\"node_cap\":%zu,\"cache_cap\":%zu,\"vars\":%u", node_cap,
                cache_cap, nvars);
    m = oxidd_bdd_manager_new(node_cap, cache_cap, 1);
    oxidd_bdd_manager_add_vars(m, nvars);
    var_base = 0;
    if (!oxidd_apply_var_order(m, var_base, opts, &order)) {
      oxidd_resolved_order_free(&order);
      oxidd_bdd_manager_unref(m);
      aig_free(game);
      return nullptr;
    }
    oxidd_resolved_order_free(&order);
  } else {
    if (!oxidd_var_order_is_default(opts)) {
      oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "manager_create",
                           "session_nondefault_order", 0, 0);
      aig_free(game);
      return nullptr;
    }
    m = oxidd_session_get();
    if (!oxidd_session_config(opts, &node_cap, &cache_cap)) {
      oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "manager_create",
                           "session_capacity_mismatch", 0, 0);
      oxidd_trace(opts, "manager_create", "failure",
                  ",\"reason\":\"session_capacity_mismatch\"");
      aig_free(game);
      return nullptr;
    }
    var_base = oxidd_session_alloc_vars(nvars);
  }

  if (var_base == UINT32_MAX) {
    aig_free(game);
    return nullptr;
  }
  OxiddRun run_state;
  OxiddRun *run = &run_state;
  oxidd_run_init(run, m, opts, node_cap, cache_cap);
  Aig *strat = nullptr;
  Bdd *var_bdd = calloc(maxvar + 1, sizeof *var_bdd);
  Bdd *next_bdd = nlat ? calloc(nlat, sizeof *next_bdd) : nullptr;
  Bdd *goal_bdd = m_goals ? calloc(m_goals, sizeof *goal_bdd) : nullptr;
  uint32_t *goal_record =
      want_certificate_json ? calloc(m_goals, sizeof *goal_record) : nullptr;
  uint32_t *goal_member =
      want_certificate_json ? calloc(m_goals, sizeof *goal_member) : nullptr;
  Bdd *fair_bdd = m_fair ? calloc(m_fair, sizeof *fair_bdd) : nullptr;
  Bdd *curr_bdd =
      auxiliary_vars ? calloc(auxiliary_vars, sizeof *curr_bdd) : nullptr;
  uint32_t *var2lit = calloc(nvars, sizeof *var2lit);
  uint32_t *lat_lit = nlat ? calloc(nlat, sizeof *lat_lit) : nullptr;
  uint32_t *curr_latch_lit =
      auxiliary_vars ? calloc(auxiliary_vars, sizeof *curr_latch_lit) : nullptr;
  uint32_t *cvars = nin ? calloc(nin, sizeof *cvars) : nullptr;
  uint32_t *uvars = nin ? calloc(nin, sizeof *uvars) : nullptr;
  uint32_t *cinput = nin ? calloc(nin, sizeof *cinput) : nullptr;
  uint32_t *uinput = nin ? calloc(nin, sizeof *uinput) : nullptr;
  Bdd *strat_f = nullptr;
  BddVec *y_levels = m_goals ? calloc(m_goals, sizeof *y_levels) : nullptr;
  BddVec *x_levels =
      m_goals ? calloc(m_goals * n_fair_disj, sizeof *x_levels) : nullptr;
  Bdd *move_bdd =
      want_certificate && m_goals ? calloc(m_goals, sizeof *move_bdd) : nullptr;

  if (!var_bdd || (nlat && !next_bdd) || !goal_bdd || (m_fair && !fair_bdd) ||
      (want_certificate_json && (!goal_record || !goal_member)) || !curr_bdd ||
      !var2lit || (nlat && !lat_lit) || !curr_latch_lit ||
      (nin && (!cvars || !uvars || !cinput || !uinput)) || !y_levels ||
      !x_levels || (want_certificate && !move_bdd)) {
    oxidd_record_failure(opts, OXIDD_FAILURE_HOST, "construction", "calloc", 0,
                         0);
    free(var_bdd);
    free(next_bdd);
    free(goal_bdd);
    free(goal_record);
    free(goal_member);
    free(fair_bdd);
    free(curr_bdd);
    free(var2lit);
    free(lat_lit);
    free(curr_latch_lit);
    free(cvars);
    free(uvars);
    free(cinput);
    free(uinput);
    free(y_levels);
    free(x_levels);
    free(move_bdd);
    if (own_mgr)
      oxidd_bdd_manager_unref(m);
    aig_free(game);
    return nullptr;
  }
  oxidd_trace(opts, "input", "game",
              ",\"inputs\":%u,\"latches\":%u,\"ands\":%u,"
              "\"outputs\":%u,\"justice\":%u,\"fairness\":%u",
              nin, nlat, nand, aig_num_outputs(game), m_goals, m_fair);

  Bdd bad = {0}, notbad = {0}, W = {0}, ctrl_cube = {0}, unc_cube = {0};
  Bdd L = {0};
  DualVec dual_levels = {0};
  Bdd *environment_move = nullptr;
  Bdd *environment_strategy = nullptr;
  Bdd *environment_next_counter = nullptr;
  oxidd_bdd_substitution_t *sub_lat = nullptr;
  uint32_t ncv = 0, nuv = 0;
  bool ok = true;

  // Variables: input p -> bdd var (var_base+p); latch j -> bdd var
  // (var_base+nin+j);
  //            goal counter j -> bdd var (var_base+nin+nlat+j).
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *name = aig_input_name(game, p, &lit);
    var_bdd[lit / 2] = oxidd_run_var(run, var_base + p);
    if (is_controllable(name)) {
      cvars[ncv] = var_base + p;
      cinput[ncv] = p;
      ncv++;
    } else {
      uvars[nuv] = var_base + p;
      uinput[nuv++] = p;
    }
  }
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, nullptr);
    var_bdd[cur / 2] = oxidd_run_var(run, var_base + nin + j);
  }
  for (uint32_t j = 0; j < auxiliary_vars; j++)
    curr_bdd[j] = oxidd_run_var(run, var_base + nin + nlat + j);

  oxidd_phase(run, "construction");
  ok = build_gr1_roots(run, game, var_bdd, maxvar, m_goals, &bad, next_bdd,
                       goal_bdd, fair_bdd);
  if (ok) {
    notbad = oxidd_run_not(run, bad);
    ok = !bdd_invalid(notbad);
  }

  if (ok && want_certificate_json) {
    uint32_t goal_idx = 0;
    for (uint32_t r = 0; r < m_goal_records; r++) {
      uint32_t n;
      aig_justice_at(game, r, nullptr, &n);
      uint32_t members = n ? n : 1;
      for (uint32_t k = 0; k < members; k++) {
        goal_record[goal_idx] = r;
        goal_member[goal_idx++] = k;
      }
    }
  }
  // Fairness BDDs.  Each assumption gets its own inner ν-fixpoint below;
  // combining their negations would allow the environment to alternate which
  // assumption is false while still satisfying every assumption infinitely.
  for (uint32_t i = 0; i < m_fair && ok; i++) {
    if (bdd_invalid(fair_bdd[i])) {
      ok = false;
      break;
    }
  }

  // Latch substitution s_j := next_j (used in cpre and W-substitution).
  if (ok) {
    sub_lat = oxidd_bdd_substitution_new(nlat);
    if (!sub_lat) {
      ok = false;
    } else {
      for (uint32_t j = 0; j < nlat; j++)
        oxidd_bdd_substitution_add_pair(sub_lat, var_base + nin + j,
                                        next_bdd[j]);
      ctrl_cube = oxidd_run_cube(run, cvars, ncv);
      unc_cube = oxidd_run_cube(run, uvars, nuv);
      if (bdd_invalid(ctrl_cube) || bdd_invalid(unc_cube))
        ok = false;
    }
  }
  if (ok) {
    oxidd_release_var_map(var_bdd, maxvar);
    free(var_bdd);
    var_bdd = nullptr;
    oxidd_phase(run, "root_release");
  }

  // -----------------------------------------------------------------------
  // PPS GR(1) fixpoint
  //   W* = νZ. ⋀_j [ μY. ⋃_i νX.
  //                         cpre( (Z∩goal_j) ∪ Y ∪ (X∩¬fair_i) ) ]
  //
  // Y_levels[j][k] and X_levels[j,i][k] retain the final outer iteration for
  // strategy extraction.  With no fairness assumptions there is one disjunct
  // whose ¬fair term is false.
  // -----------------------------------------------------------------------

  if (ok) {
    oxidd_phase(run, "fixpoint");
    W = oxidd_bdd_true(m); // outer ν starts at ⊤

    for (;;) { // outer ν-fixpoint over W (= Z)
      Bdd W_prev = oxidd_bdd_ref(W);
      Bdd W_new = oxidd_bdd_true(m); // ⋀_j Win_j

      for (uint32_t j = 0; j < m_goals && ok; j++) {
        bddvec_free_all(&y_levels[j]); // reset levels for this outer iteration
        for (uint32_t i = 0; i < n_fair_disj; i++)
          bddvec_free_all(&x_levels[j * n_fair_disj + i]);

        Bdd Y = oxidd_bdd_false(m); // μ-fixpoint from ⊥

        for (;;) { // μ-fixpoint over Y
          Bdd Y_new = oxidd_bdd_false(m);

          for (uint32_t i = 0; i < n_fair_disj && ok; i++) {
            Bdd not_fair_i =
                m_fair ? oxidd_run_not(run, fair_bdd[i]) : oxidd_bdd_false(m);
            if (bdd_invalid(not_fair_i)) {
              ok = false;
              break;
            }
            Bdd X = oxidd_bdd_true(m); // inner ν-fixpoint from ⊤

            for (;;) { // inner ν-fixpoint over X for fairness i
              run->index++;
              Bdd wg = oxidd_run_and(run, W, goal_bdd[j]);
              Bdd wgy = oxidd_run_or(run, wg, Y);
              Bdd xnf = oxidd_run_and(run, X, not_fair_i);
              Bdd target = oxidd_run_or(run, wgy, xnf);
              oxidd_bdd_unref(wg);
              oxidd_bdd_unref(wgy);
              oxidd_bdd_unref(xnf);

              Bdd X_new =
                  cpre_full(run, target, sub_lat, notbad, ctrl_cube, unc_cube);
              oxidd_bdd_unref(target);

              if (bdd_invalid(X_new)) {
                oxidd_bdd_unref(X);
                ok = false;
                break;
              }
              bool inner_conv = bdd_eq(X_new, X);
              oxidd_bdd_unref(X);
              X = X_new;
              if (inner_conv)
                break;
            }
            oxidd_bdd_unref(not_fair_i);
            if (!ok)
              break;

            if (!bddvec_push_ref(run, &x_levels[j * n_fair_disj + i], X)) {
              oxidd_bdd_unref(X);
              ok = false;
              break;
            }
            Bdd tmp = oxidd_run_or(run, Y_new, X);
            oxidd_bdd_unref(Y_new);
            oxidd_bdd_unref(X);
            Y_new = tmp;
            if (bdd_invalid(Y_new))
              ok = false;
          }
          if (!ok)
            oxidd_bdd_unref(Y_new);
          if (!ok)
            break;

          // Save this μ-level and check μ-convergence.
          bool mu_conv = bdd_eq(Y_new, Y);
          if (!bddvec_push_ref(run, &y_levels[j], Y_new)) {
            oxidd_bdd_unref(Y_new);
            ok = false;
            break;
          }
          oxidd_bdd_unref(Y);
          Y = Y_new; // Y holds the ref (bddvec holds an extra ref)
          if (mu_conv)
            break;
        }
        if (!ok) {
          oxidd_bdd_unref(Y);
          break;
        }

        // Win_j = Y (converged μ); W_new ∧= Win_j.
        Bdd tmp = oxidd_run_and(run, W_new, Y);
        oxidd_bdd_unref(W_new);
        oxidd_bdd_unref(Y);
        W_new = tmp;
        if (bdd_invalid(W_new)) {
          ok = false;
          break;
        }
      }

      bool outer_conv = ok && bdd_eq(W_new, W_prev);
      oxidd_bdd_unref(W);
      oxidd_bdd_unref(W_prev);
      W = W_new;
      if (outer_conv || !ok)
        break;
      oxidd_pressure_gc_checkpoint(run);
    }
  }

  // Bdd W is now W* (or invalid if !ok).

  // -----------------------------------------------------------------------
  // Realizability: W* must hold at latch reset cube.
  // -----------------------------------------------------------------------

  if (ok) {
    oxidd_var_no_bool_pair_t *args =
        nlat ? calloc(nlat, sizeof *args) : nullptr;
    if (nlat && !args)
      ok = false;
    for (uint32_t j = 0; j < nlat && ok; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      if (reset != 0 && reset != 1) {
        ok = false;
        break;
      }
      args[j].var = var_base + nin + j;
      args[j].val = reset != 0;
    }
    bool realizable = ok && oxidd_bdd_eval(W, args, nlat);
    free(args);
    if (ok && !realizable) {
      *unreal = 1;
      if (certificate &&
          certificate->semantics == GR1_CERTIFICATE_SEMANTICS_STRICT &&
          (want_certificate || want_policy)) {
        certificate_error(
            certificate,
            "refusing UNREAL certificate/policy from strict semantics",
            nullptr);
        ok = false;
      } else if (!want_certificate && !want_policy) {
        ok = false;
      }
    }
  }

  if (ok && *unreal) {
    oxidd_phase(run, "dual_fixpoint");
    ok = compute_dual_fixpoint(run, m_goals, n_fair_disj, goal_bdd,
                               m_fair ? fair_bdd : nullptr, sub_lat, bad,
                               ctrl_cube, unc_cube, &dual_levels, &L);
    if (ok) {
      oxidd_var_no_bool_pair_t *args =
          nlat ? calloc(nlat, sizeof *args) : nullptr;
      if (nlat && !args) {
        ok = false;
      } else {
        for (uint32_t j = 0; j < nlat; j++) {
          uint32_t reset;
          aig_latch_at(game, j, nullptr, nullptr, &reset);
          args[j].var = var_base + nin + j;
          args[j].val = reset != 0;
        }
        if (!oxidd_bdd_eval(L, args, nlat)) {
          oxidd_record_failure(opts, OXIDD_FAILURE_INVALID, "dual_fixpoint",
                               "reset_not_environment_winning", run->operations,
                               run->index);
          ok = false;
        }
        free(args);
      }
    }
    if (ok) {
      oxidd_phase(run, "dual_strategy_relation");
      ok = extract_environment_counterstrategy(
          run, m_goals, n_fair_disj, goal_bdd, m_fair ? fair_bdd : nullptr,
          &dual_levels, curr_bdd, sub_lat, bad, ctrl_cube, uvars, nuv,
          &environment_move, &environment_strategy, &environment_next_counter);
    }
    if (!ok && certificate && !certificate->failed)
      certificate_error(certificate,
                        "environment counter-strategy construction failed",
                        nullptr);
  }

  // -----------------------------------------------------------------------
  // Strategy extraction
  //
  // Build M_total(s, curr[], u, c) as follows:
  //
  //   For each goal j:
  //     at_goal_j = W* ∩ goal_bdd[j]
  //     M_j = (s ∈ at_goal_j) ∧ cpre_c(W*)              // advance: any safe
  //     move
  //         ∪ (s ∈ level_j_0 \ at_goal_j) ∧ cpre_c(at_goal_j)
  //         ∪ (s ∈ level_j_k \ level_j_{k-1} \ at_goal_j) ∧ cpre_c(Y_{k-1} ∪
  //         at_goal_j)
  //         ...
  //
  //   M_total = ⋃_j [curr_bdd[j] ∧ M_j]
  //
  // Then Skolem-extract f_k(s, curr[], u) from M_total for each controllable.
  // -----------------------------------------------------------------------

  if (ok && !*unreal) {
    strat_f = ncv ? calloc(ncv, sizeof *strat_f) : nullptr;
    if (ncv && !strat_f)
      ok = false;
  }

  // Goal-counter next-functions and strategy move predicate both use
  // "effective_curr[j]": when all curr bits are 0 (initial state, all reset to
  // 0), treat it as curr[0]=1.  This avoids the AIGER reset=1 latch line that
  // Spot's parser does not accept.
  //
  //   any_curr = ⋃_j curr[j]
  //   effective_curr[j] = curr[j]       (j > 0)
  //                     = curr[0] ∨ ¬any_curr   (j = 0)
  //
  // After step 1 at least one curr latch becomes 1 (proved by case analysis),
  // so the one-hot property is maintained from step 1 onwards.
  Bdd *eff_curr = nullptr;
  if (ok && !*unreal) {
    eff_curr = calloc(m_goals, sizeof *eff_curr);
    if (!eff_curr) {
      ok = false;
    } else {
      Bdd any_curr = oxidd_bdd_false(m);
      for (uint32_t j = 0; j < m_goals && ok; j++) {
        Bdd tmp = oxidd_run_or(run, any_curr, curr_bdd[j]);
        oxidd_bdd_unref(any_curr);
        any_curr = tmp;
        if (bdd_invalid(any_curr))
          ok = false;
      }
      if (ok) {
        Bdd not_any = oxidd_run_not(run, any_curr);
        eff_curr[0] = oxidd_run_or(run, curr_bdd[0], not_any);
        oxidd_bdd_unref(not_any);
        for (uint32_t j = 1; j < m_goals; j++)
          eff_curr[j] = oxidd_bdd_ref(curr_bdd[j]);
        if (bdd_invalid(eff_curr[0]))
          ok = false;
      }
      oxidd_bdd_unref(any_curr);
    }
  }

  if (ok && !*unreal) {
    // W_star image for "any safe move" = cpre_c(W*).
    oxidd_phase(run, "strategy_relation");
    Bdd w_safe = cpre_unquantified(run, W, sub_lat, notbad);

    // Build M_total = ⋃_j [eff_curr[j] ∧ M_j].
    Bdd M_total = oxidd_bdd_false(m);

    for (uint32_t j = 0; j < m_goals && ok; j++) {
      Bdd at_goal = oxidd_run_and(run, W, goal_bdd[j]);

      // case_at_goal = at_goal ∧ w_safe
      Bdd case_at_goal = oxidd_run_and(run, at_goal, w_safe);
      Bdd M_j = oxidd_bdd_ref(case_at_goal);
      oxidd_bdd_unref(case_at_goal);

      // covered = at_goal (states already handled by the at-goal case)
      Bdd covered = oxidd_bdd_ref(at_goal);

      for (uint32_t k = 0; k < y_levels[j].n && ok; k++) {
        // Strict progress goes to the goal or a lower μ-rank.  Within the
        // least rank, choose the least fairness index whose X[k,i] contains
        // the state; only that fixed assumption may justify staying in X.
        Bdd strict = k == 0
                         ? oxidd_bdd_ref(at_goal)
                         : oxidd_run_or(run, y_levels[j].arr[k - 1], at_goal);

        for (uint32_t i = 0; i < n_fair_disj && ok; i++) {
          Bdd xki = x_levels[j * n_fair_disj + i].arr[k];
          Bdd ncover = oxidd_run_not(run, covered);
          Bdd layer = oxidd_run_and(run, xki, ncover);
          oxidd_bdd_unref(ncover);

          Bdd not_fair_i =
              m_fair ? oxidd_run_not(run, fair_bdd[i]) : oxidd_bdd_false(m);
          Bdd escape = oxidd_run_and(run, not_fair_i, xki);
          Bdd target = oxidd_run_or(run, strict, escape);
          oxidd_bdd_unref(not_fair_i);
          oxidd_bdd_unref(escape);
          if (bdd_invalid(target)) {
            oxidd_bdd_unref(layer);
            ok = false;
            break;
          }

          Bdd move_ki = cpre_unquantified(run, target, sub_lat, notbad);
          oxidd_bdd_unref(target);
          Bdd case_ki = oxidd_run_and(run, layer, move_ki);
          oxidd_bdd_unref(layer);
          oxidd_bdd_unref(move_ki);

          Bdd new_mj = oxidd_run_or(run, M_j, case_ki);
          oxidd_bdd_unref(M_j);
          oxidd_bdd_unref(case_ki);
          M_j = new_mj;

          Bdd new_cov = oxidd_run_or(run, covered, xki);
          oxidd_bdd_unref(covered);
          covered = new_cov;
          if (bdd_invalid(M_j) || bdd_invalid(covered))
            ok = false;
        }
        oxidd_bdd_unref(strict);
      }

      oxidd_bdd_unref(covered);
      oxidd_bdd_unref(at_goal);

      if (ok) {
        if (want_certificate)
          move_bdd[j] = oxidd_bdd_ref(M_j);
        // M_total |= eff_curr[j] ∧ M_j
        Bdd piece = oxidd_run_and(run, eff_curr[j], M_j);
        oxidd_bdd_unref(M_j);
        Bdd new_total = oxidd_run_or(run, M_total, piece);
        oxidd_bdd_unref(M_total);
        oxidd_bdd_unref(piece);
        M_total = new_total;
        if (bdd_invalid(M_total))
          ok = false;
      } else {
        oxidd_bdd_unref(M_j);
      }
    }
    oxidd_bdd_unref(w_safe);
    oxidd_bdd_substitution_free(sub_lat);
    sub_lat = nullptr;
    oxidd_bdd_unref(notbad);
    notbad = (Bdd){0};
    oxidd_bdd_unref(ctrl_cube);
    ctrl_cube = (Bdd){0};
    oxidd_bdd_unref(unc_cube);
    unc_cube = (Bdd){0};
    if (!want_certificate)
      for (uint32_t j = 0; j < m_goals; j++)
        bddvec_free_all(&y_levels[j]);

    // Skolem: f_k(s, curr[], u) = ∃(c_{k+1}...) M_total|_{c_k=1}
    if (ok) {
      oxidd_phase(run, "skolem");
      Bdd R = M_total;
      M_total = (Bdd){0};
      for (uint32_t k = 0; k < ncv && ok; k++) {
        run->index = k;
        Bdd pos = oxidd_run_var(run, cvars[k]);
        Bdd rk1 = oxidd_run_restrict(run, R, pos);
        Bdd rem = oxidd_run_cube(run, cvars + k + 1, ncv - k - 1);
        Bdd fk = oxidd_run_exists(run, rk1, rem);
        oxidd_bdd_unref(pos);
        oxidd_bdd_unref(rk1);
        oxidd_bdd_unref(rem);
        if (bdd_invalid(fk)) {
          oxidd_bdd_unref(fk);
          ok = false;
          break;
        }
        strat_f[k] = fk;
        oxidd_bdd_substitution_t *s1 = oxidd_bdd_substitution_new(1);
        if (!s1) {
          ok = false;
          break;
        }
        oxidd_bdd_substitution_add_pair(s1, cvars[k], fk);
        Bdd rnew = oxidd_run_substitute(run, R, s1);
        oxidd_bdd_substitution_free(s1);
        oxidd_bdd_unref(R);
        R = rnew;
        if (bdd_invalid(R))
          ok = false;
      }
      oxidd_bdd_unref(R);
    }
    oxidd_bdd_unref(M_total);
  }

  // Goal-counter next-functions: next_curr[j] = (eff_curr[j] ∧ ¬advance_j)
  //                                           ∨ (eff_curr[prev] ∧ advance_prev)
  // where advance_j = eff_curr[j] ∧ (W* ∩ goal_j).
  Bdd *next_curr = nullptr;
  if (ok && !*unreal) {
    next_curr = m_goals ? calloc(m_goals, sizeof *next_curr) : nullptr;
    if (!next_curr) {
      ok = false;
    } else {
      Bdd *adv = calloc(m_goals, sizeof *adv);
      if (!adv) {
        ok = false;
      } else {
        for (uint32_t j = 0; j < m_goals && ok; j++) {
          Bdd wg = oxidd_run_and(run, W, goal_bdd[j]);
          adv[j] = oxidd_run_and(run, eff_curr[j], wg);
          oxidd_bdd_unref(wg);
          if (bdd_invalid(adv[j]))
            ok = false;
        }
        if (ok) {
          for (uint32_t j = 0; j < m_goals && ok; j++) {
            uint32_t prev = (j + m_goals - 1) % m_goals;
            Bdd not_adv = oxidd_run_not(run, adv[j]);
            Bdd stay = oxidd_run_and(run, eff_curr[j], not_adv);
            Bdd come = oxidd_run_and(run, eff_curr[prev], adv[prev]);
            Bdd nxt = oxidd_run_or(run, stay, come);
            oxidd_bdd_unref(not_adv);
            oxidd_bdd_unref(stay);
            oxidd_bdd_unref(come);
            next_curr[j] = nxt;
            if (bdd_invalid(nxt))
              ok = false;
          }
        }
        for (uint32_t j = 0; j < m_goals; j++)
          oxidd_bdd_unref(adv[j]);
        free(adv);
      }
    }
  }

  // -----------------------------------------------------------------------
  // Build the strategy AIG.
  // -----------------------------------------------------------------------

  if (ok && !*unreal) {
    oxidd_phase(run, "conversion");
    strat = aig_new();
    for (uint32_t v = 0; v < nvars; v++)
      var2lit[v] = UINT32_MAX;

    // Uncontrollable inputs.
    for (uint32_t p = 0; p < nin; p++) {
      uint32_t lit;
      const char *name = aig_input_name(game, p, &lit);
      if (!is_controllable(name))
        var2lit[p] = aig_input(
            strat, oxidd_input_name_or_synthetic(name, p, (char[32]){0}));
    }

    // Game latches (same reset values, next wired below).
    for (uint32_t j = 0; j < nlat; j++) {
      uint32_t reset;
      aig_latch_at(game, j, nullptr, nullptr, &reset);
      lat_lit[j] = aig_latch(strat, AIG_FALSE, reset);
      var2lit[nin + j] = lat_lit[j];
    }

    // Goal-counter latches: all reset to 0; eff_curr[0] handles initial state.
    for (uint32_t j = 0; j < m_goals; j++) {
      curr_latch_lit[j] = aig_latch(strat, AIG_FALSE, 0u);
      var2lit[nin + nlat + j] = curr_latch_lit[j];
    }

    // Controllable outputs f_k.
    bool convert_error = false;
    for (uint32_t k = 0; k < ncv; k++) {
      uint32_t lit;
      const char *name = aig_input_name(game, cinput[k], &lit);
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars, {0}, false, run, 0};
      uint32_t out = bdd2aig_root(&ctx, strat_f[k]);
      convert_error = convert_error || ctx.error;
      aig_set_output(strat, name, out);
    }

    // Game latch next-functions (Skolem substitution applied).
    oxidd_bdd_substitution_t *sc =
        ncv ? oxidd_bdd_substitution_new(ncv) : nullptr;
    if (ncv && !sc)
      convert_error = true;
    for (uint32_t k = 0; k < ncv && !convert_error; k++)
      oxidd_bdd_substitution_add_pair(sc, cvars[k], strat_f[k]);
    for (uint32_t j = 0; j < nlat && !convert_error; j++) {
      run->index = j;
      Bdd na = ncv ? oxidd_run_substitute(run, next_bdd[j], sc)
                   : oxidd_bdd_ref(next_bdd[j]);
      if (bdd_invalid(na)) {
        oxidd_bdd_unref(na);
        convert_error = true;
        break;
      }
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars, {0}, false, run, 0};
      uint32_t nl = bdd2aig_root(&ctx, na);
      convert_error = convert_error || ctx.error;
      oxidd_bdd_unref(na);
      aig_set_latch_next(strat, lat_lit[j], nl);
    }
    if (sc)
      oxidd_bdd_substitution_free(sc);

    // Goal-counter latch next-functions.
    for (uint32_t j = 0; j < m_goals && !convert_error; j++) {
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars, {0}, false, run, 0};
      uint32_t nl = bdd2aig_root(&ctx, next_curr[j]);
      convert_error = convert_error || ctx.error;
      aig_set_latch_next(strat, curr_latch_lit[j], nl);
    }

    if (convert_error) {
      if (!run->stopped)
        oxidd_record_failure(opts, OXIDD_FAILURE_CONVERSION, "conversion",
                             "bdd2aig_or_substitution", run->operations,
                             run->index);
      aig_free(strat);
      strat = nullptr;
      ok = false;
    }
  }

  if (ok && oxidd_run_stopped(run))
    ok = false;
  if (ok && want_policy && !*unreal) {
    oxidd_phase(run, "policy");
    if (!export_policy(run, game, certificate, original_nlat, m_goals, nin,
                       nlat, nvars, var_base, cinput, ncv, strat_f,
                       next_curr)) {
      aig_free(strat);
      strat = nullptr;
      ok = false;
    }
  }

  if (ok && want_policy && *unreal) {
    oxidd_phase(run, "environment_policy");
    if (!export_environment_policy(run, game, certificate, original_nlat,
                                   m_goals, n_fair_disj, nin, nlat, nvars,
                                   var_base, uinput, nuv, environment_strategy,
                                   environment_next_counter))
      ok = false;
  }

  if (ok && want_certificate) {
    oxidd_phase(run, "certificate");
    bool exported =
        *unreal ? export_environment_certificate(
                      run, game, certificate, original_nlat, m_goals, m_fair,
                      n_fair_disj, nin, nlat, nvars, var_base, goal_bdd,
                      fair_bdd, &dual_levels, environment_move, L)
                : export_certificate(run, game, certificate, false,
                                     original_nlat, m_goal_records, m_goals,
                                     m_fair, n_fair_disj, nin, nlat, nvars,
                                     var_base, goal_record, goal_member,
                                     goal_bdd, y_levels, x_levels, move_bdd, W);
    if (!exported) {
      aig_free(strat);
      strat = nullptr;
      ok = false;
    }
  }

  if (ok && oxidd_run_stopped(run))
    ok = false;
  size_t artifact_cap = certificate && certificate->max_artifact_bytes
                            ? certificate->max_artifact_bytes
                            : opts->max_artifact_bytes;
  if (ok && artifact_cap && certificate &&
      ((certificate->aag_size && *certificate->aag_size > artifact_cap) ||
       (certificate->json_size && *certificate->json_size > artifact_cap) ||
       (certificate->policy_aag_size &&
        *certificate->policy_aag_size > artifact_cap) ||
       (certificate->policy_json_size &&
        *certificate->policy_json_size > artifact_cap))) {
    certificate_error(certificate, "artifact cap exceeded", nullptr);
    oxidd_record_failure(opts, OXIDD_FAILURE_ARTIFACT_LIMIT, "export",
                         "artifact_cap", run->operations, run->index);
    ok = false;
  }
  if (!ok && *unreal && (want_certificate || want_policy))
    *unreal = 0;
  if (!ok && strat) {
    aig_free(strat);
    strat = nullptr;
  }

  // -----------------------------------------------------------------------
  // Cleanup.
  // -----------------------------------------------------------------------

  if (next_curr) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(next_curr[j]);
    free(next_curr);
  }
  if (environment_move) {
    for (uint32_t i = 0; i < n_fair_disj; i++)
      oxidd_bdd_unref(environment_move[i]);
    free(environment_move);
  }
  if (environment_strategy) {
    for (uint32_t i = 0; i < nuv; i++)
      oxidd_bdd_unref(environment_strategy[i]);
    free(environment_strategy);
  }
  if (environment_next_counter) {
    for (uint32_t i = 0; i < n_fair_disj; i++)
      oxidd_bdd_unref(environment_next_counter[i]);
    free(environment_next_counter);
  }
  dualvec_free_all(&dual_levels, m_goals, n_fair_disj);
  if (strat_f) {
    for (uint32_t k = 0; k < ncv; k++)
      oxidd_bdd_unref(strat_f[k]);
    free(strat_f);
  }
  if (y_levels) {
    for (uint32_t j = 0; j < m_goals; j++)
      bddvec_free_all(&y_levels[j]);
    free(y_levels);
  }
  if (x_levels) {
    for (uint32_t j = 0; j < m_goals; j++)
      for (uint32_t i = 0; i < n_fair_disj; i++)
        bddvec_free_all(&x_levels[j * n_fair_disj + i]);
    free(x_levels);
  }
  if (move_bdd) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(move_bdd[j]);
    free(move_bdd);
  }
  if (goal_bdd) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(goal_bdd[j]);
    free(goal_bdd);
  }
  if (fair_bdd) {
    for (uint32_t i = 0; i < m_fair; i++)
      oxidd_bdd_unref(fair_bdd[i]);
    free(fair_bdd);
  }
  if (curr_bdd) {
    for (uint32_t j = 0; j < auxiliary_vars; j++)
      oxidd_bdd_unref(curr_bdd[j]);
    free(curr_bdd);
  }
  if (eff_curr) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(eff_curr[j]);
    free(eff_curr);
  }
  for (uint32_t j = 0; j < nlat; j++)
    oxidd_bdd_unref(next_bdd[j]);
  oxidd_release_var_map(var_bdd, maxvar);
  oxidd_bdd_unref(bad);
  oxidd_bdd_unref(notbad);
  oxidd_bdd_unref(W);
  oxidd_bdd_unref(L);
  oxidd_bdd_unref(ctrl_cube);
  oxidd_bdd_unref(unc_cube);
  if (sub_lat)
    oxidd_bdd_substitution_free(sub_lat);
  if (!strat && !*unreal && (!certificate || !certificate->failed) &&
      (!opts->failure || opts->failure->kind == OXIDD_FAILURE_NONE))
    oxidd_record_failure(opts, OXIDD_FAILURE_HOST, run->phase,
                         "host_allocation_or_invalid_input", run->operations,
                         run->index);
  oxidd_run_finish(run);
  if (own_mgr)
    oxidd_bdd_manager_unref(m);
  else
    oxidd_session_gc();

  free(var_bdd);
  free(next_bdd);
  free(goal_record);
  free(goal_member);
  free(var2lit);
  free(lat_lit);
  free(curr_latch_lit);
  free(cvars);
  free(uvars);
  free(cinput);
  free(uinput);
  aig_free(game);
  return strat;
}

typedef struct {
  const char *path;
  const char *bytes;
  size_t size;
  char *temporary, *backup;
  bool published, had_original;
} ExportStage;

static char *nearby_name(const char *path, const char *suffix, int *fd) {
  size_t length = strlen(path) + strlen(suffix) + 7;
  char *name = malloc(length);
  if (!name)
    return nullptr;
  snprintf(name, length, "%s%sXXXXXX", path, suffix);
  *fd = mkstemp(name);
  if (*fd < 0) {
    free(name);
    return nullptr;
  }
  return name;
}

static bool publish_exports(ExportStage files[4]) {
  bool ok = true;
  for (size_t i = 0; i < 4 && ok; i++) {
    if (!files[i].path)
      continue;
    int fd;
    files[i].temporary = nearby_name(files[i].path, ".stage-", &fd);
    if (!files[i].temporary) {
      ok = false;
      break;
    }
    FILE *out = fdopen(fd, "wb");
    if (!out) {
      close(fd);
      ok = false;
      break;
    }
    ok = fwrite(files[i].bytes, 1, files[i].size, out) == files[i].size;
    if (fclose(out) != 0)
      ok = false;
  }
  for (size_t i = 0; i < 4 && ok; i++) {
    if (!files[i].path)
      continue;
    if (access(files[i].path, F_OK) == 0) {
      int fd;
      files[i].backup = nearby_name(files[i].path, ".backup-", &fd);
      if (!files[i].backup) {
        ok = false;
        break;
      }
      close(fd);
      unlink(files[i].backup);
      if (rename(files[i].path, files[i].backup) != 0) {
        ok = false;
        break;
      }
      files[i].had_original = true;
    }
    if (rename(files[i].temporary, files[i].path) != 0) {
      ok = false;
      break;
    }
    files[i].published = true;
  }
  if (!ok)
    for (size_t i = 4; i-- > 0;) {
      if (files[i].published)
        unlink(files[i].path);
      if (files[i].had_original)
        rename(files[i].backup, files[i].path);
    }
  for (size_t i = 0; i < 4; i++) {
    if (files[i].temporary)
      unlink(files[i].temporary);
    if (ok && files[i].backup)
      unlink(files[i].backup);
    free(files[i].temporary);
    free(files[i].backup);
  }
  return ok;
}

static void clear_export_outputs(Gr1CertificateOptions *certificate) {
  if (certificate->aag_bytes)
    *certificate->aag_bytes = nullptr;
  if (certificate->json_bytes)
    *certificate->json_bytes = nullptr;
  if (certificate->policy_aag_bytes)
    *certificate->policy_aag_bytes = nullptr;
  if (certificate->policy_json_bytes)
    *certificate->policy_json_bytes = nullptr;
  if (certificate->aag_size)
    *certificate->aag_size = 0;
  if (certificate->json_size)
    *certificate->json_size = 0;
  if (certificate->policy_aag_size)
    *certificate->policy_aag_size = 0;
  if (certificate->policy_json_size)
    *certificate->policy_json_size = 0;
}

Aig *solve_gr1_oxidd_ex_with_certificate(Aig *game, int *unreal,
                                         const OxiddSolveOptions *options,
                                         Gr1CertificateOptions *certificate) {
  OxiddSolveOptions resolved =
      options ? *options : oxidd_solve_options_default();
  OxiddFailure failure = {0};
  resolved.failure = &failure;
  if (!certificate) {
    Aig *strategy = solve_gr1_oxidd_impl(game, unreal, &resolved, nullptr);
    if (options && options->failure)
      *options->failure = failure;
    return strategy;
  }
  if ((certificate->aag_bytes && !certificate->aag_size) ||
      (certificate->json_bytes && !certificate->json_size) ||
      (certificate->policy_aag_bytes && !certificate->policy_aag_size) ||
      (certificate->policy_json_bytes && !certificate->policy_json_size) ||
      ((certificate->json_path || certificate->json_bytes) &&
       !certificate->aag_path && !certificate->aag_bytes) ||
      ((certificate->policy_json_path || certificate->policy_json_bytes) &&
       !certificate->policy_aag_path && !certificate->policy_aag_bytes) ||
      ((certificate->policy_aag_path || certificate->policy_aag_bytes) &&
       !certificate->policy_json_path && !certificate->policy_json_bytes)) {
    clear_export_outputs(certificate);
    certificate_error(certificate, "invalid in-memory export buffers", nullptr);
    oxidd_record_failure(&resolved, OXIDD_FAILURE_INVALID, "configuration",
                         "export_buffers", 0, 0);
    if (options && options->failure)
      *options->failure = failure;
    if (unreal)
      *unreal = 0;
    aig_free(game);
    return nullptr;
  }
  clear_export_outputs(certificate);
  Gr1CertificateOptions staged = *certificate;
  char *bytes[4] = {0};
  size_t sizes[4] = {0};
  bool requested[4] = {
      certificate->aag_path || certificate->aag_bytes,
      certificate->json_path || certificate->json_bytes,
      certificate->policy_aag_path || certificate->policy_aag_bytes,
      certificate->policy_json_path || certificate->policy_json_bytes,
  };
  staged.aag_bytes = requested[0] ? &bytes[0] : nullptr;
  staged.json_bytes = requested[1] ? &bytes[1] : nullptr;
  staged.policy_aag_bytes = requested[2] ? &bytes[2] : nullptr;
  staged.policy_json_bytes = requested[3] ? &bytes[3] : nullptr;
  staged.aag_size = requested[0] ? &sizes[0] : nullptr;
  staged.json_size = requested[1] ? &sizes[1] : nullptr;
  staged.policy_aag_size = requested[2] ? &sizes[2] : nullptr;
  staged.policy_json_size = requested[3] ? &sizes[3] : nullptr;
  Aig *strategy = solve_gr1_oxidd_impl(game, unreal, &resolved, &staged);
  certificate->failed = staged.failed;
  memcpy(certificate->error, staged.error, sizeof certificate->error);
  bool ok = !staged.failed && failure.kind == OXIDD_FAILURE_NONE &&
            (strategy || (unreal && *unreal));
  for (size_t i = 0; i < 4; i++)
    if (ok && requested[i] && !bytes[i])
      ok = false;
  if (ok) {
    ExportStage files[4] = {
        {.path = certificate->aag_path, .bytes = bytes[0], .size = sizes[0]},
        {.path = certificate->json_path, .bytes = bytes[1], .size = sizes[1]},
        {.path = certificate->policy_aag_path,
         .bytes = bytes[2],
         .size = sizes[2]},
        {.path = certificate->policy_json_path,
         .bytes = bytes[3],
         .size = sizes[3]},
    };
    for (size_t i = 0; i < 4 && ok; i++)
      for (size_t j = 0; j < i; j++)
        if (files[i].path && files[j].path &&
            strcmp(files[i].path, files[j].path) == 0)
          ok = false;
    if (ok)
      ok = publish_exports(files);
    if (!ok) {
      certificate_error(certificate, "cannot publish complete export", nullptr);
      oxidd_record_failure(&resolved, OXIDD_FAILURE_HOST, "export", "publish",
                           0, 0);
    }
  }
  if (ok) {
    char **outputs[4] = {certificate->aag_bytes, certificate->json_bytes,
                         certificate->policy_aag_bytes,
                         certificate->policy_json_bytes};
    size_t *lengths[4] = {certificate->aag_size, certificate->json_size,
                          certificate->policy_aag_size,
                          certificate->policy_json_size};
    for (size_t i = 0; i < 4; i++) {
      if (outputs[i]) {
        *outputs[i] = bytes[i];
        *lengths[i] = sizes[i];
        bytes[i] = nullptr;
      }
    }
  } else {
    if (strategy)
      aig_free(strategy);
    strategy = nullptr;
    if (unreal)
      *unreal = 0;
    clear_export_outputs(certificate);
    certificate->failed = true;
    if (failure.kind == OXIDD_FAILURE_NONE)
      oxidd_record_failure(&resolved, OXIDD_FAILURE_HOST, "export", "staging",
                           0, 0);
  }
  for (size_t i = 0; i < 4; i++)
    free(bytes[i]);
  if (options && options->failure)
    *options->failure = failure;
  return strategy;
}

Aig *solve_gr1_oxidd_ex(Aig *game, int *unreal, const OxiddSolveOptions *opts) {
  return solve_gr1_oxidd_ex_with_certificate(game, unreal, opts, nullptr);
}

static Aig *
solve_gr1_oxidd_with_certificate_internal(Aig *game, int *unreal,
                                          Gr1CertificateOptions *certificate) {
  OxiddSolveOptions opts = oxidd_solve_options_default();
  opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT;
  opts.safety_output_index = 0;
  return solve_gr1_oxidd_ex_with_certificate(game, unreal, &opts, certificate);
}

Aig *solve_gr1_oxidd(Aig *game, int *unreal) {
  return solve_gr1_oxidd_with_certificate_internal(game, unreal, nullptr);
}
