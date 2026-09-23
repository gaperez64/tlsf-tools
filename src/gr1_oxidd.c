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

#include "tlsf/oxidd_common.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// Dynamic array of BDD references (for μ-fixpoint Y-levels)
// ---------------------------------------------------------------------------

typedef struct {
  Bdd *arr;
  uint32_t n, cap;
} BddVec;

static bool bddvec_push_ref(OxiddRun *run, BddVec *v, Bdd b) {
  if (v->n == v->cap) {
    uint32_t nc = v->cap ? v->cap * 2 : 4;
    Bdd *narr = realloc(v->arr, nc * sizeof *narr);
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
  size_t count = 1u + (size_t)nl + m_goals + nf;
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
  if (run->options->safety_output_index >= aig_num_outputs(game)) {
    free(lits);
    free(roots);
    return false;
  }
  aig_output_at(game, run->options->safety_output_index, &lits[k++]);
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
    k = 0;
    *bad = roots[k];
    roots[k++] = (Bdd){0};
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

static const char *input_name_or_synthetic(const char *name, uint32_t index,
                                           char buf[32]) {
  if (name)
    return name;
  snprintf(buf, 32, "i%u", index);
  return buf;
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

static void json_string(FILE *out, const char *value) {
  fputc('"', out);
  for (const unsigned char *p = (const unsigned char *)value; *p; p++) {
    switch (*p) {
    case '"':
      fputs("\\\"", out);
      break;
    case '\\':
      fputs("\\\\", out);
      break;
    case '\b':
      fputs("\\b", out);
      break;
    case '\f':
      fputs("\\f", out);
      break;
    case '\n':
      fputs("\\n", out);
      break;
    case '\r':
      fputs("\\r", out);
      break;
    case '\t':
      fputs("\\t", out);
      break;
    default:
      if (*p < 0x20)
        fprintf(out, "\\u%04x", *p);
      else
        fputc(*p, out);
    }
  }
  fputc('"', out);
}

static void json_predicate(FILE *out, bool *first, const char *name,
                           const char *kind, int goal, int level,
                           int fairness) {
  if (!*first)
    fputs(",\n", out);
  *first = false;
  fputs("    {\"name\": ", out);
  json_string(out, name);
  fputs(", \"kind\": ", out);
  json_string(out, kind);
  if (goal >= 0)
    fprintf(out, ", \"goal\": %d", goal);
  if (level >= 0)
    fprintf(out, ", \"level\": %d", level);
  if (fairness >= 0)
    fprintf(out, ", \"fairness\": %d", fairness);
  fputc('}', out);
}

static bool write_certificate_json(FILE *out, const Aig *certificate,
                                   const Aig *game, const char *aag_path,
                                   bool unreal, uint32_t original_nlat,
                                   uint32_t m_goal_records, uint32_t m_goals,
                                   uint32_t m_fair, uint32_t n_fair_disj,
                                   const uint32_t *goal_record,
                                   const uint32_t *goal_member,
                                   const BddVec *y_levels) {
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

  fputs("{\n  \"format\": \"tlsf-gr1-certificate-v1\",\n", out);
  fputs("  \"status\": ", out);
  json_string(out, unreal ? "unrealizable" : "realizable");
  fputs(",\n  \"circuit\": {\"path\": ", out);
  json_string(out, aag_path);
  fputs(", \"kind\": \"ASCII AIGER combinational\"},\n", out);
  fputs("  \"fixpoint\": ", out);
  json_string(out, "Z = nu Z. AND_j mu Y. OR_i nu X. "
                   "cpre((Z & goal_j) | Y | (X & !fair_i))");
  fputs(",\n  \"counts\": {\n", out);
  fprintf(out,
          "    \"goals\": %u,\n    \"justice_records\": %u,\n"
          "    \"fairness_assumptions\": %u,\n"
          "    \"state_variables\": %u,\n"
          "    \"original_game_latches\": %u,\n"
          "    \"sampling_latches\": %u,\n"
          "    \"uncontrollable_inputs\": %u,\n"
          "    \"controllable_inputs\": %u,\n"
          "    \"predicates\": %u,\n    \"aig_inputs\": %u,\n"
          "    \"aig_latches\": %u,\n    \"aig_ands\": %u,\n"
          "    \"levels_per_goal\": [",
          m_goals, m_goal_records, m_fair, nlat, original_nlat,
          nlat - original_nlat, nu, nc, aig_num_outputs(certificate),
          aig_num_inputs(certificate), aig_num_latches(certificate),
          aig_num_ands(certificate));
  for (uint32_t j = 0; j < m_goals; j++)
    fprintf(out, "%s%u", j ? ", " : "", y_levels[j].n);
  fputs("]\n  },\n", out);

  fputs("  \"outputs\": [\n", out);
  bool first = true;
  json_predicate(out, &first, "inv", "winning_region", -1, -1, -1);
  if (unreal)
    json_predicate(out, &first, "losing", "nonwinning_region", -1, -1, -1);
  char name[96];
  for (uint32_t j = 0; j < m_goals; j++) {
    snprintf(name, sizeof name, "goal_%u", j);
    json_predicate(out, &first, name, "goal", (int)j, -1, -1);
  }
  for (uint32_t j = 0; j < m_goals; j++)
    for (uint32_t k = 0; k < y_levels[j].n; k++) {
      snprintf(name, sizeof name, "y_%u_%u", j, k);
      json_predicate(out, &first, name, "mu_level", (int)j, (int)k, -1);
    }
  for (uint32_t j = 0; j < m_goals; j++)
    for (uint32_t k = 0; k < y_levels[j].n; k++)
      for (uint32_t i = 0; i < n_fair_disj; i++) {
        snprintf(name, sizeof name, "x_%u_%u_%u", j, k, i);
        json_predicate(out, &first, name, "nu_level", (int)j, (int)k, (int)i);
      }
  if (!unreal)
    for (uint32_t j = 0; j < m_goals; j++) {
      snprintf(name, sizeof name, "move_%u", j);
      json_predicate(out, &first, name, "move_relation", (int)j, -1, -1);
    }
  fputs("\n  ],\n", out);

  fputs("  \"goals\": [", out);
  for (uint32_t j = 0; j < m_goals; j++)
    fprintf(out,
            "%s{\"goal\": %u, \"justice_record\": %u, "
            "\"record_member\": %u}",
            j ? ", " : "", j, goal_record[j], goal_member[j]);
  fputs("],\n", out);

  fputs("  \"variables\": {\n    \"state\": [\n", out);
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur, next, reset;
    aig_latch_at(game, j, &cur, &next, &reset);
    const char *latch_name = aig_latch_name(game, j);
    char fallback[32];
    if (!latch_name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      latch_name = fallback;
    }
    fprintf(out,
            "%s      {\"certificate_input\": %u, \"name\": ", j ? ",\n" : "",
            j);
    json_string(out, latch_name);
    fprintf(out,
            ", \"game_latch\": %u, \"game_literal\": %u, "
            "\"next_game_literal\": %u, \"reset\": %u, "
            "\"solver_added\": %s",
            j, cur, next, reset, j >= original_nlat ? "true" : "false");
    if (j >= original_nlat) {
      bool found = false;
      for (uint32_t r = 0; r < m_goal_records && !found; r++) {
        const uint32_t *lits;
        uint32_t count;
        aig_justice_at(game, r, &lits, &count);
        for (uint32_t k = 0; k < count; k++)
          if (lits[k] == cur) {
            fprintf(out,
                    ", \"source\": {\"kind\": \"justice\", "
                    "\"record\": %u, \"member\": %u}",
                    r, k);
            found = true;
            break;
          }
      }
      for (uint32_t i = 0; i < m_fair && !found; i++)
        if (aig_fairness_at(game, i) == cur) {
          fprintf(out,
                  ", \"source\": {\"kind\": \"fairness\", "
                  "\"index\": %u}",
                  i);
          found = true;
        }
      if (!found)
        fputs(", \"source\": null", out);
    }
    fputc('}', out);
  }
  fputs("\n    ],\n    \"uncontrollable\": [", out);
  first = true;
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *input_name = aig_input_name(game, p, &lit);
    if (is_controllable(input_name))
      continue;
    char fallback[32];
    input_name = input_name_or_synthetic(input_name, p, fallback);
    fprintf(out,
            "%s{\"certificate_input\": %u, \"game_input\": %u, "
            "\"game_literal\": %u, \"name\": ",
            first ? "" : ", ", nlat + p, p, lit);
    json_string(out, input_name);
    fputc('}', out);
    first = false;
  }
  fputs("],\n    \"controllable\": [", out);
  first = true;
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *input_name = aig_input_name(game, p, &lit);
    if (!is_controllable(input_name))
      continue;
    char fallback[32];
    input_name = input_name_or_synthetic(input_name, p, fallback);
    fprintf(out,
            "%s{\"certificate_input\": %u, \"game_input\": %u, "
            "\"game_literal\": %u, \"name\": ",
            first ? "" : ", ", nlat + p, p, lit);
    json_string(out, input_name);
    fputc('}', out);
    first = false;
  }
  fputs("]\n  },\n", out);

  fputs("  \"sampling_semantics\": ", out);
  json_string(out,
              "Each solver-added reset-0 latch stores the preceding letter's "
              "input-dependent acceptance literal: next(sample)=source. "
              "The corresponding GF predicate is replaced by sample because "
              "GF p iff GF X p.");
  fputs(",\n  \"goal_counter_latches\": [", out);
  for (uint32_t j = 0; j < m_goals; j++) {
    char counter_name[64];
    snprintf(counter_name, sizeof counter_name, "__tlsf_gr1_goal_counter_%u",
             j);
    fprintf(out, "%s{\"strategy_latch\": %u, \"name\": ", j ? ", " : "",
            nlat + j);
    json_string(out, counter_name);
    fprintf(out,
            ", \"goal\": %u, "
            "\"reset\": 0, \"effective_initial\": %s, "
            "\"advance_to_goal\": %u}",
            j, j == 0 ? "true" : "false", (j + 1) % m_goals);
  }
  fputs("],\n  \"goal_counter_semantics\": ", out);
  json_string(out,
              "Strategy latches after the game/sampling latches are one-hot "
              "goal counters. All reset to 0; all-zero is interpreted as "
              "goal 0, then goal j advances to (j+1) mod goals exactly when "
              "inv & goal_j holds.");
  fputs(",\n  \"rank_semantics\": ", out);
  json_string(out,
              "For goal j the selected rank is the least lexicographic (k,i) "
              "whose x_j_k_i contains the state; y_j_k is the union of the "
              "fairness disjuncts at mu level k.");
  fputs(",\n  \"move_semantics\": ", out);
  json_string(out,
              "move_j is the pre-Skolem most-permissive relation over state, "
              "uncontrollable inputs and controllable inputs: advance safely "
              "inside inv at goal_j; otherwise move to goal/lower rank or "
              "stay in the selected x_j_k_i while fair_i is false.");
  if (unreal)
    fputs(",\n  \"environment_counter_strategy_exported\": false", out);
  fputs("\n}\n", out);
  return !ferror(out);
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
    name = input_name_or_synthetic(name, p, fallback);
    var2lit[p] = aig_input(certificate, name);
  }

  Bdd2Aig ctx = {certificate, var2lit, var_base, nvars, {0}, false};
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
    oxidd_record_failure(run->options, OXIDD_FAILURE_CONVERSION, run->phase,
                         "certificate_bdd2aig", run->operations, run->index);
    aig_free(certificate);
    certificate_error(options, "BDD-to-AIG certificate conversion failed",
                      nullptr);
    return false;
  }

  FILE *aag = fopen(options->aag_path, "w");
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

  if (options->json_path) {
    FILE *json = fopen(options->json_path, "w");
    if (!json) {
      aig_free(certificate);
      certificate_error(options, "cannot open certificate sidecar",
                        options->json_path);
      return false;
    }
    bool json_ok = write_certificate_json(
        json, certificate, game, options->aag_path, unreal, original_nlat,
        m_goal_records, m_goals, m_fair, n_fair_disj, goal_record, goal_member,
        y_levels);
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
                              uint32_t m_goals) {
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

  fputs("{\n  \"format\": \"tlsf-gr1-policy-v1\",\n", out);
  fputs("  \"circuit\": {\"path\": ", out);
  json_string(out, aag_path);
  fputs(", \"kind\": \"ASCII AIGER combinational\"},\n", out);
  fprintf(out,
          "  \"counts\": {\"game_state_variables\": %u, "
          "\"original_game_latches\": %u, \"sampling_latches\": %u, "
          "\"goals\": %u, \"uncontrollable_inputs\": %u, "
          "\"controllable_outputs\": %u, \"aig_inputs\": %u, "
          "\"aig_outputs\": %u, \"aig_ands\": %u},\n",
          nlat, original_nlat, nlat - original_nlat, m_goals, nu, nc,
          aig_num_inputs(policy), aig_num_outputs(policy),
          aig_num_ands(policy));

  fputs("  \"inputs\": {\n    \"state\": [", out);
  for (uint32_t j = 0; j < nlat; j++) {
    const char *name = aig_latch_name(game, j);
    char fallback[32];
    if (!name) {
      snprintf(fallback, sizeof fallback, "l%u", j);
      name = fallback;
    }
    fprintf(out, "%s{\"policy_input\": %u, \"game_latch\": %u, \"name\": ",
            j ? ", " : "", j, j);
    json_string(out, name);
    fputc('}', out);
  }
  fputs("],\n    \"counter\": [", out);
  for (uint32_t j = 0; j < m_goals; j++)
    fprintf(out,
            "%s{\"policy_input\": %u, \"goal\": %u, "
            "\"name\": \"curr_%u\", \"reset\": 0, "
            "\"effective_initial\": %s}",
            j ? ", " : "", nlat + j, j, j, j == 0 ? "true" : "false");
  fputs("],\n    \"uncontrollable\": [", out);
  bool first = true;
  uint32_t policy_input = nlat + m_goals;
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (is_controllable(name))
      continue;
    fprintf(out, "%s{\"policy_input\": %u, \"game_input\": %u, \"name\": ",
            first ? "" : ", ", policy_input++, p);
    json_string(out, name);
    fputc('}', out);
    first = false;
  }
  fputs("]\n  },\n  \"outputs\": {\n    \"controllable\": [", out);
  first = true;
  uint32_t policy_output = 0;
  for (uint32_t p = 0; p < nin; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (!is_controllable(name))
      continue;
    fprintf(out, "%s{\"policy_output\": %u, \"game_input\": %u, \"name\": ",
            first ? "" : ", ", policy_output++, p);
    json_string(out, name);
    fputc('}', out);
    first = false;
  }
  fputs("],\n    \"counter_next\": [", out);
  for (uint32_t j = 0; j < m_goals; j++)
    fprintf(out,
            "%s{\"policy_output\": %u, \"goal\": %u, "
            "\"name\": \"curr_next_%u\"}",
            j ? ", " : "", policy_output + j, j, j);
  fputs("]\n  },\n", out);
  fputs("  \"counter_semantics\": ", out);
  json_string(out,
              "All curr bits reset to zero; all-zero is interpreted as curr_0. "
              "Every transition produces exactly one hot next bit, advancing "
              "from j to (j+1) mod goals iff goal_j holds, otherwise staying.");
  fputs("\n}\n", out);
  return !ferror(out);
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

  Bdd2Aig ctx = {policy, var2lit, var_base, nvars, {0}, false};
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
    oxidd_record_failure(run->options, OXIDD_FAILURE_CONVERSION, run->phase,
                         "policy_bdd2aig", run->operations, run->index);
    aig_free(policy);
    certificate_error(options, "BDD-to-AIG policy conversion failed", nullptr);
    return false;
  }

  FILE *aag = fopen(options->policy_aag_path, "w");
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

  FILE *json = fopen(options->policy_json_path, "w");
  if (!json) {
    aig_free(policy);
    certificate_error(options, "cannot open policy sidecar",
                      options->policy_json_path);
    return false;
  }
  ok = write_policy_json(json, policy, game, options->policy_aag_path,
                         original_nlat, m_goals);
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

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

static void release_var_map(Bdd *var_bdd, uint32_t maxvar) {
  if (!var_bdd)
    return;
  for (uint32_t v = 0; v <= maxvar; v++) {
    oxidd_bdd_unref(var_bdd[v]);
    var_bdd[v] = (Bdd){0};
  }
}

Aig *solve_gr1_oxidd_ex_with_certificate(Aig *game, int *unreal,
                                         const OxiddSolveOptions *user_opts,
                                         Gr1CertificateOptions *certificate) {
  OxiddSolveOptions defaults = oxidd_solve_options_default();
  const OxiddSolveOptions *opts = user_opts ? user_opts : &defaults;
  *unreal = 0;
  if (opts->failure)
    *opts->failure = (OxiddFailure){0};
  if (!game)
    return nullptr;
  if (opts->demand_transitions || opts->realizability_only) {
    oxidd_record_failure(opts, OXIDD_FAILURE_CONFIGURATION, "configuration",
                         "safety_only_option", 0, 0);
    aig_free(game);
    return nullptr;
  }

  bool want_certificate = certificate && certificate->aag_path;
  bool want_certificate_json = want_certificate && certificate->json_path;
  bool want_policy = certificate && certificate->policy_aag_path;
  if (certificate) {
    certificate->failed = false;
    certificate->error[0] = '\0';
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

  // Highest AIG variable index, to size the literal -> BDD map.
  uint32_t maxvar = 0;
  for (uint32_t i = 0; i < nin; i++) {
    uint32_t lit;
    aig_input_name(game, i, &lit);
    if (lit / 2 > maxvar)
      maxvar = lit / 2;
  }
  for (uint32_t i = 0; i < nlat; i++) {
    uint32_t cur;
    aig_latch_at(game, i, &cur, nullptr, nullptr);
    if (cur / 2 > maxvar)
      maxvar = cur / 2;
  }
  for (uint32_t i = 0; i < nand; i++) {
    uint32_t lhs;
    aig_and_at(game, i, &lhs, nullptr, nullptr);
    if (lhs / 2 > maxvar)
      maxvar = lhs / 2;
  }

  // Allocations.
  // BDD var layout: 0..nin-1 = inputs, nin..nin+nlat-1 = latches,
  //                 nin+nlat..nin+nlat+m_goals-1 = goal counter curr[j].
  uint32_t nvars = nin + nlat + m_goals;

  // Manager: reuse session manager when active; otherwise right-size a fresh
  // one.
  bool own_mgr = (oxidd_session_get()._p == NULL);
  oxidd_bdd_manager_t m;
  uint32_t var_base;
  size_t node_cap = 0, cache_cap = 0;
  OxiddResolvedOrder order = {0};
  if (own_mgr) {
    if (!oxidd_resolve_var_order(game, opts, m_goals, &order)) {
      aig_free(game);
      return nullptr;
    }
    node_cap =
        opts->node_cap ? opts->node_cap : oxidd_default_capacity(nvars, 6);
    cache_cap =
        opts->cache_cap ? opts->cache_cap : oxidd_default_capacity(nvars, 6);
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
  Bdd *curr_bdd = m_goals ? calloc(m_goals, sizeof *curr_bdd) : nullptr;
  uint32_t *var2lit = calloc(nvars, sizeof *var2lit);
  uint32_t *lat_lit = nlat ? calloc(nlat, sizeof *lat_lit) : nullptr;
  uint32_t *curr_latch_lit =
      m_goals ? calloc(m_goals, sizeof *curr_latch_lit) : nullptr;
  uint32_t *cvars = nin ? calloc(nin, sizeof *cvars) : nullptr;
  uint32_t *uvars = nin ? calloc(nin, sizeof *uvars) : nullptr;
  uint32_t *cinput = nin ? calloc(nin, sizeof *cinput) : nullptr;
  Bdd *strat_f = nullptr;
  BddVec *y_levels = m_goals ? calloc(m_goals, sizeof *y_levels) : nullptr;
  uint32_t n_fair_disj = m_fair ? m_fair : 1;
  BddVec *x_levels =
      m_goals ? calloc(m_goals * n_fair_disj, sizeof *x_levels) : nullptr;
  Bdd *move_bdd =
      want_certificate && m_goals ? calloc(m_goals, sizeof *move_bdd) : nullptr;

  if (!var_bdd || (nlat && !next_bdd) || !goal_bdd || (m_fair && !fair_bdd) ||
      (want_certificate_json && (!goal_record || !goal_member)) || !curr_bdd ||
      !var2lit || (nlat && !lat_lit) || !curr_latch_lit ||
      (nin && (!cvars || !uvars || !cinput)) || !y_levels || !x_levels ||
      (want_certificate && !move_bdd)) {
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
      uvars[nuv++] = var_base + p;
    }
  }
  for (uint32_t j = 0; j < nlat; j++) {
    uint32_t cur;
    aig_latch_at(game, j, &cur, nullptr, nullptr);
    var_bdd[cur / 2] = oxidd_run_var(run, var_base + nin + j);
  }
  for (uint32_t j = 0; j < m_goals; j++)
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
  oxidd_bdd_unref(bad);
  bad = (Bdd){0};

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
    release_var_map(var_bdd, maxvar);
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
      if (!want_certificate)
        ok = false;
    }
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
        var2lit[p] =
            aig_input(strat, input_name_or_synthetic(name, p, (char[32]){0}));
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
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars, {0}, false};
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
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars, {0}, false};
      uint32_t nl = bdd2aig_root(&ctx, na);
      convert_error = convert_error || ctx.error;
      oxidd_bdd_unref(na);
      aig_set_latch_next(strat, lat_lit[j], nl);
    }
    if (sc)
      oxidd_bdd_substitution_free(sc);

    // Goal-counter latch next-functions.
    for (uint32_t j = 0; j < m_goals && !convert_error; j++) {
      Bdd2Aig ctx = {strat, var2lit, var_base, nvars, {0}, false};
      uint32_t nl = bdd2aig_root(&ctx, next_curr[j]);
      convert_error = convert_error || ctx.error;
      aig_set_latch_next(strat, curr_latch_lit[j], nl);
    }

    if (convert_error) {
      oxidd_record_failure(opts, OXIDD_FAILURE_CONVERSION, "conversion",
                           "bdd2aig_or_substitution", run->operations,
                           run->index);
      aig_free(strat);
      strat = nullptr;
      ok = false;
    }
  }

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

  if (ok && want_certificate) {
    oxidd_phase(run, "certificate");
    if (!export_certificate(run, game, certificate, *unreal != 0, original_nlat,
                            m_goal_records, m_goals, m_fair, n_fair_disj, nin,
                            nlat, nvars, var_base, goal_record, goal_member,
                            goal_bdd, y_levels, x_levels, move_bdd, W)) {
      aig_free(strat);
      strat = nullptr;
      ok = false;
    }
  }

  // -----------------------------------------------------------------------
  // Cleanup.
  // -----------------------------------------------------------------------

  if (next_curr) {
    for (uint32_t j = 0; j < m_goals; j++)
      oxidd_bdd_unref(next_curr[j]);
    free(next_curr);
  }
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
    for (uint32_t j = 0; j < m_goals; j++)
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
  release_var_map(var_bdd, maxvar);
  oxidd_bdd_unref(bad);
  oxidd_bdd_unref(notbad);
  oxidd_bdd_unref(W);
  oxidd_bdd_unref(ctrl_cube);
  oxidd_bdd_unref(unc_cube);
  if (sub_lat)
    oxidd_bdd_substitution_free(sub_lat);
  if (!strat && !*unreal && (!certificate || !certificate->failed))
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
  aig_free(game);
  return strat;
}

Aig *solve_gr1_oxidd_ex(Aig *game, int *unreal, const OxiddSolveOptions *opts) {
  return solve_gr1_oxidd_ex_with_certificate(game, unreal, opts, nullptr);
}

Aig *solve_gr1_oxidd_with_certificate(Aig *game, int *unreal,
                                      Gr1CertificateOptions *certificate) {
  OxiddSolveOptions opts = oxidd_solve_options_default();
  opts.safety_objective = OXIDD_SAFETY_OBJECTIVE_OUTPUT;
  opts.safety_output_index = 0;
  return solve_gr1_oxidd_ex_with_certificate(game, unreal, &opts, certificate);
}

Aig *solve_gr1_oxidd(Aig *game, int *unreal) {
  return solve_gr1_oxidd_with_certificate(game, unreal, nullptr);
}
