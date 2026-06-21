// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/graph.h"

#include "tlsf/print_ltlxba.h"

#include <stdlib.h>
#include <string.h>

static const char *KNOWN_TEMPLATES[] = {"response",
                                        "mutex",
                                        "pure-recurrence",
                                        "persistence",
                                        "guarded-next-assignment",
                                        "global-recurrence-switch",
                                        "definition"};
enum { N_KNOWN = 7 };

static bool sel(const GraphOpts *o, uint32_t i) {
  return !o->selected || o->selected[i];
}

static bool has_candidate(const Constraint *c, const char *name) {
  for (uint16_t i = 0; i < c->candidate_count; i++)
    if (strcmp(c->candidates[i], name) == 0)
      return true;
  return false;
}

// Render a formula to a freshly malloc'd string (caller frees).
static char *formula_str(const Node *n) {
  char *buf = nullptr;
  size_t sz = 0;
  FILE *ms = open_memstream(&buf, &sz);
  if (!ms)
    return nullptr;
  print_ltlxba_formula(ms, n, /*full_parens=*/false);
  fclose(ms);
  return buf;
}

static const char *sem_name(Semantics s) {
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
  return "?";
}
static const char *tgt_name(Target t) {
  return t == TARGET_MOORE ? "Moore" : "Mealy";
}

// ---------------------------------------------------------------------------
// Text summary
// ---------------------------------------------------------------------------

static void emit_text(FILE *out, ConstraintCover *cov, const GraphOpts *o) {
  TlsfSpec *spec = cov->spec;
  uint32_t nin = 0, nout = 0;
  for (uint32_t i = 0; i < cov->aps.count; i++) {
    uint8_t f = ap_table_flags(&cov->aps, i);
    nin += (f & AP_FLAG_INPUT) != 0;
    nout += (f & AP_FLAG_OUTPUT) != 0;
  }

  uint32_t nsel = 0, nsafe = 0, nlive = 0;
  uint32_t tally[N_KNOWN] = {0};
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    nsel++;
    Constraint *c = &cov->items[i];
    if (c->is_safety)
      nsafe++;
    else
      nlive++;
    for (int k = 0; k < N_KNOWN; k++)
      if (has_candidate(c, KNOWN_TEMPLATES[k]))
        tally[k]++;
  }

  if (!o->candidates_only) {
    fprintf(out, "semantics: %s\n", sem_name(spec->info.semantics));
    fprintf(out, "target: %s\n", tgt_name(spec->info.target));
    fprintf(out, "inputs: %u\n", nin);
    fprintf(out, "outputs: %u\n", nout);
    fprintf(out, "constraints: %u\n", nsel);
    fprintf(out, "syntactic safety: %u\n", nsafe);
    fprintf(out, "syntactic liveness: %u\n", nlive);
  }

  if (o->templates || o->candidates_only) {
    fprintf(out, "template candidates:\n");
    for (int k = 0; k < N_KNOWN; k++) {
      if (o->only_template && strcmp(o->only_template, KNOWN_TEMPLATES[k]) != 0)
        continue;
      if (tally[k])
        fprintf(out, "  %s: %u\n", KNOWN_TEMPLATES[k], tally[k]);
    }
    if (cov->block_count) {
      fprintf(out, "template blocks:\n");
      for (uint32_t b = 0; b < cov->block_count; b++) {
        if (o->only_template &&
            strcmp(o->only_template, cov->blocks[b].template_name) != 0)
          continue;
        fprintf(out, "  %s: %u constraints\n", cov->blocks[b].template_name,
                cov->blocks[b].count);
      }
    }
  }
}

// ---------------------------------------------------------------------------
// GSNF line format (DIMACS-style: one tagged record per line, see README)
// ---------------------------------------------------------------------------

static void emit_gsnf(FILE *out, ConstraintCover *cov, const GraphOpts *o) {
  uint32_t nin = 0, nout = 0, nsel = 0;
  for (uint32_t i = 0; i < cov->aps.count; i++) {
    uint8_t f = ap_table_flags(&cov->aps, i);
    nin += (f & AP_FLAG_INPUT) != 0;
    nout += (f & AP_FLAG_OUTPUT) != 0;
  }
  for (uint32_t i = 0; i < cov->count; i++)
    if (sel(o, i))
      nsel++;

  fprintf(out, "c GSNF (candidate-only structural view)\n");
  fprintf(out, "p gsnf %u %u %u\n", nin, nout, nsel);
  fprintf(out, "m semantics %s\n", sem_name(cov->spec->info.semantics));
  fprintf(out, "m target %s\n", tgt_name(cov->spec->info.target));
  for (uint32_t i = 0; i < cov->aps.count; i++)
    if (ap_table_flags(&cov->aps, i) & AP_FLAG_INPUT)
      fprintf(out, "i %s\n", ap_table_name(&cov->aps, i));
  for (uint32_t i = 0; i < cov->aps.count; i++)
    if (ap_table_flags(&cov->aps, i) & AP_FLAG_OUTPUT)
      fprintf(out, "o %s\n", ap_table_name(&cov->aps, i));

  // Constraint nodes, their candidates and formulas.
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    if (o->candidates_only && c->candidate_count == 0)
      continue;
    fprintf(out, "n c%u %s %s\n", c->id, role_name(c->role),
            c->is_safety ? "safety" : "liveness");
    if (o->templates)
      for (uint16_t k = 0; k < c->candidate_count; k++)
        if (!o->only_template ||
            strcmp(o->only_template, c->candidates[k]) == 0)
          fprintf(out, "k c%u %s\n", c->id, c->candidates[k]);
    char *fs = formula_str(c->formula);
    fprintf(out, "f c%u %s\n", c->id, fs ? fs : "");
    free(fs);
  }

  // Edges: occurs_in (synthesis only) + response/mutex.
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    if (o->kind == GK_SYNTHESIS)
      for (uint32_t a = 0; a < cov->aps.count; a++)
        if (apset_test(&c->inputs, a) || apset_test(&c->outputs, a))
          fprintf(out, "e c%u %s occurs_in\n", c->id,
                  ap_table_name(&cov->aps, a));
    const TemplateCandidate *resp =
        constraint_find_candidate_payload(cov, c, CAND_RESPONSE);
    if (resp && resp->u.response.guard >= 0)
      fprintf(out, "e c%u %s response_guard\n", c->id,
              ap_table_name(&cov->aps, (uint32_t)resp->u.response.guard));
    if (resp && resp->u.response.target >= 0)
      fprintf(out, "e c%u %s response_target\n", c->id,
              ap_table_name(&cov->aps, (uint32_t)resp->u.response.target));
    const TemplateCandidate *mutex =
        constraint_find_candidate_payload(cov, c, CAND_MUTEX);
    if (mutex)
      for (uint32_t a = 0; a < cov->aps.count; a++)
        if (apset_test(&mutex->u.mutex.members, a))
          fprintf(out, "e c%u %s mutex_member\n", c->id,
                  ap_table_name(&cov->aps, a));
  }

  // Template blocks: tag, then the member constraint ids.
  for (uint32_t b = 0; b < cov->block_count; b++) {
    if (o->only_template &&
        strcmp(o->only_template, cov->blocks[b].template_name) != 0)
      continue;
    fprintf(out, "t %s", cov->blocks[b].template_name);
    for (uint32_t k = 0; k < cov->blocks[b].count; k++)
      fprintf(out, " c%u", cov->blocks[b].constraint_ids[k]);
    fprintf(out, "\n");
  }
}

// ---------------------------------------------------------------------------
// DOT
// ---------------------------------------------------------------------------

static void emit_dot(FILE *out, ConstraintCover *cov, const GraphOpts *o) {
  fprintf(out, "digraph GSNF {\n  rankdir=LR;\n");
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    fprintf(out, "  c%u [shape=box,label=\"c%u\\n%s\\n%s\"];\n", c->id, c->id,
            role_name(c->role), c->is_safety ? "safety" : "liveness");
  }
  if (o->kind == GK_SYNTHESIS)
    for (uint32_t a = 0; a < cov->aps.count; a++)
      fprintf(out, "  \"%s\" [shape=ellipse];\n", ap_table_name(&cov->aps, a));

  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    if (o->kind == GK_SYNTHESIS)
      for (uint32_t a = 0; a < cov->aps.count; a++)
        if (apset_test(&c->inputs, a) || apset_test(&c->outputs, a))
          fprintf(out, "  c%u -> \"%s\" [label=\"occurs_in\"];\n", c->id,
                  ap_table_name(&cov->aps, a));
    const TemplateCandidate *resp =
        constraint_find_candidate_payload(cov, c, CAND_RESPONSE);
    if (resp && resp->u.response.target >= 0)
      fprintf(out, "  c%u -> \"%s\" [label=\"response_target\"];\n", c->id,
              ap_table_name(&cov->aps, (uint32_t)resp->u.response.target));
  }
  fprintf(out, "}\n");
}

// ---------------------------------------------------------------------------
// TSV constraint table
// ---------------------------------------------------------------------------

static void emit_tsv(FILE *out, ConstraintCover *cov, const GraphOpts *o) {
  fprintf(out,
          "id\trole\tside\tinvariant\tclass\tinputs\toutputs\tcandidates\n");
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    fprintf(out, "c%u\t%s\t%s\t%s\t%s\t%u\t%u\t", c->id, role_name(c->role),
            c->assumption_side ? "assumption" : "guarantee",
            c->invariant_wrapped ? "yes" : "no",
            c->is_safety ? "safety" : "liveness", apset_count(&c->inputs),
            apset_count(&c->outputs));
    for (uint16_t k = 0; k < c->candidate_count; k++)
      fprintf(out, "%s%s", k ? ";" : "", c->candidates[k]);
    fprintf(out, "\n");
  }
}

int graph_emit(FILE *out, ConstraintCover *cov, GraphFormat fmt,
               const GraphOpts *o) {
  switch (fmt) {
  case GFMT_TEXT:
    emit_text(out, cov, o);
    return 0;
  case GFMT_GSNF:
    emit_gsnf(out, cov, o);
    return 0;
  case GFMT_DOT:
    emit_dot(out, cov, o);
    return 0;
  case GFMT_TSV:
    emit_tsv(out, cov, o);
    return 0;
  }
  return -1;
}
