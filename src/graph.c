#define _POSIX_C_SOURCE 200809L
#include "tlsf/graph.h"

#include "tlsf/json.h"
#include "tlsf/print_ltlxba.h"

#include <stdlib.h>
#include <string.h>

static const char *KNOWN_TEMPLATES[] = {"response",
                                        "mutex",
                                        "pure-recurrence",
                                        "persistence",
                                        "guarded-next-assignment",
                                        "definition"};
enum { N_KNOWN = 6 };

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
// JSON (GSNF)
// ---------------------------------------------------------------------------

static void json_ap_array(JsonWriter *w, const ApTable *t, uint8_t flag) {
  json_arr_begin(w);
  for (uint32_t i = 0; i < t->count; i++)
    if (ap_table_flags(t, i) & flag)
      json_str(w, ap_table_name(t, i));
  json_arr_end(w);
}

static void json_set_names(JsonWriter *w, const ApTable *t, const ApSet *s) {
  json_arr_begin(w);
  for (uint32_t i = 0; i < t->count; i++)
    if (apset_test(s, i))
      json_str(w, ap_table_name(t, i));
  json_arr_end(w);
}

static void emit_json(FILE *out, ConstraintCover *cov, const GraphOpts *o) {
  JsonWriter w;
  json_init(&w, out, o->pretty);
  json_obj_begin(&w);
  json_key(&w, "format");
  json_str(&w, "GSNF");
  json_key(&w, "version");
  json_int(&w, 1);
  json_key(&w, "semantics");
  json_str(&w, sem_name(cov->spec->info.semantics));
  json_key(&w, "target");
  json_str(&w, tgt_name(cov->spec->info.target));
  json_key(&w, "inputs");
  json_ap_array(&w, &cov->aps, AP_FLAG_INPUT);
  json_key(&w, "outputs");
  json_ap_array(&w, &cov->aps, AP_FLAG_OUTPUT);

  // Constraints.
  json_key(&w, "constraints");
  json_arr_begin(&w);
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    if (o->candidates_only && c->candidate_count == 0)
      continue;
    char idbuf[24];
    snprintf(idbuf, sizeof idbuf, "c%u", c->id);
    json_obj_begin(&w);
    json_key(&w, "id");
    json_str(&w, idbuf);
    json_key(&w, "role");
    json_str(&w, role_name(c->role));
    json_key(&w, "class");
    json_str(&w, c->is_safety ? "syntactic_safety" : "syntactic_liveness");
    json_key(&w, "formula");
    char *fs = formula_str(c->formula);
    json_str(&w, fs ? fs : "");
    free(fs);
    json_key(&w, "inputs");
    json_set_names(&w, &cov->aps, &c->inputs);
    json_key(&w, "outputs");
    json_set_names(&w, &cov->aps, &c->outputs);
    if (o->templates) {
      json_key(&w, "template_candidates");
      json_arr_begin(&w);
      for (uint16_t k = 0; k < c->candidate_count; k++)
        if (!o->only_template || !strcmp(o->only_template, c->candidates[k]))
          json_str(&w, c->candidates[k]);
      json_arr_end(&w);
    }
    json_obj_end(&w);
  }
  json_arr_end(&w);

  // Edges (synthesis graph: AP ownership + response/mutex; constraint graph
  // omits per-AP occurrence edges).
  json_key(&w, "edges");
  json_arr_begin(&w);
  for (uint32_t i = 0; i < cov->count; i++) {
    if (!sel(o, i))
      continue;
    Constraint *c = &cov->items[i];
    char src[24];
    snprintf(src, sizeof src, "c%u", c->id);
    if (o->kind == GK_SYNTHESIS) {
      for (uint32_t a = 0; a < cov->aps.count; a++) {
        bool in = apset_test(&c->inputs, a), ou = apset_test(&c->outputs, a);
        if (!in && !ou)
          continue;
        json_obj_begin(&w);
        json_key(&w, "src");
        json_str(&w, src);
        json_key(&w, "dst");
        json_str(&w, ap_table_name(&cov->aps, a));
        json_key(&w, "type");
        json_str(&w, "occurs_in");
        json_obj_end(&w);
      }
    }
    if (c->resp_guard >= 0) {
      json_obj_begin(&w);
      json_key(&w, "src");
      json_str(&w, src);
      json_key(&w, "dst");
      json_str(&w, ap_table_name(&cov->aps, (uint32_t)c->resp_guard));
      json_key(&w, "type");
      json_str(&w, "response_guard");
      json_obj_end(&w);
    }
    if (c->resp_target >= 0) {
      json_obj_begin(&w);
      json_key(&w, "src");
      json_str(&w, src);
      json_key(&w, "dst");
      json_str(&w, ap_table_name(&cov->aps, (uint32_t)c->resp_target));
      json_key(&w, "type");
      json_str(&w, "response_target");
      json_obj_end(&w);
    }
    if (c->has_mutex) {
      for (uint32_t a = 0; a < cov->aps.count; a++) {
        if (!apset_test(&c->mutex_members, a))
          continue;
        json_obj_begin(&w);
        json_key(&w, "src");
        json_str(&w, src);
        json_key(&w, "dst");
        json_str(&w, ap_table_name(&cov->aps, a));
        json_key(&w, "type");
        json_str(&w, "mutex_member");
        json_obj_end(&w);
      }
    }
  }
  json_arr_end(&w);

  // Template blocks.
  json_key(&w, "template_blocks");
  json_arr_begin(&w);
  for (uint32_t b = 0; b < cov->block_count; b++) {
    if (o->only_template &&
        strcmp(o->only_template, cov->blocks[b].template_name) != 0)
      continue;
    char idbuf[24];
    snprintf(idbuf, sizeof idbuf, "tb%u", b);
    json_obj_begin(&w);
    json_key(&w, "id");
    json_str(&w, idbuf);
    json_key(&w, "template");
    json_str(&w, cov->blocks[b].template_name);
    json_key(&w, "constraints");
    json_arr_begin(&w);
    for (uint32_t k = 0; k < cov->blocks[b].count; k++) {
      char cb[24];
      snprintf(cb, sizeof cb, "c%u", cov->blocks[b].constraint_ids[k]);
      json_str(&w, cb);
    }
    json_arr_end(&w);
    json_key(&w, "status");
    json_str(&w, "candidate");
    json_obj_end(&w);
  }
  json_arr_end(&w);

  json_key(&w, "wl");
  json_null(&w);
  json_obj_end(&w);
  fputc('\n', out);
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
    if (c->resp_target >= 0)
      fprintf(out, "  c%u -> \"%s\" [label=\"response_target\"];\n", c->id,
              ap_table_name(&cov->aps, (uint32_t)c->resp_target));
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
  if (o->kind == GK_FORMULA || o->kind == GK_QUOTIENT)
    return -1; // not implemented this milestone
  switch (fmt) {
  case GFMT_TEXT:
    emit_text(out, cov, o);
    return 0;
  case GFMT_JSON:
    emit_json(out, cov, o);
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
