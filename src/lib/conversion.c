#define _POSIX_C_SOURCE 200809L
#include "tlsf/convert.h"
#include "conversion_internal.h"
#include "diagnostic.h"
#include "gr.h"
#include "nnf.h"
#include "spec_internal.h"
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

const char *conversion_semantics_name(Semantics s) {
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

const char *conversion_target_name(Target t) {
  return t == TARGET_MOORE ? "Moore" : "Mealy";
}

char *conversion_dup_cstr(const char *s) {
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
  char *out = conversion_dup_cstr(s);
  if (!out || !lower)
    return out;
  for (char *p = out; *p; p++)
    *p = (char)tolower((unsigned char)*p);
  return out;
}

void conversion_free_strings(char **items, uint32_t count) {
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

bool conversion_collect_signals(const ApTable *aps, const bool *seen,
                                uint8_t flag, bool lower, char ***items,
                                uint32_t *count) {
  *items = nullptr;
  *count = 0;
  for (uint32_t a = 0; a < aps->count; a++) {
    if (seen && !seen[a])
      continue;
    if (!(ap_table_flags(aps, a) & flag) &&
        !(flag == AP_FLAG_INPUT && ap_table_flags(aps, a) == 0))
      continue;
    if (!push_signal(items, count, ap_table_name(aps, a), lower)) {
      conversion_free_strings(*items, *count);
      *items = nullptr;
      *count = 0;
      return false;
    }
  }
  return true;
}

static uint32_t count_indexed_families(const SignalDecl *signals,
                                       uint32_t count) {
  uint32_t result = 0;
  for (uint32_t i = 0; i < count; i++)
    if (signals[i].origin_is_bus &&
        signals[i].origin_index == signals[i].origin_bus_lo)
      result++;
  return result;
}

static bool fill_indexed_family(TlsfDecomposeIndexedFamily *out,
                                const SignalDecl *signals, uint32_t count,
                                uint32_t first, bool is_output, bool lower) {
  const SignalDecl *source = &signals[first];
  out->lo = source->origin_bus_lo;
  out->hi = source->origin_bus_hi;
  out->is_output = is_output;
  out->is_enum = source->origin_is_enum;
  out->origin_name = dup_maybe_lower(source->origin_name, lower);
  out->n_members = (uint32_t)out->hi - out->lo + 1u;
  out->members = calloc(out->n_members, sizeof *out->members);
  if (!out->origin_name || !out->members)
    return false;

  for (uint32_t i = first; i < count; i++) {
    const SignalDecl *candidate = &signals[i];
    if (!candidate->origin_is_bus ||
        candidate->origin_name != source->origin_name ||
        candidate->origin_bus_lo != out->lo ||
        candidate->origin_bus_hi != out->hi)
      continue;
    uint32_t position = candidate->origin_index - out->lo;
    if (position >= out->n_members || out->members[position])
      return false;
    out->members[position] = dup_maybe_lower(candidate->name, lower);
    if (!out->members[position])
      return false;
  }
  for (uint32_t i = 0; i < out->n_members; i++)
    if (!out->members[i])
      return false;
  return true;
}

bool conversion_collect_families(TlsfDecomposeIndexedFamily **families,
                                 uint32_t *count, const TlsfSpec *spec,
                                 bool lower) {
  const uint32_t input_families =
      count_indexed_families(spec->inputs, spec->input_count);
  const uint32_t output_families =
      count_indexed_families(spec->outputs, spec->output_count);
  *count = input_families + output_families;
  if (!*count)
    return true;
  (*families) = calloc(*count, sizeof *(*families));
  if (!(*families))
    return false;

  uint32_t at = 0;
  const SignalDecl *lists[2] = {spec->inputs, spec->outputs};
  const uint32_t counts[2] = {spec->input_count, spec->output_count};
  for (uint32_t side = 0; side < 2; side++)
    for (uint32_t i = 0; i < counts[side]; i++)
      if (lists[side][i].origin_is_bus &&
          lists[side][i].origin_index == lists[side][i].origin_bus_lo &&
          !fill_indexed_family(&(*families)[at++], lists[side], counts[side], i,
                               side == 1, lower))
        return false;
  return at == *count;
}

char *conversion_render_ltl(const Node *root, LtlFormat fmt, bool finite,
                            bool lower) {
  if (!root)
    return nullptr;
  char *buf = nullptr;
  size_t len = 0;
  FILE *ms = open_memstream(&buf, &len);
  if (!ms)
    return nullptr;
  bool ok = print_ltl(ms, root, fmt, /*full_parens=*/false, finite, lower);
  if (fclose(ms) != 0 || !ok) {
    free(buf);
    return nullptr;
  }
  if (len && buf[len - 1] == '\n')
    buf[len - 1] = '\0';
  return buf;
}

// Intern every atomic proposition occurring in `n` (no flag change).
void conversion_intern_aps(ApTable *t, const Node *n) {
  switch (n->kind) {
  case NODE_AP:
    (void)ap_table_intern(t, n->name, 0);
    return;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    conversion_intern_aps(t, n->arg);
    return;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    conversion_intern_aps(t, n->lhs);
    conversion_intern_aps(t, n->rhs);
    return;
  default:
    return; // true / false
  }
}
void conversion_seed_signals(ApTable *aps, const TlsfSpec *spec) {
  // Seed the AP table with scalar signals so input/output flags are known.
  // (Buses are exploded into scalar elements during expand().)
  for (uint32_t i = 0; i < spec->input_count; i++)
    if (!spec->inputs[i].is_bus)
      (void)ap_table_intern(aps, spec->inputs[i].name, AP_FLAG_INPUT);
  for (uint32_t i = 0; i < spec->output_count; i++)
    if (!spec->outputs[i].is_bus)
      (void)ap_table_intern(aps, spec->outputs[i].name, AP_FLAG_OUTPUT);
}

bool conversion_prepare(TlsfSpec *spec, const char *semantics,
                        const char *target, const ParamOverride *overrides,
                        size_t count, bool fair_environment, const char *tool) {
  if (semantics && !parse_semantics(semantics, &spec->info.semantics)) {
    fprintf(tlsf_diagnostic_stream(), "%s: invalid semantics '%s'\n", tool,
            semantics);
    return false;
  }
  if (target && !parse_target(target, &spec->info.target)) {
    fprintf(tlsf_diagnostic_stream(),
            "%s: invalid target '%s' (expect Mealy or Moore)\n", tool, target);
    return false;
  }
  if (!spec_validate_semantics(spec, tool))
    return false;
  if (fair_environment && semantics_is_finite(spec->info.semantics)) {
    fprintf(tlsf_diagnostic_stream(),
            "%s: --fair-environment is only available for infinite semantics\n",
            tool);
    return false;
  }
  if (fair_environment && !spec_add_fair_environment(spec)) {
    fprintf(tlsf_diagnostic_stream(),
            "%s: fair-environment transform failed (OOM)\n", tool);
    return false;
  }
  if (expand(spec, overrides, count) != 0)
    return false;
  if (!spec_adapt_target(spec)) {
    fprintf(tlsf_diagnostic_stream(),
            "%s: semantics/target adaptation failed (OOM)\n", tool);
    return false;
  }
  return !arena_failed(spec->arena);
}

static bool has_indexed_conjunction(const char *text) {
  while ((text = strstr(text, "&&"))) {
    text += 2;
    while (isspace((unsigned char)*text))
      ++text;
    if (*text == '[')
      return true;
  }
  return false;
}

static bool family_member(const char *name,
                          const TlsfDecomposeIndexedFamily *families,
                          uint32_t count, bool output) {
  for (uint32_t i = 0; i < count; ++i)
    if (families[i].is_output == output)
      for (uint32_t j = 0; j < families[i].n_members; ++j)
        if (strcmp(name, families[i].members[j]) == 0)
          return true;
  return false;
}

// The old Acacia serialization: reverse scalar declarations, then reverse
// ordinary and enum bus declarations, retaining each bus's member order.
static bool order_signals(char ***items, uint32_t *count,
                          const TlsfConversionResult *result, bool output) {
  char **ordered = nullptr;
  uint32_t size = 0;
  for (uint32_t i = *count; i-- > 0;)
    if (!family_member((*items)[i], result->indexed_families,
                       result->n_indexed_families, output) &&
        !push_signal(&ordered, &size, (*items)[i], false))
      goto fail;
  for (unsigned enums = 0; enums < 2; ++enums)
    for (uint32_t i = result->n_indexed_families; i-- > 0;) {
      const TlsfDecomposeIndexedFamily *family = &result->indexed_families[i];
      if (family->is_output != output || family->is_enum != (bool)enums)
        continue;
      for (uint32_t j = 0; j < family->n_members; ++j)
        if (!push_signal(&ordered, &size, family->members[j], false))
          goto fail;
    }
  conversion_free_strings(*items, *count);
  *items = ordered;
  *count = size;
  return true;
fail:
  conversion_free_strings(ordered, size);
  return false;
}

static bool collect_spec_signals(TlsfConversionResult *result, TlsfSpec *spec) {
  ApTable aps;
  ap_table_init(&aps, spec->arena);
  conversion_seed_signals(&aps, spec);
  // Match the cover's actual AP producer, including undeclared occurrences
  // and their traversal order, without constructing constraints or a cover.
  const FormulaList *lists[] = {&spec->initially, &spec->require,
                                &spec->assume,    &spec->preset,
                                &spec->assert_,   &spec->guarantee};
  for (size_t i = 0; i < sizeof lists / sizeof *lists; ++i)
    for (uint32_t j = 0; j < lists[i]->count; ++j) {
      Node *nnf = to_nnf(spec->arena, lists[i]->formulas[j], true,
                         semantics_is_finite(spec->info.semantics));
      if (!nnf)
        return false;
      conversion_intern_aps(&aps, nnf);
    }
  return conversion_collect_signals(&aps, nullptr, AP_FLAG_INPUT, true,
                                    &result->inputs, &result->n_inputs) &&
         conversion_collect_signals(&aps, nullptr, AP_FLAG_OUTPUT, true,
                                    &result->outputs, &result->n_outputs) &&
         order_signals(&result->inputs, &result->n_inputs, result, false) &&
         order_signals(&result->outputs, &result->n_outputs, result, true);
}

TlsfConversionResult *tlsf_convert(const char *text,
                                   const char *effective_target) {
  if (!text)
    return nullptr;
  FILE *input = fmemopen((void *)text, strlen(text), "r");
  if (!input)
    return nullptr;
  TlsfSpec *spec = spec_parse(input, "tlsf-convert");
  fclose(input);
  if (!spec)
    return nullptr;
  TlsfConversionResult *result = calloc(1, sizeof *result);
  if (!result)
    goto fail;
  result->semantics =
      conversion_dup_cstr(conversion_semantics_name(spec->info.semantics));
  result->original_target =
      conversion_dup_cstr(conversion_target_name(spec->info.target));
  if (semantics_is_finite(spec->info.semantics)) {
    fprintf(tlsf_diagnostic_stream(),
            "tlsf-convert: finite TLSF semantics are not supported\n");
    goto fail;
  }
  if (!conversion_prepare(spec, nullptr, effective_target, nullptr, 0, false,
                          "tlsf-convert") ||
      !spec_validate_lowercase_signals(spec, "tlsf-convert") ||
      !spec_validate_ltlxba_atoms(spec, "tlsf-convert"))
    goto fail;
  result->effective_target =
      conversion_dup_cstr(conversion_target_name(spec->info.target));
  result->gr_level = gr_level(spec);
  result->has_indexed_conjunction = has_indexed_conjunction(text);
  ClassifiedSpec *classified = classify_spec(spec);
  if (!classified)
    goto fail;
  Node *root = build_spec_formula(spec, classified, PRINT_ALL);
  if (!root || arena_failed(spec->arena))
    goto fail;
  result->preprocessed_ltl =
      conversion_render_ltl(root, LTL_FMT_LTLXBA, false, true);
  if (!result->semantics || !result->original_target ||
      !result->effective_target || !result->preprocessed_ltl ||
      !conversion_collect_families(&result->indexed_families,
                                   &result->n_indexed_families, spec, true) ||
      !collect_spec_signals(result, spec) || arena_failed(spec->arena))
    goto fail;
  spec_free(spec);
  return result;
fail:
  spec_free(spec);
  tlsf_conversion_result_free(result);
  return nullptr;
}

void tlsf_conversion_result_free(TlsfConversionResult *result) {
  if (!result)
    return;
  free(result->preprocessed_ltl);
  conversion_free_strings(result->inputs, result->n_inputs);
  conversion_free_strings(result->outputs, result->n_outputs);
  if (result->indexed_families)
    for (uint32_t i = 0; i < result->n_indexed_families; ++i) {
      free(result->indexed_families[i].origin_name);
      conversion_free_strings(result->indexed_families[i].members,
                              result->indexed_families[i].n_members);
    }
  free(result->indexed_families);
  free(result->semantics);
  free(result->original_target);
  free(result->effective_target);
  free(result);
}
