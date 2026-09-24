#define _GNU_SOURCE
#include "provenance.h"

#include "tlsf/print_tlsf.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

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
      if (*p < 32)
        fprintf(out, "\\u%04x", *p);
      else
        fputc(*p, out);
    }
  }
  fputc('"', out);
}

static char *formula_text(const Node *node) {
  char *buf = nullptr;
  size_t size = 0;
  FILE *stream = open_memstream(&buf, &size);
  if (!stream)
    return nullptr;
  print_tlsf_formula(stream, node);
  if (fclose(stream) != 0) {
    free(buf);
    return nullptr;
  }
  return buf;
}

static bool contains_definition_call(const Node *node) {
  if (!node)
    return false;
  switch (node->kind) {
  case NODE_DEF_CALL:
    return true;
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
  case NODE_AP:
  case NODE_INT_VAR:
  case NODE_SIZEOF:
    return false;
  case NODE_BUS_INDEX:
    return contains_definition_call(node->bus_index);
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    return contains_definition_call(node->arg);
  case NODE_ITE:
    return contains_definition_call(node->if_cond) ||
           contains_definition_call(node->if_then) ||
           contains_definition_call(node->if_else);
  case NODE_SET:
  case NODE_SET_ENUM:
    for (uint16_t i = 0; i < node->set_size; i++)
      if (contains_definition_call(node->set_elems[i]))
        return true;
    return false;
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    return contains_definition_call(node->qlo) ||
           contains_definition_call(node->qhi) ||
           contains_definition_call(node->qset) ||
           contains_definition_call(node->qbody);
  default:
    return contains_definition_call(node->lhs) ||
           contains_definition_call(node->rhs);
  }
}

static void mark_aps(const Node *node, const SignalDecl *inputs,
                     uint32_t ninputs, const SignalDecl *outputs,
                     uint32_t noutputs, bool *used, bool *unresolved) {
  if (!node)
    return;
  switch (node->kind) {
  case NODE_AP: {
    uint32_t matches = 0;
    for (uint32_t i = 0; i < ninputs; i++)
      if (strcmp(inputs[i].name, node->name) == 0) {
        used[i] = true;
        matches++;
      }
    for (uint32_t i = 0; i < noutputs; i++)
      if (strcmp(outputs[i].name, node->name) == 0) {
        used[ninputs + i] = true;
        matches++;
      }
    if (matches != 1)
      *unresolved = true;
    return;
  }
  case NODE_TRUE:
  case NODE_FALSE:
    return;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    mark_aps(node->arg, inputs, ninputs, outputs, noutputs, used, unresolved);
    return;
  default:
    mark_aps(node->lhs, inputs, ninputs, outputs, noutputs, used, unresolved);
    mark_aps(node->rhs, inputs, ninputs, outputs, noutputs, used, unresolved);
    return;
  }
}

static void emit_signal(FILE *out, const SignalDecl *signal, bool is_output,
                        bool *first) {
  if (!*first)
    fputs(",\n", out);
  *first = false;
  fprintf(out, "    {\"name\": ");
  json_string(out, signal->name);
  fprintf(out,
          ", \"direction\": \"%s\", \"declaration_id\": \"%s:%u\", "
          "\"source_name\": ",
          is_output ? "output" : "input", is_output ? "output" : "input",
          signal->origin_id);
  json_string(out, signal->origin_name);
  fprintf(out, ", \"dimensions\": %u, \"index_tuple\": [",
          signal->origin_is_bus ? 1u : 0u);
  if (signal->origin_is_bus)
    fprintf(out, "%u", signal->origin_index);
  fprintf(out,
          "], \"bounds\": [%u, %u], \"width\": %u, "
          "\"width_kind\": ",
          signal->origin_bus_lo, signal->origin_bus_hi,
          signal->origin_is_bus
              ? (unsigned)(signal->origin_bus_hi - signal->origin_bus_lo + 1u)
              : 1u);
  if (!signal->origin_is_bus)
    json_string(out, "scalar");
  else if (signal->origin_is_enum)
    json_string(out, "enum-encoding");
  else if (signal->origin_is_encoded_bit)
    json_string(out, "proved-logarithmic-encoding");
  else if (contains_definition_call(signal->origin_width_expr))
    json_string(out, "derived-width");
  else
    json_string(out, "range");
  fputs(", \"width_expression\": ", out);
  char *expression = signal->origin_width_expr
                         ? formula_text(signal->origin_width_expr)
                         : nullptr;
  if (expression)
    json_string(out, expression);
  else
    fputs("null", out);
  free(expression);
  fputs(", \"index_role\": ", out);
  if (!signal->origin_is_bus)
    json_string(out, "scalar");
  else if (signal->origin_is_enum || signal->origin_is_encoded_bit)
    json_string(out, "representation-bit");
  else if (contains_definition_call(signal->origin_width_expr))
    json_string(out, "undetermined");
  else
    json_string(out, "element");
  fputc('}', out);
}

typedef struct {
  FILE *out;
  const TlsfSpec *spec;
  const char *block;
  uint32_t ordinal;
  uint32_t generated_position;
  bool first;
  bool failed;
  bool unresolved;
} ConjunctWriter;

static void emit_conjunct(ConjunctWriter *writer, const Node *node,
                          bool under_globally) {
  if (writer->failed)
    return;
  if (node->kind == NODE_AND) {
    emit_conjunct(writer, node->lhs, under_globally);
    emit_conjunct(writer, node->rhs, under_globally);
    return;
  }
  if (!under_globally && node->kind == NODE_G && node->arg->kind == NODE_AND) {
    emit_conjunct(writer, node->arg, true);
    return;
  }
  Node wrapper = {.kind = NODE_G, .arg = (Node *)node};
  const Node *formula = under_globally ? &wrapper : node;
  char *text = formula_text(formula);
  if (!text) {
    writer->failed = true;
    return;
  }
  FILE *out = writer->out;
  if (!writer->first)
    fputs(",\n", out);
  writer->first = false;
  uint32_t position = writer->generated_position++;
  fputs("    {\"block\": ", out);
  json_string(out, writer->block);
  fprintf(out,
          ", \"source_formula_id\": \"%s:%u\", "
          "\"source_node_id\": %u, \"generated_position\": %u, "
          "\"formula\": ",
          writer->block, writer->ordinal, node->source_id, position);
  json_string(out, text);
  free(text);
  fputs(", \"bindings\": [", out);
  bool first = true;
  for (const OriginBinding *binding = node->origin_bindings; binding;
       binding = binding->parent) {
    if (!first)
      fputs(", ", out);
    first = false;
    fprintf(out, "{\"binder_id\": %u, \"name\": ", binding->binder_id);
    json_string(out, binding->name);
    fprintf(out, ", \"value\": %lld}", (long long)binding->value);
  }
  fputs("], \"signals\": [", out);
  uint32_t count = writer->spec->input_count + writer->spec->output_count;
  bool *used = calloc(count ? count : 1, sizeof *used);
  if (!used) {
    writer->failed = true;
    return;
  }
  bool unresolved = false;
  mark_aps(formula, writer->spec->inputs, writer->spec->input_count,
           writer->spec->outputs, writer->spec->output_count, used,
           &unresolved);
  if (unresolved)
    writer->unresolved = true;
  first = true;
  for (uint32_t i = 0; i < count; i++) {
    if (!used[i])
      continue;
    if (!first)
      fputs(", ", out);
    first = false;
    const SignalDecl *signal =
        i < writer->spec->input_count
            ? &writer->spec->inputs[i]
            : &writer->spec->outputs[i - writer->spec->input_count];
    json_string(out, signal->name);
  }
  free(used);
  fprintf(out, "], \"unresolved_signal_reference\": %s}",
          unresolved ? "true" : "false");
}

int provenance_write(FILE *out, const TlsfSpec *spec, const ParamDecl *params,
                     uint16_t param_count, const char source_sha256[65]) {
  bool duplicate_signals = false;
  for (uint32_t i = 0; i < spec->input_count + spec->output_count; i++) {
    const SignalDecl *left = i < spec->input_count
                                 ? &spec->inputs[i]
                                 : &spec->outputs[i - spec->input_count];
    for (uint32_t j = 0; j < i; j++) {
      const SignalDecl *right = j < spec->input_count
                                    ? &spec->inputs[j]
                                    : &spec->outputs[j - spec->input_count];
      if (strcmp(left->name, right->name) == 0)
        duplicate_signals = true;
    }
  }
  fprintf(out, "{\n  \"schema\": \"tlsf-tools.frontend-provenance.v1\",\n"
               "  \"format_version\": 1,\n  \"source_sha256\": ");
  json_string(out, source_sha256);
  fputs(",\n  \"parameters\": [", out);
  for (uint16_t i = 0; i < param_count; i++) {
    if (i)
      fputs(", ", out);
    fprintf(out, "{\"id\": %u, \"name\": ", (unsigned)i + 1);
    json_string(out, params[i].name);
    fprintf(out, ", \"value\": %lld}", (long long)params[i].value);
  }
  fputs("],\n  \"signals\": [\n", out);
  bool first = true;
  for (uint32_t i = 0; i < spec->input_count; i++)
    emit_signal(out, &spec->inputs[i], false, &first);
  for (uint32_t i = 0; i < spec->output_count; i++)
    emit_signal(out, &spec->outputs[i], true, &first);
  fputs("\n  ],\n  \"conjuncts\": [\n", out);
  ConjunctWriter writer = {.out = out, .spec = spec, .first = true};
  const struct {
    const char *name;
    const FormulaList *list;
  } blocks[] = {
      {"INITIALLY", &spec->initially}, {"PRESET", &spec->preset},
      {"REQUIRE", &spec->require},     {"ASSERT", &spec->assert_},
      {"ASSUME", &spec->assume},       {"GUARANTEE", &spec->guarantee}};
  for (size_t k = 0; k < sizeof blocks / sizeof *blocks; k++) {
    writer.block = blocks[k].name;
    for (uint32_t i = 0; i < blocks[k].list->count; i++) {
      writer.ordinal = i + 1;
      writer.generated_position = 0;
      emit_conjunct(&writer, blocks[k].list->formulas[i], false);
    }
  }
  fprintf(out, "\n  ],\n  \"ambiguous\": %s\n}\n",
          spec->provenance_ambiguous || writer.unresolved || duplicate_signals
              ? "true"
              : "false");
  return writer.failed || ferror(out) ? -1 : 0;
}
