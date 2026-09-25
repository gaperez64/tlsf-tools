#define _GNU_SOURCE
#include "provenance.h"

#include "tlsf/print_tlsf.h"
#include "yyjson_builder.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

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

static void emit_signal(JsonBuilder *builder, yyjson_mut_val *signals,
                        const SignalDecl *signal, bool is_output) {
  yyjson_mut_val *row = jb_obj(builder);
  jb_push(builder, signals, row);
  JB_STR(builder, row, "name", signal->name);
  JB_STR(builder, row, "direction", is_output ? "output" : "input");
  char id[64];
  snprintf(id, sizeof id, "%s:%u", is_output ? "output" : "input",
           signal->origin_id);
  JB_STR(builder, row, "declaration_id", id);
  JB_STR(builder, row, "source_name", signal->origin_name);
  JB_UINT(builder, row, "dimensions", signal->origin_is_bus ? 1u : 0u);
  yyjson_mut_val *tuple = jb_arr(builder);
  if (signal->origin_is_bus)
    jb_push(builder, tuple, jb_uint(builder, signal->origin_index));
  jb_put(builder, row, "index_tuple", tuple);
  yyjson_mut_val *bounds = jb_arr(builder);
  jb_push(builder, bounds, jb_uint(builder, signal->origin_bus_lo));
  jb_push(builder, bounds, jb_uint(builder, signal->origin_bus_hi));
  jb_put(builder, row, "bounds", bounds);
  JB_UINT(builder, row, "width",
          signal->origin_is_bus
              ? (unsigned)(signal->origin_bus_hi - signal->origin_bus_lo + 1u)
              : 1u);
  const char *width_kind =
      !signal->origin_is_bus          ? "scalar"
      : signal->origin_is_enum        ? "enum-encoding"
      : signal->origin_is_encoded_bit ? "proved-logarithmic-encoding"
      : contains_definition_call(signal->origin_width_expr) ? "derived-width"
                                                            : "range";
  JB_STR(builder, row, "width_kind", width_kind);
  char *expression = signal->origin_width_expr
                         ? formula_text(signal->origin_width_expr)
                         : nullptr;
  if (signal->origin_width_expr && !expression)
    builder->failed = true;
  jb_put(builder, row, "width_expression",
         expression ? jb_str(builder, expression) : jb_null(builder));
  free(expression);
  const char *index_role =
      !signal->origin_is_bus ? "scalar"
      : signal->origin_is_enum || signal->origin_is_encoded_bit
          ? "representation-bit"
      : contains_definition_call(signal->origin_width_expr) ? "undetermined"
                                                            : "element";
  JB_STR(builder, row, "index_role", index_role);
}

typedef struct {
  JsonBuilder *builder;
  yyjson_mut_val *conjuncts;
  const TlsfSpec *spec;
  const char *block;
  uint32_t ordinal;
  uint32_t generated_position;
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
  JsonBuilder *builder = writer->builder;
  yyjson_mut_val *row = jb_obj(builder);
  jb_push(builder, writer->conjuncts, row);
  JB_STR(builder, row, "block", writer->block);
  char id[64];
  snprintf(id, sizeof id, "%s:%u", writer->block, writer->ordinal);
  JB_STR(builder, row, "source_formula_id", id);
  JB_UINT(builder, row, "source_node_id", node->source_id);
  JB_UINT(builder, row, "generated_position", writer->generated_position++);
  JB_STR(builder, row, "formula", text);
  free(text);
  yyjson_mut_val *bindings = jb_arr(builder);
  for (const OriginBinding *binding = node->origin_bindings; binding;
       binding = binding->parent) {
    yyjson_mut_val *item = jb_obj(builder);
    jb_push(builder, bindings, item);
    JB_UINT(builder, item, "binder_id", binding->binder_id);
    JB_STR(builder, item, "name", binding->name);
    JB_SINT(builder, item, "value", binding->value);
  }
  jb_put(builder, row, "bindings", bindings);
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
  yyjson_mut_val *signals = jb_arr(builder);
  for (uint32_t i = 0; i < count; i++) {
    if (!used[i])
      continue;
    const SignalDecl *signal =
        i < writer->spec->input_count
            ? &writer->spec->inputs[i]
            : &writer->spec->outputs[i - writer->spec->input_count];
    jb_push(builder, signals, jb_str(builder, signal->name));
  }
  free(used);
  jb_put(builder, row, "signals", signals);
  JB_BOOL(builder, row, "unresolved_signal_reference", unresolved);
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
  JsonBuilder builder = jb_new();
  yyjson_mut_val *root = jb_obj(&builder);
  JB_STR(&builder, root, "schema", "tlsf-tools.frontend-provenance.v1");
  JB_UINT(&builder, root, "format_version", 1);
  JB_STR(&builder, root, "source_sha256", source_sha256);
  yyjson_mut_val *parameters = jb_arr(&builder);
  for (uint16_t i = 0; i < param_count; i++) {
    yyjson_mut_val *row = jb_obj(&builder);
    jb_push(&builder, parameters, row);
    JB_UINT(&builder, row, "id", (unsigned)i + 1);
    JB_STR(&builder, row, "name", params[i].name);
    JB_SINT(&builder, row, "value", params[i].value);
  }
  jb_put(&builder, root, "parameters", parameters);
  yyjson_mut_val *signals = jb_arr(&builder);
  for (uint32_t i = 0; i < spec->input_count; i++)
    emit_signal(&builder, signals, &spec->inputs[i], false);
  for (uint32_t i = 0; i < spec->output_count; i++)
    emit_signal(&builder, signals, &spec->outputs[i], true);
  jb_put(&builder, root, "signals", signals);
  yyjson_mut_val *conjuncts = jb_arr(&builder);
  ConjunctWriter writer = {
      .builder = &builder, .conjuncts = conjuncts, .spec = spec};
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
  jb_put(&builder, root, "conjuncts", conjuncts);
  JB_BOOL(&builder, root, "ambiguous",
          spec->provenance_ambiguous || writer.unresolved || duplicate_signals);
  builder.failed |= writer.failed;
  return jb_write(&builder, root, out) ? 0 : -1;
}
