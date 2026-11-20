#define _GNU_SOURCE
#include "provenance.h"
#include "arena_budget.h"
#include "frontend_stream.h"
#include "spec_internal.h"

#include "tlsf/print_tlsf.h"
#include "yyjson_builder.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static char *formula_text(Arena *arena, const Node *node) {
  char *buf = nullptr;
  size_t size = 0;
  FILE *stream = frontend_memstream(arena, &buf, &size);
  if (!stream)
    return nullptr;
  if (arena->cancelled)
    print_tlsf_formula_checked(stream, node, arena);
  else
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

static void mark_aps(Arena *arena, const Node *node, const SignalDecl *inputs,
                     uint32_t ninputs, const SignalDecl *outputs,
                     uint32_t noutputs, bool *used, bool *unresolved) {
  if (!node || !arena_check_budget(arena, 0))
    return;
  switch (node->kind) {
  case NODE_AP: {
    uint32_t matches = 0;
    for (uint32_t i = 0; i < ninputs; i++) {
      if (!arena_check_budget(arena, 0))
        return;
      if (strcmp(inputs[i].name, node->name) == 0) {
        used[i] = true;
        matches++;
      }
    }
    for (uint32_t i = 0; i < noutputs; i++) {
      if (!arena_check_budget(arena, 0))
        return;
      if (strcmp(outputs[i].name, node->name) == 0) {
        used[ninputs + i] = true;
        matches++;
      }
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
    mark_aps(arena, node->arg, inputs, ninputs, outputs, noutputs, used,
             unresolved);
    return;
  default:
    mark_aps(arena, node->lhs, inputs, ninputs, outputs, noutputs, used,
             unresolved);
    mark_aps(arena, node->rhs, inputs, ninputs, outputs, noutputs, used,
             unresolved);
    return;
  }
}

// Resolve integer leaves through source definitions to parameter declarations.
// Unknown leaves decline ownership inference; printed expressions are never
// used as bindings.
typedef struct WidthEnv {
  const struct WidthEnv *parent;
  const DefDecl *definition;
  Node *const *actuals;
} WidthEnv;

typedef struct {
  Arena *arena;
  const ParamDecl *params;
  uint16_t param_count;
  const DefDecl *defs;
  uint16_t def_count;
} WidthSource;

static bool width_dependencies(const Node *node, const WidthSource *spec,
                               const WidthEnv *env, bool *used,
                               unsigned depth) {
  if (!node)
    return true;
  if (!arena_check_budget(spec->arena, 0) || depth > 64)
    return false;
  switch (node->kind) {
  case NODE_INT:
  case NODE_TRUE:
  case NODE_FALSE:
    return true;
  case NODE_INT_VAR:
  case NODE_AP: {
    // Definitions are top-level: their bodies see their own formals and
    // global parameters, not formals from the definition that called them.
    if (env)
      for (uint16_t i = 0; i < env->definition->param_count; i++)
        if (strcmp(node->name, env->definition->params[i]) == 0)
          return width_dependencies(env->actuals[i], spec, env->parent, used,
                                    depth + 1);
    for (uint16_t i = 0; i < spec->param_count; i++)
      if (strcmp(node->name, spec->params[i].name) == 0) {
        used[i] = true;
        return true;
      }
    for (uint16_t i = 0; i < spec->def_count; i++)
      if (spec->defs[i].param_count == 0 &&
          strcmp(node->name, spec->defs[i].name) == 0) {
        const WidthEnv nested = {env, &spec->defs[i], nullptr};
        for (const WidthEnv *parent = env; parent; parent = parent->parent)
          if (parent->definition == nested.definition)
            return false;
        return width_dependencies(spec->defs[i].body, spec, &nested, used,
                                  depth + 1);
      }
    return false;
  }
  case NODE_DEF_CALL: {
    const DefDecl *definition = nullptr;
    for (uint16_t i = 0; i < spec->def_count; i++)
      if (spec->defs[i].param_count == node->call_argc &&
          strcmp(node->callee, spec->defs[i].name) == 0) {
        definition = &spec->defs[i];
        break;
      }
    if (!definition)
      return false;
    for (const WidthEnv *parent = env; parent; parent = parent->parent)
      if (parent->definition == definition)
        return false;
    const WidthEnv nested = {env, definition, node->call_args};
    return width_dependencies(definition->body, spec, &nested, used, depth + 1);
  }
  case NODE_INT_NEG:
  case NODE_NOT:
    return width_dependencies(node->arg, spec, env, used, depth + 1);
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
  case NODE_CMP_EQ:
  case NODE_CMP_NE:
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE:
  case NODE_AND:
  case NODE_OR:
    return width_dependencies(node->lhs, spec, env, used, depth + 1) &&
           width_dependencies(node->rhs, spec, env, used, depth + 1);
  case NODE_ITE:
    return width_dependencies(node->if_cond, spec, env, used, depth + 1) &&
           width_dependencies(node->if_then, spec, env, used, depth + 1) &&
           width_dependencies(node->if_else, spec, env, used, depth + 1);
  default:
    return false;
  }
}

static void emit_signal(JsonBuilder *builder, yyjson_mut_val *signals,
                        const SignalDecl *signal, bool is_output,
                        const WidthSource *source) {
  if (!arena_check_budget(source->arena, 0)) {
    builder->failed = true;
    return;
  }
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
  char *expression =
      signal->origin_width_expr
          ? formula_text(source->arena, signal->origin_width_expr)
          : nullptr;
  if (signal->origin_width_expr && !expression)
    builder->failed = true;
  jb_put(builder, row, "width_expression",
         expression ? jb_str(builder, expression) : jb_null(builder));
  free(expression);
  if (!arena_check_budget(source->arena, source->param_count + 1u)) {
    builder->failed = true;
    return;
  }
  bool *used =
      calloc(source->param_count ? source->param_count : 1, sizeof *used);
  if (!used) {
    builder->failed = true;
    return;
  }
  bool complete =
      width_dependencies(signal->bus_lo_expr, source, nullptr, used, 0) &&
      width_dependencies(signal->origin_width_expr, source, nullptr, used, 0);
  yyjson_mut_val *parameter_ids = jb_arr(builder);
  for (uint16_t i = 0; i < source->param_count; i++)
    if (used[i])
      jb_push(builder, parameter_ids, jb_uint(builder, (unsigned)i + 1));
  jb_put(builder, row, "width_parameter_ids", parameter_ids);
  JB_BOOL(builder, row, "width_binding_complete", complete);
  free(used);
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
  if (writer->failed || !arena_check_budget(writer->spec->arena, 0)) {
    writer->failed = true;
    return;
  }
  if (writer->builder->failed)
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
  char *text = formula_text(writer->spec->arena, formula);
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
  if (!arena_check_budget(writer->spec->arena, (size_t)count + 1)) {
    writer->failed = true;
    return;
  }
  bool *used = calloc(count ? count : 1, sizeof *used);
  if (!used) {
    writer->failed = true;
    return;
  }
  bool unresolved = false;
  mark_aps(writer->spec->arena, formula, writer->spec->inputs,
           writer->spec->input_count, writer->spec->outputs,
           writer->spec->output_count, used, &unresolved);
  if (unresolved)
    writer->unresolved = true;
  yyjson_mut_val *signals = jb_arr(builder);
  for (uint32_t i = 0; i < count; i++) {
    if (!arena_check_budget(writer->spec->arena, 0)) {
      writer->failed = true;
      break;
    }
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

static void *provenance_malloc(void *raw, size_t size) {
  Arena *arena = raw;
  return arena_check_budget(arena, size) ? malloc(size) : nullptr;
}

static void *provenance_realloc(void *raw, void *ptr, size_t old, size_t size) {
  (void)old;
  Arena *arena = raw;
  return arena_check_budget(arena, size) ? realloc(ptr, size) : nullptr;
}

static void provenance_free(void *raw, void *ptr) {
  (void)raw;
  free(ptr);
}

// yyjson's whole-document writer has no traversal callback. Stream containers
// ourselves so even serialization with no allocator growth remains
// interruptible.
static bool provenance_json(FILE *out, yyjson_mut_val *value,
                            const yyjson_alc *allocator) {
  if (!arena_check_budget(allocator->ctx, 0))
    return false;
  if (yyjson_mut_is_arr(value)) {
    if (fputc('[', out) == EOF)
      return false;
    size_t i, count;
    yyjson_mut_val *item;
    yyjson_mut_arr_foreach(value, i, count, item) {
      if ((i && fputc(',', out) == EOF) ||
          !provenance_json(out, item, allocator))
        return false;
    }
    return fputc(']', out) != EOF;
  }
  if (yyjson_mut_is_obj(value)) {
    if (fputc('{', out) == EOF)
      return false;
    size_t i, count;
    yyjson_mut_val *key, *item;
    yyjson_mut_obj_foreach(value, i, count, key, item) {
      if ((i && fputc(',', out) == EOF) ||
          !provenance_json(out, key, allocator) || fputc(':', out) == EOF ||
          !provenance_json(out, item, allocator))
        return false;
    }
    return fputc('}', out) != EOF;
  }
  if (yyjson_mut_is_str(value)) {
    const char *data = yyjson_mut_get_str(value);
    size_t remaining = yyjson_mut_get_len(value);
    if (fputc('"', out) == EOF)
      return false;
    while (remaining) {
      size_t count = remaining < 4096 ? remaining : 4096;
      // Keep a UTF-8 code point together across serialization chunks.
      while (count < remaining && count &&
             ((unsigned char)data[count] & 0xc0) == 0x80)
        --count;
      if (!count)
        return false;
      yyjson_mut_val part = {0};
      yyjson_mut_set_strn(&part, data, count);
      size_t size = 0;
      char *bytes =
          yyjson_mut_val_write_opts(&part, 0, allocator, &size, nullptr);
      if (!bytes)
        return false;
      bool ok = fwrite(bytes + 1, 1, size - 2, out) == size - 2;
      free(bytes);
      if (!ok)
        return false;
      data += count;
      remaining -= count;
    }
    return fputc('"', out) != EOF;
  }
  size_t size = 0;
  char *bytes = yyjson_mut_val_write_opts(value, 0, allocator, &size, nullptr);
  if (!bytes)
    return false;
  bool ok = fwrite(bytes, 1, size, out) == size;
  free(bytes);
  return ok;
}

int provenance_write(FILE *out, const TlsfSpec *spec, const ParamDecl *params,
                     uint16_t param_count, const DefDecl *defs,
                     uint16_t def_count, const char source_sha256[65]) {
  const WidthSource width_source = {spec->arena, params, param_count, defs,
                                    def_count};
  bool duplicate_signals = false;
  for (uint32_t i = 0; i < spec->input_count + spec->output_count; i++) {
    const SignalDecl *left = i < spec->input_count
                                 ? &spec->inputs[i]
                                 : &spec->outputs[i - spec->input_count];
    for (uint32_t j = 0; j < i; j++) {
      if (!arena_check_budget(spec->arena, 0))
        return -1;
      const SignalDecl *right = j < spec->input_count
                                    ? &spec->inputs[j]
                                    : &spec->outputs[j - spec->input_count];
      if (strcmp(left->name, right->name) == 0)
        duplicate_signals = true;
    }
  }
  yyjson_alc allocator = {.malloc = provenance_malloc,
                          .realloc = provenance_realloc,
                          .free = provenance_free,
                          .ctx = spec->arena};
  JsonBuilder builder =
      spec->arena->cancelled
          ? (JsonBuilder){.doc = yyjson_mut_doc_new(&allocator)}
          : jb_new();
  builder.failed |= !builder.doc;
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
  for (uint32_t i = 0; i < spec->input_count && !builder.failed; i++)
    emit_signal(&builder, signals, &spec->inputs[i], false, &width_source);
  for (uint32_t i = 0; i < spec->output_count && !builder.failed; i++)
    emit_signal(&builder, signals, &spec->outputs[i], true, &width_source);
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
    for (uint32_t i = 0;
         i < blocks[k].list->count && !writer.failed && !builder.failed; i++) {
      writer.ordinal = i + 1;
      writer.generated_position = 0;
      emit_conjunct(&writer, blocks[k].list->formulas[i], false);
    }
  }
  jb_put(&builder, root, "conjuncts", conjuncts);
  JB_BOOL(&builder, root, "ambiguous",
          spec->provenance_ambiguous || writer.unresolved || duplicate_signals);
  builder.failed |= writer.failed || arena_failed(spec->arena);
  if (!spec->arena->cancelled)
    return jb_write(&builder, root, out) ? 0 : -1;
  bool ok = !builder.failed && provenance_json(out, root, &allocator) &&
            fputc('\n', out) != EOF;
  yyjson_mut_doc_free(builder.doc);
  return ok ? 0 : -1;
}
