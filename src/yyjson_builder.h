#ifndef TLSF_YYJSON_BUILDER_H
#define TLSF_YYJSON_BUILDER_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <yyjson.h>

typedef struct {
  yyjson_alc allocator;
  size_t used, limit;
  bool limited;
} JsonBuilderBudget;

typedef struct {
  yyjson_mut_doc *doc;
  JsonBuilderBudget *budget;
  bool failed;
  bool limited;
} JsonBuilder;

static inline void *jb_malloc(void *opaque, size_t size) {
  JsonBuilderBudget *budget = opaque;
  if (size > SIZE_MAX - sizeof(size_t) ||
      size + sizeof(size_t) > budget->limit - budget->used) {
    budget->limited = true;
    return nullptr;
  }
  size_t *block = malloc(size + sizeof(size_t));
  if (!block)
    return nullptr;
  *block = size + sizeof(size_t);
  budget->used += *block;
  return block + 1;
}

static inline void *jb_realloc(void *opaque, void *ptr, size_t old_size,
                               size_t size) {
  (void)old_size;
  if (!ptr)
    return jb_malloc(opaque, size);
  JsonBuilderBudget *budget = opaque;
  size_t *block = (size_t *)ptr - 1;
  size_t old = *block;
  if (size > SIZE_MAX - sizeof(size_t) ||
      size + sizeof(size_t) > budget->limit - (budget->used - old)) {
    budget->limited = true;
    return nullptr;
  }
  size_t *grown = realloc(block, size + sizeof(size_t));
  if (!grown)
    return nullptr;
  *grown = size + sizeof(size_t);
  budget->used = budget->used - old + *grown;
  return grown + 1;
}

static inline void jb_free(void *opaque, void *ptr) {
  if (!ptr)
    return;
  JsonBuilderBudget *budget = opaque;
  size_t *block = (size_t *)ptr - 1;
  budget->used -= *block;
  free(block);
}

static inline JsonBuilder jb_new(void) {
  JsonBuilder builder = {.doc = yyjson_mut_doc_new(nullptr)};
  builder.failed = !builder.doc;
  return builder;
}

static inline JsonBuilder jb_new_bounded(size_t artifact_cap) {
  if (!artifact_cap || artifact_cap == SIZE_MAX)
    return jb_new();
  JsonBuilder builder = {0};
  builder.budget = calloc(1, sizeof *builder.budget);
  if (!builder.budget) {
    builder.failed = true;
    return builder;
  }
  builder.budget->limit = artifact_cap > (SIZE_MAX - 4096) / 16
                              ? SIZE_MAX
                              : artifact_cap * 16 + 4096;
  builder.budget->allocator = (yyjson_alc){.malloc = jb_malloc,
                                           .realloc = jb_realloc,
                                           .free = jb_free,
                                           .ctx = builder.budget};
  builder.doc = yyjson_mut_doc_new(&builder.budget->allocator);
  builder.failed = !builder.doc;
  return builder;
}

static inline yyjson_mut_val *jb_obj(JsonBuilder *builder) {
  yyjson_mut_val *value = builder->doc ? yyjson_mut_obj(builder->doc) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_arr(JsonBuilder *builder) {
  yyjson_mut_val *value = builder->doc ? yyjson_mut_arr(builder->doc) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_str(JsonBuilder *builder, const char *text) {
  yyjson_mut_val *value =
      text && builder->doc ? yyjson_mut_strcpy(builder->doc, text) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_uint(JsonBuilder *builder, uint64_t number) {
  yyjson_mut_val *value =
      builder->doc ? yyjson_mut_uint(builder->doc, number) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_sint(JsonBuilder *builder, int64_t number) {
  yyjson_mut_val *value =
      builder->doc ? yyjson_mut_sint(builder->doc, number) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_real(JsonBuilder *builder, double number) {
  yyjson_mut_val *value =
      builder->doc ? yyjson_mut_real(builder->doc, number) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_bool(JsonBuilder *builder, bool boolean) {
  yyjson_mut_val *value =
      builder->doc ? yyjson_mut_bool(builder->doc, boolean) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline yyjson_mut_val *jb_null(JsonBuilder *builder) {
  yyjson_mut_val *value =
      builder->doc ? yyjson_mut_null(builder->doc) : nullptr;
  builder->failed |= !value;
  return value;
}

static inline void jb_put(JsonBuilder *builder, yyjson_mut_val *object,
                          const char *name, yyjson_mut_val *value) {
  yyjson_mut_val *key =
      builder->doc && name ? yyjson_mut_strcpy(builder->doc, name) : nullptr;
  if (!object || !key || !value || !yyjson_mut_obj_add(object, key, value))
    builder->failed = true;
}

static inline void jb_push(JsonBuilder *builder, yyjson_mut_val *array,
                           yyjson_mut_val *value) {
  if (!array || !value || !yyjson_mut_arr_append(array, value))
    builder->failed = true;
}

#define JB_STR(b, o, k, v) jb_put((b), (o), (k), jb_str((b), (v)))
#define JB_UINT(b, o, k, v) jb_put((b), (o), (k), jb_uint((b), (v)))
#define JB_SINT(b, o, k, v) jb_put((b), (o), (k), jb_sint((b), (v)))
#define JB_BOOL(b, o, k, v) jb_put((b), (o), (k), jb_bool((b), (v)))

static inline bool jb_write(JsonBuilder *builder, yyjson_mut_val *root,
                            FILE *stream) {
  if (!builder->failed && root) {
    yyjson_mut_doc_set_root(builder->doc, root);
    size_t size = 0;
    char *bytes =
        builder->budget
            ? yyjson_mut_write_opts(builder->doc, 0,
                                    &builder->budget->allocator, &size, nullptr)
            : yyjson_mut_write(builder->doc, 0, &size);
    if (!bytes)
      builder->failed = true;
    else {
      if (fwrite(bytes, 1, size, stream) != size || fputc('\n', stream) == EOF)
        builder->failed = true;
      if (builder->budget)
        jb_free(builder->budget, bytes);
      else
        free(bytes);
    }
  }
  yyjson_mut_doc_free(builder->doc);
  builder->doc = nullptr;
  if (builder->budget) {
    builder->limited = builder->budget->limited;
    free(builder->budget);
    builder->budget = nullptr;
  }
  return !builder->failed && !ferror(stream);
}

#endif
