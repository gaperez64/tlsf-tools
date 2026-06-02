#ifndef TLSF_JSON_H
#define TLSF_JSON_H

/// json.h — a tiny streaming JSON writer (objects, arrays, scalars) with
/// correct string escaping.  Dependency-light, in the style of print_tlsf.c.
///
/// Object members must be written as json_key(...) followed by exactly one
/// value.  Array elements are written as bare values.

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

enum { JSON_MAX_DEPTH = 64 };

typedef struct {
  FILE *out;
  bool pretty;
  int depth;
  bool after_key;
  bool first[JSON_MAX_DEPTH];
} JsonWriter;

void json_init(JsonWriter *w, FILE *out, bool pretty);
void json_obj_begin(JsonWriter *w);
void json_obj_end(JsonWriter *w);
void json_arr_begin(JsonWriter *w);
void json_arr_end(JsonWriter *w);
void json_key(JsonWriter *w, const char *key);
void json_str(JsonWriter *w, const char *s);
void json_int(JsonWriter *w, int64_t v);
void json_bool(JsonWriter *w, bool v);
void json_null(JsonWriter *w);

#endif // TLSF_JSON_H
