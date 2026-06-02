#include "tlsf/json.h"

void json_init(JsonWriter *w, FILE *out, bool pretty) {
  w->out = out;
  w->pretty = pretty;
  w->depth = 0;
  w->after_key = false;
  w->first[0] = true;
}

static void indent(JsonWriter *w) {
  if (!w->pretty || w->depth == 0)
    return;
  fputc('\n', w->out);
  for (int i = 0; i < w->depth; i++)
    fputs("  ", w->out);
}

// Emitted before any value (scalar or container).  After a key the value sits
// on the same line; otherwise it is a fresh array element / top-level value.
static void pre_value(JsonWriter *w) {
  if (w->after_key) {
    w->after_key = false;
    if (w->pretty)
      fputc(' ', w->out);
    return;
  }
  if (!w->first[w->depth])
    fputc(',', w->out);
  w->first[w->depth] = false;
  indent(w);
}

void json_obj_begin(JsonWriter *w) {
  pre_value(w);
  fputc('{', w->out);
  w->depth++;
  w->first[w->depth] = true;
}

void json_obj_end(JsonWriter *w) {
  bool had = !w->first[w->depth];
  w->depth--;
  if (had)
    indent(w);
  fputc('}', w->out);
}

void json_arr_begin(JsonWriter *w) {
  pre_value(w);
  fputc('[', w->out);
  w->depth++;
  w->first[w->depth] = true;
}

void json_arr_end(JsonWriter *w) {
  bool had = !w->first[w->depth];
  w->depth--;
  if (had)
    indent(w);
  fputc(']', w->out);
}

static void emit_escaped(FILE *out, const char *s) {
  fputc('"', out);
  for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
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
      if (*p < 0x20)
        fprintf(out, "\\u%04x", *p);
      else
        fputc((int)*p, out);
    }
  }
  fputc('"', out);
}

void json_key(JsonWriter *w, const char *key) {
  if (!w->first[w->depth])
    fputc(',', w->out);
  w->first[w->depth] = false;
  indent(w);
  emit_escaped(w->out, key);
  fputc(':', w->out);
  w->after_key = true;
}

void json_str(JsonWriter *w, const char *s) {
  pre_value(w);
  emit_escaped(w->out, s);
}

void json_int(JsonWriter *w, int64_t v) {
  pre_value(w);
  fprintf(w->out, "%lld", (long long)v);
}

void json_bool(JsonWriter *w, bool v) {
  pre_value(w);
  fputs(v ? "true" : "false", w->out);
}

void json_null(JsonWriter *w) {
  pre_value(w);
  fputs("null", w->out);
}
