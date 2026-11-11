#define _GNU_SOURCE
#include <errno.h>
#include "conversion_internal.h"
#include "section_pattern.h"
#include "rewrite.h"
#include "templates_internal.h"
#include "tlsf/ast_api.h"
#include "tlsf/convert.h"
#include "tlsf/pipeline.h"
#include "tlsf/print_tlsf.h"
#include <yyjson.h>

// Keep the gate active in release builds too.
#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #condition);          \
      abort();                                                                 \
    }                                                                          \
  } while (0)
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static size_t fail_at, allocations, match_size;
static bool armed, fired, fail_slab, assembly_only;
static bool rewrite_only, cover_only, composition_only;
static bool composition_arena_only;
static bool slab_at_assembly;
static bool heap_after_assembly, heap_armed;
static size_t heap_at, heap_count;

static bool heap_fault(void) {
  if (!heap_armed)
    return false;
  if (++heap_count != heap_at)
    return false;
  fired = true;
  return true;
}

void *__real_malloc(size_t);
void *__wrap_malloc(size_t);
void *__wrap_malloc(size_t n) {
  return heap_fault() ? nullptr : __real_malloc(n);
}
void *__real_calloc(size_t, size_t);
void *__wrap_calloc(size_t, size_t);
void *__wrap_calloc(size_t n, size_t size) {
  return heap_fault() ? nullptr : __real_calloc(n, size);
}
void *__real_realloc(void *, size_t);
void *__wrap_realloc(void *, size_t);
void *__wrap_realloc(void *p, size_t n) {
  return heap_fault() ? nullptr : __real_realloc(p, n);
}
// An unbuffered proxy exercises real stdio failures, including writes that
// occur inside libc. Fail only once, then allow all later writes and close.
static bool stream_armed;
static size_t stream_at, stream_count;
static FILE *stream_target;
static ssize_t stream_write(void *cookie, const char *buf, size_t size) {
  (void)cookie;
  if (++stream_count == stream_at) {
    fired = true;
    errno = ENOMEM;
    return -1;
  }
  return (ssize_t)fwrite(buf, 1, size, stream_target);
}
static int stream_close(void *cookie) {
  (void)cookie;
  return fclose(stream_target);
}
FILE *__real_open_memstream(char **, size_t *);
FILE *__wrap_open_memstream(char **, size_t *);
FILE *__wrap_open_memstream(char **buf, size_t *size) {
  if (heap_fault())
    return nullptr;
  FILE *ms = __real_open_memstream(buf, size);
  if (!ms || !stream_armed)
    return ms;
  stream_target = ms;
  FILE *proxy = fopencookie(
      nullptr, "w",
      (cookie_io_functions_t){.write = stream_write, .close = stream_close});
  CHECK(proxy);
  int rc = setvbuf(proxy, nullptr, _IONBF, 0);
  CHECK(rc == 0);
  return proxy;
}
FILE *__real_fmemopen(void *, size_t, const char *);
FILE *__wrap_fmemopen(void *, size_t, const char *);
FILE *__wrap_fmemopen(void *buf, size_t size, const char *mode) {
  return heap_fault() ? nullptr : __real_fmemopen(buf, size, mode);
}
// glibc's memory stream can return EOF while leaving ferror clear. Model that
// independently of its buffer sizes, so a later successful write cannot hide
// it.
static size_t char_at, char_count;
static size_t write_at, write_count;
static FILE *write_target;
static bool write_fault(FILE *out) {
  if (out != write_target || ++write_count != write_at)
    return false;
  fired = true;
  errno = ENOMEM;
  CHECK(!ferror(out));
  return true;
}
int __wrap_fprintf(FILE *, const char *, ...);
int __wrap_fprintf(FILE *out, const char *fmt, ...) {
  if (write_fault(out))
    return -1;
  va_list args;
  va_start(args, fmt);
  int rc = vfprintf(out, fmt, args);
  va_end(args);
  return rc;
}
#ifdef __GLIBC__
// Ubuntu enables _FORTIFY_SOURCE by default in optimized builds. Its stdio
// headers redirect fprintf to __fprintf_chk, bypassing the ordinary wrapper.
// Keep the same one-shot failure without setting the FILE error indicator,
// and preserve fortification on successful writes.
int __vfprintf_chk(FILE *, int, const char *, va_list);
int __wrap___fprintf_chk(FILE *, int, const char *, ...);
int __wrap___fprintf_chk(FILE *out, int flag, const char *fmt, ...) {
  if (write_fault(out))
    return -1;
  va_list args;
  va_start(args, fmt);
  int rc = __vfprintf_chk(out, flag, fmt, args);
  va_end(args);
  return rc;
}
#endif
int __real_fputs(const char *, FILE *);
int __wrap_fputs(const char *, FILE *);
int __wrap_fputs(const char *s, FILE *out) {
  return write_fault(out) ? EOF : __real_fputs(s, out);
}
int __real_fputc(int, FILE *);
int __wrap_fputc(int, FILE *);
int __wrap_fputc(int c, FILE *out) {
  if (write_fault(out))
    return EOF;
  if (char_at && ++char_count == char_at) {
    fired = true;
    CHECK(!ferror(out));
    return EOF;
  }
  return __real_fputc(c, out);
}

bool tlsf_arena_fault(size_t size, bool slab);
bool tlsf_arena_fault(size_t size, bool slab) {
  if (slab) {
    if (!fail_slab)
      return false;
    fail_slab = false;
    fired = true;
    return true;
  }
  if (!armed)
    return false;
  ++allocations;
  if ((fail_at && allocations == fail_at) ||
      (match_size && size == match_size)) {
    match_size = 0;
    fired = true;
    return true;
  }
  return false;
}

Node *__real_build_spec_formula(const TlsfSpec *, const ClassifiedSpec *,
                                PrintMode);
Node *__wrap_build_spec_formula(const TlsfSpec *, const ClassifiedSpec *,
                                PrintMode);
Node *__wrap_build_spec_formula(const TlsfSpec *spec, const ClassifiedSpec *cs,
                                PrintMode mode) {
  if (assembly_only) {
    armed = true;
    allocations = 0;
  }
  if (slab_at_assembly) {
    fail_slab = true;
    CHECK(!arena_alloc_aligned(spec->arena, 2 * ARENA_DEFAULT_SLAB_SIZE, 1));
    CHECK(arena_alloc_aligned(spec->arena, 1, 1));
    CHECK(arena_failed(spec->arena));
  }
  Node *root = __real_build_spec_formula(spec, cs, mode);
  if (heap_after_assembly)
    heap_armed = true;
  if (assembly_only)
    armed = false;
  if (rewrite_only) {
    armed = true;
    allocations = 0;
  }
  return root;
}

ConstraintCover *__real_cover_build(TlsfSpec *, bool);
ConstraintCover *__wrap_cover_build(TlsfSpec *, bool);
ConstraintCover *__wrap_cover_build(TlsfSpec *spec, bool split) {
  if (cover_only) {
    armed = true;
    allocations = 0;
  }
  ConstraintCover *cov = __real_cover_build(spec, split);
  if (cover_only)
    armed = false;
  return cov;
}

CsnfComposition *__real_csnf_compose(const Csnf *);
CsnfComposition *__wrap_csnf_compose(const Csnf *);
CsnfComposition *__wrap_csnf_compose(const Csnf *c) {
  if (composition_only)
    heap_armed = true;
  if (composition_arena_only) {
    CHECK(!arena_failed(c->cov->arena));
    armed = true;
    allocations = 0;
  }
  CsnfComposition *r = __real_csnf_compose(c);
  if (composition_only)
    heap_armed = false;
  if (composition_arena_only) {
    armed = false;
    CHECK(!fired || (arena_failed(c->cov->arena) && !r));
  }
  return r;
}

static void reset(size_t nth) {
  fail_at = nth;
  allocations = match_size = 0;
  armed = true;
  fired = fail_slab = assembly_only = slab_at_assembly = false;
  rewrite_only = cover_only = composition_only = false;
  composition_arena_only = false;
  heap_after_assembly = heap_armed = false;
  heap_at = heap_count = 0;
  stream_armed = false;
  stream_at = stream_count = char_at = char_count = 0;
  write_target = nullptr;
  write_at = write_count = 0;
}

static void heap_sweep(const char *source, bool frontend) {
  reset(0);
  heap_after_assembly = !frontend;
  heap_armed = frontend;
  TlsfConversionResult *r = tlsf_convert(source, nullptr);
  CHECK(r);
  size_t count = heap_count;
  char *expected = strdup(r->preprocessed_ltl);
  CHECK(expected);
  tlsf_conversion_result_free(r);
  CHECK(count);
  for (size_t n = 1; n <= count; ++n) {
    reset(0);
    heap_after_assembly = !frontend;
    heap_armed = frontend;
    heap_at = n;
    r = tlsf_convert(source, nullptr);
    if (!fired || r)
      fprintf(stderr, "heap n=%zu/%zu, result=%p\n", n, count, (void *)r);
    CHECK(fired && !r);
  }
  reset(0);
  r = tlsf_convert(source, nullptr);
  CHECK(r && !strcmp(r->preprocessed_ltl, expected));
  tlsf_conversion_result_free(r);
  free(expected);
}

int objective_cli_main(int argc, char **argv);
static void cli_checks(const char *source, const char *expected, size_t count,
                       bool rewriting) {
  reset(0);
  FILE *in = tmpfile(), *out = tmpfile(), *err = tmpfile();
  CHECK(in && out && err);
  fputs(source, in);
  fflush(in);
  char input[64], output[64];
  snprintf(input, sizeof input, "/proc/self/fd/%d", fileno(in));
  snprintf(output, sizeof output, "/proc/self/fd/%d", fileno(out));
  char *argv[] = {"objective-cli",
                  "--output",
                  output,
                  input,
                  rewriting ? "--weak-simplify" : nullptr,
                  nullptr};
  int saved_stderr = dup(STDERR_FILENO);
  CHECK(saved_stderr >= 0 && dup2(fileno(err), STDERR_FILENO) >= 0);
  for (size_t n = 1; n <= count; ++n) {
    reset(n);
    armed = false;
    assembly_only = !rewriting;
    rewrite_only = rewriting;
    int rc = objective_cli_main(rewriting ? 5 : 4, argv);
    CHECK(rc != 0 && fired);
    CHECK(fseek(out, 0, SEEK_END) == 0 && ftell(out) == 0);
  }
  fflush(stderr);
  CHECK(dup2(saved_stderr, STDERR_FILENO) >= 0);
  close(saved_stderr);
  rewind(err);
  char diagnostic[256];
  CHECK(fgets(diagnostic, sizeof diagnostic, err));
  CHECK(strstr(diagnostic,
               rewriting ? "transform failed" : "objective assembly failed"));
  reset(0);
  int rc = objective_cli_main(rewriting ? 5 : 4, argv);
  CHECK(rc == 0);
  rewind(out);
  char text[256];
  CHECK(fgets(text, sizeof text, out));
  text[strcspn(text, "\n")] = '\0';
  CHECK(!strcmp(text, expected));
  fclose(in);
  fclose(out);
  fclose(err);
}

// These objectives are propositional. Exhaust both valuations independently of
// the serialized text, so a corrupted root cannot serve as its own oracle.
static bool eval(const Node *n, bool p) {
  CHECK(n);
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_FALSE:
    return false;
  case NODE_AP:
    return p;
  case NODE_NOT:
    return !eval(n->arg, p);
  case NODE_AND:
    return eval(n->lhs, p) && eval(n->rhs, p);
  default:
    abort();
  }
}

static void healthy(const char *source, const char *expected) {
  reset(0);
  TlsfConversionResult *r = tlsf_convert(source, nullptr);
  CHECK(r && !strcmp(r->preprocessed_ltl, expected));
  tlsf_conversion_result_free(r);
}

static void conversion_sweep(const char *source, const char *expected) {
  reset(0);
  TlsfConversionResult *r = tlsf_convert(source, nullptr);
  CHECK(r && !strcmp(r->preprocessed_ltl, expected));
  size_t count = allocations;
  tlsf_conversion_result_free(r);
  for (size_t n = 1; n <= count; ++n) {
    reset(n);
    r = tlsf_convert(source, nullptr);
    CHECK(fired && !r); // A null result publishes neither text nor AST.
    healthy(source, expected);
  }
  reset(count + 1);
  r = tlsf_convert(source, nullptr);
  CHECK(!fired && r && !strcmp(r->preprocessed_ltl, expected));
  tlsf_conversion_result_free(r);
}

static TlsfSpec *prepared(const char *source, ClassifiedSpec **cs) {
  reset(0);
  FILE *fp = fmemopen((void *)source, strlen(source), "r");
  CHECK(fp);
  TlsfSpec *spec = spec_parse(fp, "objective-alloc");
  fclose(fp);
  CHECK(spec);
  bool ok = conversion_prepare(spec, nullptr, nullptr, nullptr, 0, false,
                               "objective-alloc");
  CHECK(ok);
  *cs = classify_spec(spec);
  CHECK(*cs);
  return spec;
}

static void adaptation_checks(void) {
  // Share an operator both within a formula and across all six sections.
  // Every failed allocation must leave every original slot untouched.
  for (unsigned moore = 0; moore < 2; ++moore) {
    size_t count = 0;
    for (size_t nth = 0; nth <= count; ++nth) {
      reset(0);
      TlsfSpec *s = spec_new();
      CHECK(s);
      s->info.semantics = moore ? SEM_MOORE : SEM_MEALY;
      s->info.target = moore ? TARGET_MEALY : TARGET_MOORE;
      const char *name = intern(s->intern, "p");
      CHECK(name);
      CHECK(spec_add_signal(s, !moore, name, false, nullptr, nullptr));
      Node *atom = node_ap(s->arena, name);
      Node *shared = node_not(s->arena, atom);
      Node *root = node_and(s->arena, shared, shared);
      CHECK(root);
      FormulaList *lists[] = {&s->initially, &s->require, &s->assume,
                              &s->preset,    &s->assert_, &s->guarantee};
      for (size_t k = 0; k < sizeof lists / sizeof *lists; ++k) {
        CHECK(formula_list_push(s, lists[k], root));
        CHECK(formula_list_push(s, lists[k], atom));
      }
      reset(nth);
      bool ok = spec_adapt_target(s);
      armed = false;
      CHECK(root->lhs == shared && root->rhs == shared);
      if (!nth) {
        count = allocations;
        CHECK(ok && !fired && count);
        CHECK(shared->arg->kind == NODE_X && shared->arg->arg == atom);
        char *text = conversion_render_ltl(root, LTL_FMT_LTLXBA, false, false);
        CHECK(text && !strcmp(text, "!X p && !X p"));
        free(text);
      } else {
        CHECK(!ok && fired && allocations == nth);
        CHECK(shared->arg == atom);
        CHECK(!spec_adapt_target(s));
      }
      for (size_t k = 0; k < sizeof lists / sizeof *lists; ++k) {
        CHECK(lists[k]->formulas[0] == root);
        Node *f = lists[k]->formulas[1];
        CHECK(nth ? f == atom : f->kind == NODE_X && f->arg == atom);
      }
      CHECK(atom->kind == NODE_AP && atom->name == name);
      spec_free(s);
    }
  }
  reset(0);
}

static char *expansion_text(const TlsfSpec *spec) {
  char *text = nullptr;
  size_t size = 0;
  FILE *out = open_memstream(&text, &size);
  CHECK(out);
  print_tlsf(out, spec, true);
  CHECK(fclose(out) == 0 && text);
  return text;
}

static void snapshot_node(FILE *out, const Node *n) {
  if (!n)
    return;
  CHECK(fwrite(n, sizeof *n, 1, out) == 1);
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_INT:
  case NODE_AP:
  case NODE_INT_VAR:
  case NODE_SIZEOF:
    break;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
  case NODE_INT_NEG:
  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    snapshot_node(out, n->arg);
    break;
  case NODE_BUS_INDEX:
    snapshot_node(out, n->bus_index);
    break;
  case NODE_DEF_CALL:
  case NODE_PATTERN:
    for (uint16_t i = 0; i < n->call_argc; ++i)
      snapshot_node(out, n->call_args[i]);
    break;
  case NODE_ITE:
    snapshot_node(out, n->if_cond);
    snapshot_node(out, n->if_then);
    snapshot_node(out, n->if_else);
    break;
  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER:
  case NODE_G_RANGE:
  case NODE_F_RANGE:
    snapshot_node(out, n->qlo);
    snapshot_node(out, n->qhi);
    if (n->kind != NODE_G_RANGE && n->kind != NODE_F_RANGE)
      snapshot_node(out, n->qset);
    snapshot_node(out, n->qbody);
    break;
  case NODE_SET:
  case NODE_SET_ENUM:
    for (uint16_t i = 0; i < n->set_size; ++i)
      snapshot_node(out, n->set_elems[i]);
    break;
  default:
    snapshot_node(out, n->lhs);
    snapshot_node(out, n->rhs);
    break;
  }
  snapshot_node(out, n->bounded.body);
}

// Printing omits source IDs, bindings and bounded metadata. Capture the raw
// source nodes too, including definitions and signal-bound expressions.
static char *expansion_nodes(const TlsfSpec *spec, size_t *size) {
  char *data = nullptr;
  FILE *out = open_memstream(&data, size);
  CHECK(out);
  for (uint16_t i = 0; i < spec->def_count; ++i)
    snapshot_node(out, spec->defs[i].body);
  const FormulaList *lists[] = {&spec->initially, &spec->preset,
                                &spec->require,   &spec->assert_,
                                &spec->assume,    &spec->guarantee};
  for (size_t k = 0; k < sizeof lists / sizeof *lists; ++k)
    for (uint32_t i = 0; i < lists[k]->count; ++i)
      snapshot_node(out, lists[k]->formulas[i]);
  const SignalDecl *signals[] = {spec->inputs, spec->outputs};
  const uint32_t counts[] = {spec->input_count, spec->output_count};
  for (size_t k = 0; k < 2; ++k)
    for (uint32_t i = 0; i < counts[k]; ++i) {
      snapshot_node(out, signals[k][i].bus_lo_expr);
      snapshot_node(out, signals[k][i].bus_hi_expr);
    }
  CHECK(fclose(out) == 0 && data);
  return data;
}

static void expansion_sweep(const char *source, bool semantic_error,
                            bool preexisting_id) {
  for (unsigned provenance = 0; provenance < 2; ++provenance) {
    size_t count = 0;
    for (size_t nth = 0; nth <= count + 1; ++nth) {
      reset(0);
      FILE *fp = fmemopen((void *)source, strlen(source), "r");
      CHECK(fp);
      TlsfSpec *s = spec_parse(fp, "expansion-alloc");
      fclose(fp);
      CHECK(s);
      s->capture_provenance = provenance;
      if (preexisting_id) {
        Node *call = s->guarantee.formulas[0];
        CHECK(call->kind == NODE_DEF_CALL && call->call_argc == 1);
        CHECK(call->call_args[0]->source_id == 0);
        call->source_id = 73;
      }
      armed = false;
      TlsfSpec before;
      memcpy(&before, s, sizeof before);
      char *original = expansion_text(s);
      size_t original_size = 0;
      char *original_nodes = expansion_nodes(s, &original_size);
      const ParamOverride override = {.name = "N", .value = 2};
      reset(nth);
      int rc = expand(s, &override, s->param_count ? 1 : 0);
      armed = false;
      if (!nth || nth == count + 1) {
        CHECK((rc != 0) == semantic_error);
        CHECK(!fired && !arena_failed(s->arena));
        if (!nth) {
          count = allocations;
          CHECK(count);
        }
        for (uint32_t i = 0; i < s->input_count; ++i)
          CHECK(s->inputs[i].name);
        for (uint32_t i = 0; i < s->output_count; ++i)
          CHECK(s->outputs[i].name);
      } else {
        CHECK(rc != 0 && fired && allocations == nth);
        CHECK(arena_failed(s->arena));
      }
      if (rc != 0) {
        for (unsigned repeat = 0; repeat < 3; ++repeat) {
          CHECK(!memcmp(s, &before, sizeof before));
          char *after = expansion_text(s);
          CHECK(!strcmp(original, after));
          free(after);
          size_t after_size = 0;
          char *after_nodes = expansion_nodes(s, &after_size);
          CHECK(original_size == after_size);
          CHECK(!memcmp(original_nodes, after_nodes, original_size));
          free(after_nodes);
          if (repeat < 2)
            CHECK(expand(s, &override, s->param_count ? 1 : 0) != 0);
        }
      }
      free(original);
      free(original_nodes);
      spec_free(s);
    }
    printf("expansion arena sweep (provenance %u, semantic error %u, "
           "preexisting ID %u): %zu failures rejected\n",
           provenance, semantic_error, preexisting_id, count);
  }
  reset(0);
}

static void expansion_provenance_checks(void) {
  const char *definitions[] = {
      "f(x) = x && X x;",
      "f(x) = x && x;",
      "f(x) = g(x) && h(x); g(y) = y && y; h(z) = z && z;",
      "f(x) = X x && x;",
  };
  for (size_t i = 0; i < sizeof definitions / sizeof *definitions; ++i) {
    reset(0);
    char source[256];
    snprintf(source, sizeof source,
             "INFO { SEMANTICS: Mealy TARGET: Mealy } "
             "GLOBAL { DEFINITIONS { %s } } "
             "MAIN { INPUTS { %s; } GUARANTEES { f(%s); } }",
             definitions[i], i == 3 ? "x" : "p", i == 3 ? "X x" : "p");
    FILE *fp = fmemopen(source, strlen(source), "r");
    CHECK(fp);
    TlsfSpec *s = spec_parse(fp, "expansion-provenance");
    CHECK(fclose(fp) == 0 && s);
    Node *call = s->guarantee.formulas[0];
    call->source_id = 73;
    // Leave the outer formals unnumbered too: the first nested call's
    // fallback must survive the second nested substitution.
    if (i >= 2)
      s->defs[0].body->source_id = 72;
    if (i == 3) {
      // Recursion gives the shared X x its fallback before copying its ID.
      Node *body = s->defs[0].body;
      call->call_args[0] = body->lhs;
      body->lhs->arg->source_id = 5;
    }
    Node *actual = call->call_args[0];
    CHECK(actual->source_id == 0);
    Node before_actual = *actual;
    char *json = nullptr;
    size_t size = 0;
    FILE *out = open_memstream(&json, &size);
    CHECK(out);
    char hash[65];
    CHECK(tlsf_pipeline_source_sha256(source, strlen(source), hash));
    CHECK(tlsf_pipeline_expand_spec(s, nullptr, 0, out, hash, false, nullptr) ==
          0);
    CHECK(fclose(out) == 0 && json);
    CHECK(!memcmp(actual, &before_actual, sizeof before_actual));
    yyjson_doc *doc = yyjson_read(json, size, 0);
    CHECK(doc);
    yyjson_val *rows = yyjson_obj_get(yyjson_doc_get_root(doc), "conjuncts");
    CHECK(yyjson_arr_size(rows) == (i == 2 ? 4 : 2));
    for (size_t j = 0; j < yyjson_arr_size(rows); ++j) {
      yyjson_val *row = yyjson_arr_get(rows, j);
      // Historical values: first formal 2, X 3, shared-DAG fallback 5.
      CHECK(yyjson_get_uint(yyjson_obj_get(row, "source_node_id")) ==
            (i == 3             ? 5
             : i == 0 && j == 1 ? 3
                                : 2));
    }
    yyjson_doc_free(doc);
    free(json);
    spec_free(s);
  }
  reset(0);
}

static void expansion_checks(void) {
  expansion_provenance_checks();
  // Substituting a bus bound or an argument below a pre-numbered call must
  // leave shared arguments untouched, including after repeated semantic errors.
  for (unsigned semantic_error = 0; semantic_error < 2; ++semantic_error)
    for (unsigned preexisting_id = 0; preexisting_id < 2; ++preexisting_id) {
      char source[256];
      snprintf(source, sizeof source,
               "INFO { SEMANTICS: Mealy TARGET: Mealy } "
               "GLOBAL { DEFINITIONS { id(n) = n; } } "
               "MAIN { INPUTS { p; b[id(2)]; } GUARANTEES { %s %s } }",
               preexisting_id ? "id(p);" : "p;",
               semantic_error ? "missing();" : "");
      expansion_sweep(source, semantic_error, preexisting_id);
    }
  // Roll back only newly assigned IDs, on semantic errors as well as OOM.
  for (unsigned oom = 0; oom < 2; ++oom) {
    reset(0);
    TlsfSpec *s = spec_new();
    CHECK(s);
    Node *atom = node_ap(s->arena, "p");
    Node *root = node_x(s->arena, atom);
    CHECK(root && formula_list_push(s, &s->guarantee, root));
    atom->source_id = 73;
    s->capture_provenance = true;
    Node before_root = *root, before_atom = *atom;
    const ParamOverride unknown = {.name = "unknown", .value = 1};
    reset(oom ? 3 : 0);
    CHECK(expand(s, oom ? nullptr : &unknown, oom ? 0 : 1) != 0);
    armed = false;
    CHECK(fired == (bool)oom);
    CHECK(!memcmp(root, &before_root, sizeof before_root));
    CHECK(!memcmp(atom, &before_atom, sizeof before_atom));
    spec_free(s);
  }
  const char *bodies[] = {"X(G[0:2]((X true) U true))", "X[3](!p)",
                          "F[1:3](!p)", "G[0:2](p || !p)"};
  for (size_t b = 0; b < sizeof bodies / sizeof *bodies; ++b) {
    char source[256];
    snprintf(source, sizeof source,
             "INFO { SEMANTICS: Strict,Mealy TARGET: Moore } "
             "MAIN { INPUTS { p; } INITIALLY { %s; } }",
             bodies[b]);
    expansion_sweep(source, false, false);
  }
  const char *cases[] = {
      // Provenance must not leak root/child IDs when allocation 2 is refused.
      "MAIN { INPUTS { p; } GUARANTEES { X p; } }",
      // The minimal definition repro; then every section and multiple slots.
      "GLOBAL { DEFINITIONS { repeat(x) = x && X x; } } "
      "MAIN { INPUTS { p; } GUARANTEES { repeat(p); } }",
      "GLOBAL { DEFINITIONS { repeat(x) = x && X x; } } MAIN { INPUTS { p; q; "
      "} "
      "INITIALLY { repeat(p); repeat(q); } REQUIRE { repeat(p); } "
      "ASSUMPTIONS { repeat(p); } PRESET { repeat(p); } "
      "ASSERT { repeat(p); } GUARANTEES { repeat(p); repeat(q); } }",
      // Numeric and Boolean definition evaluators and nested calls.
      "GLOBAL { DEFINITIONS { inc(n) = n + 1; "
      "choose(n) = inc(n) > 0 : X[inc(n)] p otherwise : q; } } "
      "MAIN { INPUTS { p; q; } GUARANTEES { choose(1); } }",
      // Pattern bindings, recursive substitutions, and unmatched guards.
      "GLOBAL { DEFINITIONS { strip(f) = f ~ G x : (x && X x) "
      "otherwise : false; } } "
      "MAIN { INPUTS { p; } GUARANTEES { strip(G p); strip(p); } }",
      // Formula-valued membership domains, including a definition as a value.
      "GLOBAL { DEFINITIONS { repeat(x) = x && X x; "
      "all(x) = &&[f IN {x, X x, repeat(x)}] (f && X f); } } "
      "MAIN { INPUTS { p; q; } GUARANTEES { all(p); ||[f IN {p, q}] f; } }",
      // Range domains, empty domains, set enums, set definitions and reducers.
      "GLOBAL { DEFINITIONS { s(n) = {n, n + 1 .. n + 2}; "
      "range(x) = &&[0 < i <= 2] x; "
      "sets(x) = (+)[v IN {{x}, {x + 1}}] v; "
      "both(x) = (*)[v IN {{x}, {x, x + 1}}] v; } } "
      "MAIN { INPUTS { p; } GUARANTEES { range(p); &&[i IN s(0)] X[i] p; "
      "&&[i IN {}] p; ||[i IN {}] p; "
      "SIZE (sets(1) (+) both(1)) == 2; "
      "(SUM[i IN s(1)] i) == 6; (PROD[i IN {1, 2}] i) == 2; } }",
      // Bus formal names, indices, SIZEOF, computed bounds and overrides.
      "GLOBAL { PARAMETERS { N = 3; } DEFINITIONS { "
      "bit(bus, i) = bus[i] && X bus[i]; width(bus) = SIZEOF bus; } } "
      "MAIN { INPUTS { b[N]; } OUTPUTS { c[2]; } "
      "GUARANTEES { bit(b, 0); width(b) == 2; } }",
      // Signal-only expansions must reject OOM too, in either signal list.
      "MAIN { INPUTS { b[2]; } }",
      "MAIN { OUTPUTS { b[2]; } }",
      // Enum matches exercise bit names, negation, conjunction and disjunction.
      "GLOBAL { DEFINITIONS { enum Mode = Ready: 10,01; } } "
      "MAIN { INPUTS { Mode b; } GUARANTEES { b == Ready; b != Ready; } }",
      // Attaching bounded metadata must not mutate an input atom on failure.
      "MAIN { INPUTS { p; q; r; s; } GUARANTEES { X[0] p; G[0:0] q; F[0:0] r; "
      "X s; } }",
      // Substitution of bounded formula bodies and their strong flags.
      "GLOBAL { DEFINITIONS { window(x) = G[0:2] x && F[1:2] x; } } "
      "MAIN { INPUTS { p; } GUARANTEES { window(p); } }",
      // #110: close numeric bindings, compare separate core keys, substitute
      // stored high-level elements through nested sets and function actuals.
      "GLOBAL { DEFINITIONS { delay(x) = X[x] o; } } "
      "MAIN { OUTPUTS { o; } GUARANTEES { "
      "&&[s IN CUP[k IN {1,2}] {{delay(k), X[1] o}}] &&[f IN s] f; } }",
  };
  for (size_t i = 0; i < sizeof cases / sizeof *cases; ++i) {
    char source[2048];
    snprintf(source, sizeof source,
             "INFO { SEMANTICS: Mealy TARGET: Mealy } %s", cases[i]);
    expansion_sweep(source, false, false);
  }
}

static void assembly_checks(const char *source, const char *expected,
                            bool empty) {
  ClassifiedSpec *cs;
  TlsfSpec *spec = prepared(source, &cs);
  reset(0);
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  CHECK(root && !arena_failed(spec->arena));
  CHECK(eval(root, false) == empty && eval(root, true) == empty);
  size_t count = allocations;
  spec_free(spec);
  cli_checks(source, expected, count, false);
  for (size_t n = 1; n <= count; ++n) {
    spec = prepared(source, &cs);
    reset(n);
    FILE *out = tmpfile();
    CHECK(out);
    CHECK(!print_ltlxba_spec(out, spec, cs, PRINT_ALL, false));
    CHECK(fired && arena_failed(spec->arena) && ftell(out) == 0);
    CHECK(!build_spec_formula(spec, cs, PRINT_ALL));
    fclose(out);
    spec_free(spec);
  }
  // The existing AST/decomposition entry point must not publish a root, text,
  // or a verdict when whole-objective assembly fails.
  for (size_t n = 1; n <= count; ++n) {
    reset(n);
    armed = false;
    assembly_only = true;
    TlsfAst *ast = tlsf_ast_from_string(source, nullptr);
    CHECK(fired && !ast && !tlsf_ast_root(ast));
    tlsf_ast_free(ast);
    reset(n);
    armed = false;
    assembly_only = true;
    TlsfDecomposeResult *r = tlsf_decompose_string(source, nullptr);
    CHECK(fired && !r);
    tlsf_decompose_result_free(r);
  }
}

static void arena_checks(void) {
  reset(0);
  CHECK(!arena_new(SIZE_MAX));
  Arena *a = arena_new(4096);
  CHECK(a && !arena_failed(a));
  CHECK(arena_alloc_aligned(a, 1, 1));
  fail_slab = true;
  CHECK(!arena_alloc_aligned(a, 8192, 1));
  CHECK(fired && arena_failed(a));
  // A one-shot slab failure leaves spare space for smaller allocations.
  CHECK(arena_alloc_aligned(a, 1, 1) && arena_failed(a));
  arena_free(a);
  a = arena_new(4096);
  CHECK(a && !arena_failed(a));
  CHECK(!ARENA_ALLOC_N(a, Node, SIZE_MAX));
  CHECK(arena_failed(a));
  arena_free(a);
  a = arena_new(4096);
  CHECK(a);
  CHECK(!arena_alloc_aligned(a, SIZE_MAX, 1) && arena_failed(a));
  arena_free(a);
}

static void stream_checks(void) {
  char atom[4095], source[3 * sizeof atom + 128], expected[2 * sizeof atom + 8];
  memset(atom, 'p', sizeof atom - 1);
  atom[sizeof atom - 1] = '\0';
  snprintf(source, sizeof source,
           "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { OUTPUTS { %s; } "
           "GUARANTEES { %s; !%s; } }",
           atom, atom, atom);
  snprintf(expected, sizeof expected, "%s && !%s", atom, atom);
  healthy(source, expected);
  // Sweep character writes without relying on the FILE error indicator.
  reset(0);
  char_at = SIZE_MAX;
  TlsfConversionResult *r = tlsf_convert(source, nullptr);
  CHECK(r && !strcmp(r->preprocessed_ltl, expected));
  size_t count = char_count;
  tlsf_conversion_result_free(r);
  for (size_t n = 1; n <= count; ++n) {
    reset(0);
    char_at = n;
    r = tlsf_convert(source, nullptr);
    CHECK(fired && !r);
  }
  healthy(source, expected);
  reset(0);
  stream_armed = true;
  r = tlsf_convert(source, nullptr);
  CHECK(r && !strcmp(r->preprocessed_ltl, expected));
  count = stream_count;
  tlsf_conversion_result_free(r);
  CHECK(count > strlen(atom));
  for (size_t n = 1; n <= count; ++n) {
    reset(0);
    stream_armed = true;
    stream_at = n;
    r = tlsf_convert(source, nullptr);
    if (!fired || r)
      fprintf(stderr, "stream n=%zu/%zu, writes=%zu, result=%p\n", n, count,
              stream_count, (void *)r);
    CHECK(fired && !r);
  }
  healthy(source, expected);
  // The shared printer must also reject failures in plain/LaTeX atoms,
  // parentheses, operators, constants, and finite strong-next spelling.
  ClassifiedSpec *cs;
  TlsfSpec *spec = prepared(
      "INFO { SEMANTICS: Mealy,Finite TARGET: Mealy } MAIN { OUTPUTS { p_q; } "
      "GUARANTEES { X[!] p_q -> F (!p_q || G p_q); } }",
      &cs);
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  CHECK(root);
  for (LtlFormat fmt = LTL_FMT_LTLXBA; fmt <= LTL_FMT_LATEX; ++fmt) {
    for (int finite = 0; finite < 2; ++finite) {
      reset(0);
      stream_armed = true;
      char *text = conversion_render_ltl(root, fmt, finite, false);
      CHECK(text);
      count = stream_count;
      free(text);
      for (size_t n = 1; n <= count; ++n) {
        reset(0);
        stream_armed = true;
        stream_at = n;
        text = conversion_render_ltl(root, fmt, finite, false);
        CHECK(fired && !text);
      }
    }
  }
  spec_free(spec);
  reset(0);
}

static void csnf_stream_checks(void) {
  char atom[4095], source[3 * sizeof atom + 256];
  memset(atom, 'p', sizeof atom - 1);
  atom[sizeof atom - 1] = '\0';
  snprintf(source, sizeof source,
           "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { q; } "
           "OUTPUTS { %s; } GUARANTEES { G(%s <-> q); false; } }",
           atom, atom);
  reset(0);
  FILE *in = fmemopen(source, strlen(source), "r");
  CHECK(in);
  TlsfPipelineOptions opts = {.certify = true, .template_mask = TPL_ALL};
  TlsfPipeline *pipe = tlsf_pipeline_load(in, &opts);
  fclose(in);
  CHECK(pipe);
  for (int lines = 0; lines < 2; ++lines) {
    size_t count = 0;
    for (size_t n = 0; n <= count; ++n) {
      reset(0);
      char *text = nullptr;
      size_t size = 0;
      FILE *out = open_memstream(&text, &size);
      CHECK(out);
      write_target = out;
      write_at = n;
      bool ok = lines ? csnf_emit_lines(out, pipe->csnf, "test", true)
                      : csnf_emit_text(out, pipe->csnf, true);
      CHECK(!ferror(out));
      CHECK(fclose(out) == 0);
      write_target = nullptr;
      if (n == 0) {
        CHECK(ok && size > sizeof atom);
        count = write_count;
        CHECK(count > 3);
      } else {
        CHECK(fired && !ok);
      }
      free(text);
    }
  }
  tlsf_pipeline_free(pipe);
}

static void cover_checks(const char *source) {
  for (int split = 0; split < 2; ++split) {
    TlsfDecomposeOptions opts = {.split = split};
    reset(0);
    armed = false;
    cover_only = true;
    TlsfDecomposeResult *r = tlsf_decompose_string(source, &opts);
    CHECK(r);
    size_t count = allocations;
    tlsf_decompose_result_free(r);
    CHECK(count);
    for (size_t n = 1; n <= count; ++n) {
      reset(n);
      armed = false;
      cover_only = true;
      r = tlsf_decompose_string(source, &opts);
      CHECK(fired && !r);
      tlsf_decompose_result_free(r);
      reset(n);
      armed = false;
      cover_only = true;
      TlsfAst *ast = tlsf_ast_from_string(source, &opts);
      CHECK(fired && !ast);
      tlsf_ast_free(ast);
    }
  }
}

static void composition_sweep(const char *source, uint32_t accepted,
                              uint32_t residual, uint32_t conflicts,
                              uint32_t eliminated) {
  size_t count = 0;
  for (size_t n = 0; n <= count + 1; ++n) {
    reset(0);
    composition_only = true;
    heap_at = n;
    FILE *in = fmemopen((void *)source, strlen(source), "r");
    CHECK(in);
    TlsfPipelineError error = {0};
    TlsfPipelineOptions opts = {
        .certify = true, .template_mask = TPL_ALL, .error = &error};
    TlsfPipeline *p = tlsf_pipeline_load(in, &opts);
    fclose(in);
    if (n == 0 || n == count + 1) {
      CHECK(!fired && p && error.status == TLSF_PIPELINE_OK);
      CsnfComposition *c = p->composition;
      CHECK(c->naccepted == accepted && c->nresidual == residual);
      CHECK(c->nconflicts == conflicts && c->nelim == eliminated);
      CHECK(c->nowned_outputs == eliminated && !c->may_strengthen);
      CHECK(c->fully_solved == (residual == 0));
      CHECK(c->neliminated == p->cover->count - residual);
      if (n == 0) {
        count = heap_count;
        CHECK(count >= 12);
      }
      tlsf_pipeline_free(p);
      continue;
    }
    if (!fired || p)
      fprintf(stderr, "composition n=%zu/%zu, result=%p\n", n, count,
              (void *)p);
    CHECK(fired && !p && error.status == TLSF_PIPELINE_LIMIT);
    CHECK(!strcmp(error.stage, "compose"));
    CHECK(strstr(error.message, "out of memory"));
    reset(0);
    composition_only = true;
    heap_at = n;
    TlsfAst *ast = tlsf_ast_from_string(source, nullptr);
    CHECK(fired && !ast && !tlsf_ast_root(ast));
    tlsf_ast_free(ast);
    reset(0);
    composition_only = true;
    heap_at = n;
    TlsfDecomposeResult *r = tlsf_decompose_string(source, nullptr);
    CHECK(fired && !r);
    tlsf_decompose_result_free(r);
  }
  printf("composition allocation sweep: %zu failures rejected\n", count);
}

static void arm_composition_arena(size_t nth) {
  reset(nth);
  armed = false;
  composition_arena_only = true;
}

static void composition_arena_sweep(const char *source, NodeKind value_kind) {
  size_t count = 0;
  for (size_t n = 0; n <= count + 1; ++n) {
    arm_composition_arena(n);
    FILE *in = fmemopen((void *)source, strlen(source), "r");
    CHECK(in);
    TlsfPipelineError error = {0};
    TlsfPipelineOptions opts = {
        .certify = true, .template_mask = TPL_ALL, .error = &error};
    TlsfPipeline *p = tlsf_pipeline_load(in, &opts);
    fclose(in);
    if (n == 0 || n == count + 1) {
      CHECK(!fired && p && error.status == TLSF_PIPELINE_OK);
      CHECK(!arena_failed(p->cover->arena));
      CsnfComposition *comp = p->composition;
      CHECK(comp->naccepted == 1 && comp->nresidual == 0);
      CHECK(comp->nelim == 1 && comp->elim[0].value);
      CHECK(comp->elim[0].value->kind == value_kind);
      CHECK(comp->fully_solved && comp->neliminated == p->cover->count);
      if (n == 0) {
        count = allocations;
        CHECK(count >= 3);
      } else {
        // A previously failed arena must also be rejected, even if later
        // allocations can succeed from spare slab space.
        CHECK(!arena_alloc_aligned(p->cover->arena, SIZE_MAX, 8));
        CHECK(arena_alloc_aligned(p->cover->arena, 1, 1));
        CHECK(!__real_csnf_compose(p->csnf));
      }
      tlsf_pipeline_free(p);
      continue;
    }
    CHECK(fired && !p && error.status == TLSF_PIPELINE_LIMIT);
    CHECK(!strcmp(error.stage, "compose"));
    CHECK(strstr(error.message, "out of memory"));

    arm_composition_arena(n);
    TlsfAst *ast = tlsf_ast_from_string(source, nullptr);
    CHECK(fired && !ast && !tlsf_ast_root(ast));
    tlsf_ast_free(ast);

    arm_composition_arena(n);
    TlsfDecomposeResult *result = tlsf_decompose_string(source, nullptr);
    CHECK(fired && !result);
    tlsf_decompose_result_free(result);
  }
  printf("composition arena sweep: %zu failures rejected\n", count);
}

static void rewrite_checks(void) {
  const char *source =
      "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
      "OUTPUTS { p; } GUARANTEES { G(!false && (p || false)); } }";
  ClassifiedSpec *cs;
  TlsfSpec *spec = prepared(source, &cs);
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  CHECK(root);
  reset(0);
  CHECK(apply_rewrites(spec->arena, root, RW_SIMPLIFY_WEAK));
  size_t count = allocations;
  CHECK(count);
  spec_free(spec);
  cli_checks(source, "G p", count, true);
}

// Evaluate next directly from its finite-word definition, independently of the
// rewrite/NNF code. Exhaust short words, including their terminal positions.
static bool finite_eval(const Node *n, unsigned word, unsigned len,
                        unsigned pos) {
  CHECK(n && pos < len);
  switch (n->kind) {
  case NODE_TRUE:
    return true;
  case NODE_FALSE:
    return false;
  case NODE_AP:
    return (word >> pos) & 1u;
  case NODE_NOT:
    return !finite_eval(n->arg, word, len, pos);
  case NODE_X:
    return pos + 1 == len || finite_eval(n->arg, word, len, pos + 1);
  case NODE_X_STRONG:
    return pos + 1 < len && finite_eval(n->arg, word, len, pos + 1);
  default:
    abort();
  }
}

static void finite_next_checks(void) {
  reset(0);
  Arena *a = arena_new(4096);
  CHECK(a);
  Node *args[] = {node_false(a), node_true(a), node_ap(a, "p")};
  for (size_t i = 0; i < sizeof args / sizeof *args; ++i)
    for (int strong = 0; strong < 2; ++strong)
      for (int neg = 0; neg < 2; ++neg) {
        Node *f = strong ? node_x_strong(a, args[i]) : node_x(a, args[i]);
        if (neg)
          f = node_not(a, f);
        unsigned flags[] = {RW_SIMPLIFY_WEAK, RW_NNF, RW_STRONG_SIMPLIFY};
        for (size_t k = 0; k < sizeof flags / sizeof *flags; ++k) {
          Node *r = apply_rewrites(a, f, flags[k] | RW_FINITE);
          CHECK(r);
          for (unsigned len = 1; len <= 3; ++len)
            for (unsigned word = 0; word < (1u << len); ++word)
              for (unsigned pos = 0; pos < len; ++pos)
                CHECK(finite_eval(f, word, len, pos) ==
                      finite_eval(r, word, len, pos));
        }
      }
  arena_free(a);
}

static void intern_sweeps(void) {
  char source[8192];
  // The 193rd distinct string grows the non-arena intern table. Exercise
  // identifiers, quoted strings, and enum bit strings at that boundary.
  for (int kind = 0; kind < 4; ++kind) {
    size_t used = (size_t)snprintf(source, sizeof source, "INFO { ");
    if (kind >= 2) {
      used += (size_t)snprintf(source + used, sizeof source - used, "TAGS: ");
      int tags = kind == 2 ? 193 : 190;
      for (int i = 0; i < tags; ++i)
        used += (size_t)snprintf(source + used, sizeof source - used,
                                 "%s\"tag%d\"", i ? "," : "", i);
    }
    used += (size_t)snprintf(source + used, sizeof source - used,
                             " SEMANTICS: Mealy TARGET: Mealy } ");
    if (kind == 3)
      used +=
          (size_t)snprintf(source + used, sizeof source - used,
                           "GLOBAL { DEFINITIONS { enum Kind = label: 0; } } ");
    used += (size_t)snprintf(source + used, sizeof source - used,
                             "MAIN { OUTPUTS { ");
    for (int i = 0; i < (kind < 2 ? 193 : 1); ++i)
      used += (size_t)snprintf(source + used, sizeof source - used, "p%d;", i);
    used += (size_t)snprintf(source + used, sizeof source - used,
                             " } GUARANTEES { ");
    if (kind == 1)
      for (int i = 0; i < 193; ++i)
        used +=
            (size_t)snprintf(source + used, sizeof source - used, "p%d;", i);
    used += (size_t)snprintf(source + used, sizeof source - used, "false; } }");
    CHECK(used < sizeof source);
    heap_sweep(source, true);
  }
}

int main(void) {
  adaptation_checks();
  expansion_checks();
  // Issue #90's minimal reaction, a longer OR, and both constant builders.
  const char *composition_bodies[] = {
      "G(a -> p); G(b -> p);",
      "G(a -> p); G(b -> p); G(c -> p);",
      "G(a -> !p); G(b -> !p);",
      "F p;",
      "F G p;",
      "G(p <-> a);",
  };
  const NodeKind value_kinds[] = {NODE_OR,   NODE_OR,   NODE_FALSE,
                                  NODE_TRUE, NODE_TRUE, NODE_AP};
  for (size_t i = 0; i < sizeof value_kinds / sizeof *value_kinds; ++i) {
    char source[512];
    snprintf(source, sizeof source,
             "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
             "INPUTS { %s } OUTPUTS { p; } GUARANTEES { %s } }",
             i == 1 ? "a; b; c;" : "a; b;", composition_bodies[i]);
    composition_arena_sweep(source, value_kinds[i]);
  }
  composition_sweep("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { "
                    "INPUTS { q; } OUTPUTS { p; } GUARANTEES { G(p <-> q); } }",
                    1, 0, 0, 1);
  composition_sweep(
      "INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { a; b; q; } "
      "OUTPUTS { p; o1; o2; o3; o4; } GUARANTEES { G(p <-> q); "
      "G(o1 <-> (a && o2)); G(o2 <-> (b && o1)); "
      "G(o3 <-> (a && o4)); G(o4 <-> (b && o3)); F(p && o1 && o3); } }",
      3, 3, 2, 3);
  arena_checks();
  stream_checks();
  csnf_stream_checks();
  rewrite_checks();
  finite_next_checks();
  cover_checks("INFO { SEMANTICS: Mealy TARGET: Mealy } "
               "MAIN { OUTPUTS { p; } GUARANTEES { false; } }");
  cover_checks("INFO { SEMANTICS: Mealy TARGET: Mealy } "
               "MAIN { OUTPUTS { p; } GUARANTEES { G(p && !p); } }");
  intern_sweeps();
  const char *bodies[] = {"GUARANTEES { false; }", "GUARANTEES { p; !p; }", ""};
  const char *expected[] = {"false", "p && !p", "true"};
  for (size_t strict = 0; strict < 2; ++strict) {
    for (size_t i = 0; i < 3; ++i) {
      char source[512];
      snprintf(source, sizeof source,
               "INFO { SEMANTICS: %s TARGET: Mealy } "
               "MAIN { OUTPUTS { p; } %s }",
               strict ? "Mealy,Strict" : "Mealy", bodies[i]);
      healthy(source, expected[i]);
      if (i == 0) {
        reset(0);
        match_size = 16 * sizeof(SectionPatternEntry);
        TlsfConversionResult *r = tlsf_convert(source, nullptr);
        CHECK(fired && !r);
        reset(0);
        slab_at_assembly = true;
        r = tlsf_convert(source, nullptr);
        CHECK(fired && !r);
        reset(0);
        slab_at_assembly = true;
        TlsfAst *ast = tlsf_ast_from_string(source, nullptr);
        CHECK(fired && !ast && !tlsf_ast_root(ast));
        tlsf_ast_free(ast);
      }
      assembly_checks(source, expected[i], i == 2);
      conversion_sweep(source, expected[i]);
      heap_sweep(source, true);
    }
  }
  heap_sweep("INFO { SEMANTICS: Mealy TARGET: Mealy } "
             "MAIN { OUTPUTS { p[2]; } GUARANTEES { false; } }",
             false);
  const char *parameterized =
      "INFO { SEMANTICS: Mealy TARGET: Mealy } "
      "GLOBAL { PARAMETERS { N = 1; } } "
      "MAIN { OUTPUTS { p[N]; } GUARANTEES { false; } }";
  conversion_sweep(parameterized, "false");
  heap_sweep(parameterized, true);
  const char *rich = "INFO { SEMANTICS: %s TARGET: Mealy } "
                     "MAIN { INPUTS { q; } OUTPUTS { p; } "
                     "INITIALLY { q; } REQUIRE { q; } ASSUMPTIONS { G F q; } "
                     "PRESET { p; } ASSERT { p; } GUARANTEES { F p; } }";
  for (size_t strict = 0; strict < 2; ++strict) {
    char source[512];
    snprintf(source, sizeof source, rich, strict ? "Mealy,Strict" : "Mealy");
    reset(0);
    TlsfConversionResult *r = tlsf_convert(source, nullptr);
    CHECK(r);
    char *expected_rich = strdup(r->preprocessed_ltl);
    CHECK(expected_rich);
    tlsf_conversion_result_free(r);
    conversion_sweep(source, expected_rich);
    free(expected_rich);
  }
  puts("objective allocation failures rejected; healthy objectives unchanged");
}
