#define _GNU_SOURCE
#include <errno.h>
#include "conversion_internal.h"
#include "section_pattern.h"
#include "rewrite.h"
#include "tlsf/ast_api.h"
#include "tlsf/convert.h"
#include "tlsf/pipeline.h"

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
static bool rewrite_only, cover_only;
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

static void reset(size_t nth) {
  fail_at = nth;
  allocations = match_size = 0;
  armed = true;
  fired = fail_slab = assembly_only = slab_at_assembly = false;
  rewrite_only = cover_only = false;
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
