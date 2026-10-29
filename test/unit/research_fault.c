#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>

#ifdef RESIDUAL_FAULT
#include "residual.h"

static bool armed;
void *__real_malloc(size_t);
void *__wrap_malloc(size_t);
void *__wrap_malloc(size_t n) {
  if (armed) {
    armed = false;
    fputs("injected residual_cluster_keys allocation failure\n", stderr);
    return nullptr;
  }
  return __real_malloc(n);
}

uint32_t __real_residual_cluster_keys(ConstraintCover *, const Node **,
                                      uint32_t, uint32_t *, uint32_t **);
uint32_t __wrap_residual_cluster_keys(ConstraintCover *, const Node **,
                                      uint32_t, uint32_t *, uint32_t **);
uint32_t __wrap_residual_cluster_keys(ConstraintCover *cov, const Node **rf,
                                      uint32_t n, uint32_t *key,
                                      uint32_t **keys) {
  armed = true;
  uint32_t count = __real_residual_cluster_keys(cov, rf, n, key, keys);
  armed = false;
  return count;
}
#elif defined(COMPOSITION_FAULT)
#include "tlsf/templates.h"

static bool composing;
static size_t fail_at, count;
static bool composition_fault(void) {
  if (!composing || ++count != fail_at)
    return false;
  fprintf(stderr, "injected composition allocation failure %zu\n", count);
  return true;
}
void *__real_malloc(size_t);
void *__wrap_malloc(size_t);
void *__wrap_malloc(size_t n) {
  return composition_fault() ? nullptr : __real_malloc(n);
}
void *__real_calloc(size_t, size_t);
void *__wrap_calloc(size_t, size_t);
void *__wrap_calloc(size_t n, size_t size) {
  return composition_fault() ? nullptr : __real_calloc(n, size);
}
void *__real_realloc(void *, size_t);
void *__wrap_realloc(void *, size_t);
void *__wrap_realloc(void *p, size_t n) {
  return composition_fault() ? nullptr : __real_realloc(p, n);
}
CsnfComposition *__real_csnf_compose(const Csnf *);
CsnfComposition *__wrap_csnf_compose(const Csnf *);
CsnfComposition *__wrap_csnf_compose(const Csnf *c) {
  const char *nth = getenv("TLSF_TEST_COMPOSITION_ALLOC");
  fail_at = nth ? strtoul(nth, nullptr, 10) : 0;
  count = 0;
  composing = true;
  CsnfComposition *r = __real_csnf_compose(c);
  composing = false;
  fprintf(stderr, "composition allocations: %zu\n", count);
  return r;
}
#else
#include "tlsf/templates.h"

static bool emitting;
FILE *__real_open_memstream(char **, size_t *);
FILE *__wrap_open_memstream(char **, size_t *);
FILE *__wrap_open_memstream(char **buf, size_t *size) {
  if (emitting) {
    emitting = false;
    fputs("injected formula_str allocation failure\n", stderr);
    return nullptr;
  }
  return __real_open_memstream(buf, size);
}

bool __real_csnf_emit_lines(FILE *, const Csnf *, const char *, bool);
bool __wrap_csnf_emit_lines(FILE *, const Csnf *, const char *, bool);
bool __wrap_csnf_emit_lines(FILE *out, const Csnf *c, const char *source,
                            bool solve) {
  emitting = true;
  bool ok = __real_csnf_emit_lines(out, c, source, solve);
  emitting = false;
  return ok;
}

bool __real_csnf_emit_text(FILE *, const Csnf *, bool);
bool __wrap_csnf_emit_text(FILE *, const Csnf *, bool);
bool __wrap_csnf_emit_text(FILE *out, const Csnf *c, bool solve) {
  emitting = true;
  bool ok = __real_csnf_emit_text(out, c, solve);
  emitting = false;
  return ok;
}
#endif
