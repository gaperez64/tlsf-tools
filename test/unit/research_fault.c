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
