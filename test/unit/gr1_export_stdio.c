#define _GNU_SOURCE
#include "gr1_export.h"

#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <sys/types.h>

// Exercise the actual BSD callbacks on glibc without pretending its FILE
// implementation has Darwin's buffering or error behavior.
typedef struct {
  void *cookie;
  int (*write)(void *, const char *, int);
  int (*close)(void *);
} BsdStream;

static ssize_t bsd_write(void *opaque, const char *bytes, size_t count) {
  BsdStream *stream = opaque;
  assert(count <= INT_MAX);
  int written = stream->write(stream->cookie, bytes, (int)count);
  // The BSD adapter must return -1 on failure; fopencookie requires zero.
  assert(written == -1 || written == (int)count);
  return written < 0 ? 0 : written;
}

static int bsd_close(void *opaque) {
  BsdStream *stream = opaque;
  int result = stream->close(stream->cookie);
  free(stream);
  return result;
}

FILE *gr1_export_test_funopen(const void *cookie,
                              int (*readfn)(void *, char *, int),
                              int (*writefn)(void *, const char *, int),
                              fpos_t (*seekfn)(void *, fpos_t, int),
                              int (*closefn)(void *)) {
  assert(!readfn && !seekfn && writefn && closefn);
  BsdStream *adapter = malloc(sizeof *adapter);
  if (!adapter)
    return nullptr;
  *adapter = (BsdStream){(void *)cookie, writefn, closefn};
  FILE *stream = fopencookie(
      adapter, "w",
      (cookie_io_functions_t){.write = bsd_write, .close = bsd_close});
  if (!stream)
    free(adapter);
  return stream;
}

FILE *gr1_export_test_open_memstream(char **output, size_t *size) {
  FILE *stream = open_memstream(output, size);
  if (!stream)
    return nullptr;
  // Darwin publishes its empty allocation at open. Flushing glibc's stream
  // reproduces that permitted behavior and catches pre-flush assumptions.
  assert(fflush(stream) == 0);
  assert(*output && *size == 0);
  return stream;
}
