#define _GNU_SOURCE
#include "frontend_stream.h"
#include "arena_budget.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

typedef struct {
  Arena *arena;
  char *data;
  size_t size, capacity;
  char **output;
  size_t *output_size;
} FrontendStream;

static ssize_t stream_write(void *raw, const char *bytes, size_t count) {
  FrontendStream *s = raw;
  if (!arena_check_budget(s->arena, 0) || count >= SIZE_MAX - s->size)
    goto fail;
  size_t needed = s->size + count + 1;
  if (needed > s->capacity) {
    size_t capacity = s->capacity ? s->capacity : 256;
    while (capacity < needed)
      capacity = capacity > SIZE_MAX / 2 ? SIZE_MAX : capacity * 2;
    if (!arena_check_budget(s->arena, capacity))
      goto fail;
    char *data = realloc(s->data, capacity);
    if (!data)
      goto fail;
    s->data = data;
    s->capacity = capacity;
  }
  memcpy(s->data + s->size, bytes, count);
  s->size += count;
  return (ssize_t)count;
fail:
  arena_mark_failed(s->arena);
  return -1;
}

static int stream_close(void *raw) {
  FrontendStream *s = raw;
  int result = -1;
  if (!arena_failed(s->arena) && s->data) {
    s->data[s->size] = '\0';
    *s->output = s->data;
    *s->output_size = s->size;
    result = 0;
  } else
    free(s->data);
  free(s);
  return result;
}

#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) ||      \
    defined(__NetBSD__)
static int stream_write_bsd(void *raw, const char *bytes, int count) {
  return (int)stream_write(raw, bytes, (size_t)count);
}
#endif

FILE *frontend_memstream(Arena *arena, char **output, size_t *size) {
  if (!arena->cancelled)
    return open_memstream(output, size);
  *output = nullptr;
  *size = 0;
  if (!arena_check_budget(arena, sizeof(FrontendStream) + BUFSIZ))
    return nullptr;
  FrontendStream *s = calloc(1, sizeof *s);
  if (!s)
    return nullptr;
  s->arena = arena;
  s->output = output;
  s->output_size = size;
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) ||      \
    defined(__NetBSD__)
  FILE *stream = funopen(s, nullptr, stream_write_bsd, nullptr, stream_close);
#else
  cookie_io_functions_t io = {.write = stream_write, .close = stream_close};
  FILE *stream = fopencookie(s, "w", io);
#endif
  if (!stream)
    free(s);
  return stream;
}
