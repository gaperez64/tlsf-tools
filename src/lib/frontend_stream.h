#ifndef TLSF_FRONTEND_STREAM_H
#define TLSF_FRONTEND_STREAM_H

#include "tlsf/arena.h"
#include <stdio.h>

/* Like open_memstream; the result is published on close and owned by free(). */
FILE *frontend_memstream(Arena *arena, char **output, size_t *size);

#endif
