#define _POSIX_C_SOURCE 200809L
#include "check.h"
#include "decode.h"
#include "tlsf/print_tlsf.h"

#include <stdlib.h>
#include <string.h>

static char *printed(const TlsfSpec *spec, size_t *size) {
  char *text = NULL;
  FILE *stream = open_memstream(&text, size);
  if (!stream)
    return NULL;
  print_tlsf(stream, spec, true);
  if (fclose(stream) != 0) {
    free(text);
    return NULL;
  }
  return text;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  char text[TLSF_FUZZ_TEXT_CAPACITY];
  size_t length = tlsf_fuzz_decode(data, size, text);
  FILE *stream = fmemopen(text, length, "r");
  if (!stream)
    return 0;
  TlsfSpec *first = spec_parse(stream, "fuzz-decoder");
  fclose(stream);
  // R1: The decoder's grammar is total: its output must always be parseable
  // TLSF.
  CHECK(R1, first);

  size_t first_size = 0, second_size = 0;
  char *once = printed(first, &first_size);
  spec_free(first);
  if (!once)
    return 0;
  stream = fmemopen(once, first_size, "r");
  if (!stream) {
    free(once);
    return 0;
  }
  TlsfSpec *second = spec_parse(stream, "fuzz-printed");
  fclose(stream);
  // R2: Printing a parsed TLSF spec must produce TLSF accepted by the same
  // parser.
  CHECK(R2, second);

  char *twice = printed(second, &second_size);
  spec_free(second);
  if (twice) {
    // R3: Canonical printing must be stable under reparsing: syntax and
    // precedence must preserve the represented tree (see README for this
    // oracle's scope).
    CHECK(R3,
          first_size == second_size && memcmp(once, twice, first_size) == 0);
  }
  free(twice);
  free(once);
  return 0;
}
