#include "gr1_export.h"

// Read OxiddSolveOptions with the library's NDEBUG layout before enabling
// assertions in release builds.
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  OxiddFailure failure;
  OxiddSolveOptions solve;
  Gr1CertificateOptions certificate;
  OxiddRun run;
  char *bytes;
  size_t size;
} Export;

static FILE *open_stream(Export *export, size_t run_cap,
                         size_t certificate_cap) {
  *export = (Export){0};
  export->solve = oxidd_solve_options_default();
  export->solve.max_artifact_bytes = run_cap;
  export->solve.failure = &export->failure;
  export->certificate.max_artifact_bytes = certificate_cap;
  export->run.options = &export->solve;
  char sentinel;
  export->bytes = &sentinel;
  export->size = SIZE_MAX;
  FILE *stream = gr1_open_export_memstream(&export->run, &export->certificate,
                                           &export->bytes, &export->size);
  assert(stream);
  // Only capped streams promise publication at close. Darwin's ordinary
  // open_memstream may publish its empty buffer immediately at open.
  if (run_cap || certificate_cap)
    assert(export->bytes == nullptr && export->size == 0);
  return stream;
}

static void within_cap(size_t run_cap, size_t certificate_cap, size_t count) {
  Export export;
  FILE *stream = open_stream(&export, run_cap, certificate_cap);
  // Binary data, including embedded NULs; cross the initial growth boundary.
  char payload[1024];
  for (size_t i = 0; i < sizeof payload; ++i)
    payload[i] = (char)(i % 128);
  assert(count <= sizeof payload);
  size_t first = count / 2;
  assert(fwrite(payload, 1, first, stream) == first);
  assert(fwrite(payload + first, 1, count - first, stream) == count - first);
  assert(fflush(stream) == 0 && !ferror(stream));
  // A nonzero cap must select the bounded stream even when it is SIZE_MAX.
  // open_memstream would already publish a buffer on fflush().
  assert(export.bytes == nullptr && export.size == 0);
  assert(fclose(stream) == 0);
  assert(export.failure.kind == OXIDD_FAILURE_NONE);
  assert(export.bytes && export.size == count);
  assert(memcmp(export.bytes, payload, count) == 0);
  // The cap excludes this byte, including when count exactly equals the cap.
  assert(export.bytes[count] == '\0');
  free(export.bytes);
}

static void crossing_cap(size_t run_cap, size_t certificate_cap, size_t cap,
                         size_t prefix) {
  Export export;
  FILE *stream = open_stream(&export, run_cap, certificate_cap);
  char payload[1024] = {0};
  assert(cap + 1 <= sizeof payload && prefix <= cap);
  assert(fwrite(payload, 1, prefix, stream) == prefix);
  assert(!ferror(stream));
  assert(export.failure.kind == OXIDD_FAILURE_NONE);
  size_t crossing = cap - prefix + 1;
  errno = 0;
  // Check the write itself, before any serializer or post-export size guard.
  assert(fwrite(payload, 1, crossing, stream) < crossing);
  assert(ferror(stream) && errno == EFBIG);
  assert(export.failure.kind == OXIDD_FAILURE_ARTIFACT_LIMIT);
  assert(strcmp(export.failure.phase, "export") == 0);
  assert(strcmp(export.failure.operation, "artifact_cap") == 0);
  assert(export.bytes == nullptr && export.size == 0);
  // Failure is sticky even if the stdio error indicator is cleared.
  clearerr(stream);
  assert(fwrite(payload, 1, 1, stream) == 0);
  assert(ferror(stream));
  assert(fclose(stream) == EOF);
  assert(export.bytes == nullptr && export.size == 0);
}

static void capped(size_t run_cap, size_t certificate_cap, size_t cap) {
  within_cap(run_cap, certificate_cap, 0);
  within_cap(run_cap, certificate_cap, cap / 2);
  within_cap(run_cap, certificate_cap, cap);
  crossing_cap(run_cap, certificate_cap, cap, 0);
  crossing_cap(run_cap, certificate_cap, cap, cap / 2);
  crossing_cap(run_cap, certificate_cap, cap, cap);
}

int main(void) {
  const size_t caps[] = {1, 4, 255, 256, 257, 513};
  for (size_t i = 0; i < sizeof caps / sizeof *caps; ++i) {
    size_t cap = caps[i];
    capped(cap, 0, cap);       // Inherit the run cap.
    capped(0, cap, cap);       // Certificate cap alone.
    capped(cap + 1, cap, cap); // Certificate cap overrides a larger run cap.
    capped(1, cap, cap);       // It also overrides a smaller run cap.
  }
  within_cap(SIZE_MAX, 0, 513);
  within_cap(0, SIZE_MAX, 513);

  // With neither cap set, retain the ordinary unbounded memory stream.
  Export export;
  FILE *stream = open_stream(&export, 0, 0);
  const char payload[] = "unlimited";
  assert(fwrite(payload, 1, sizeof payload - 1, stream) == sizeof payload - 1);
  assert(fflush(stream) == 0 && !ferror(stream));
  assert(export.bytes && export.size == sizeof payload - 1);
  assert(memcmp(export.bytes, payload, sizeof payload) == 0);
  assert(fclose(stream) == 0);
  assert(export.failure.kind == OXIDD_FAILURE_NONE);
  assert(export.bytes && export.size == sizeof payload - 1);
  assert(memcmp(export.bytes, payload, sizeof payload) == 0);
  free(export.bytes);
  return 0;
}
