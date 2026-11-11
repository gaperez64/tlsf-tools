#include "tlsf/symmetry.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef SYMMETRY_ALLOC_FAILURE
// Exercise C++ allocation failures through the C entry point, including every
// partial-result cleanup path. Requesting SIZE_MAX makes real operator new
// throw without introducing a C++ test client or library-side fault hooks.
static size_t fail_at, allocations;
void *__real__Znwm(size_t size);
void *__wrap__Znwm(size_t size);
void *__wrap__Znwm(size_t size) {
  return __real__Znwm(++allocations == fail_at ? SIZE_MAX : size);
}
#endif

static size_t ap_index(const TlsfConversionResult *c, const char *name) {
  for (uint32_t i = 0; i < c->n_inputs; ++i)
    if (!strcmp(c->inputs[i], name))
      return i;
  for (uint32_t i = 0; i < c->n_outputs; ++i)
    if (!strcmp(c->outputs[i], name))
      return (size_t)c->n_inputs + i;
  assert(0);
  return SIZE_MAX;
}

static TlsfConversionResult *read_fixture(const char *directory,
                                          const char *name) {
  char path[4096];
  int length = snprintf(path, sizeof(path), "%s/%s.tlsf", directory, name);
  assert(length > 0 && (size_t)length < sizeof(path));
  FILE *file = fopen(path, "rb");
  assert(file && !fseek(file, 0, SEEK_END));
  long size = ftell(file);
  assert(size >= 0 && !fseek(file, 0, SEEK_SET));
  char *text = malloc((size_t)size + 1);
  assert(text && fread(text, 1, (size_t)size, file) == (size_t)size);
  text[size] = '\0';
  assert(!fclose(file));
  TlsfConversionResult *c = tlsf_convert(text, "Mealy");
  free(text);
  assert(c);
  return c;
}

static void check_fixture(const char *directory, const char *name,
                          size_t n_ranges, const TlsfSymmetryVerdict *verdicts,
                          const unsigned *verified) {
  TlsfConversionResult *c = read_fixture(directory, name);
  TlsfSymmetryResult *result = NULL, *second = NULL;
  assert(tlsf_symmetry_detect(c, &result) == TLSF_SYMMETRY_OK);
  assert(result && !result->reason && result->n_ranges == n_ranges);
  assert(result->n_aps == (size_t)c->n_inputs + c->n_outputs);
  // Results are independent even for two live calls on the same conversion.
  assert(tlsf_symmetry_detect(c, &second) == TLSF_SYMMETRY_OK);
  assert(second != result && second->n_generators == result->n_generators);
  tlsf_symmetry_result_free(second);

  size_t generator = 0;
  for (size_t r = 0; r < n_ranges; ++r) {
    const TlsfSymmetryRange *range = &result->ranges[r];
    size_t width = (size_t)range->hi - range->lo + 1;
    assert(!range->reason && range->verdict == verdicts[r]);
    assert(range->n_candidates == width && range->n_families);
    for (size_t k = 0; k < width; ++k) {
      const TlsfSymmetryCandidate *candidate = &range->candidates[k];
      bool rotation = k == width - 1;
      assert(candidate->kind ==
             (rotation ? TLSF_SYMMETRY_ROTATION : TLSF_SYMMETRY_ADJACENT));
      bool expected_verified = (verified[r] & (1u << k)) != 0;
      assert((candidate->generator != SIZE_MAX) == expected_verified);
      assert((candidate->reason == NULL) == expected_verified);
      for (size_t i = 0; i < width; ++i) {
        size_t to = rotation     ? (i + 1) % width
                    : i == k     ? k + 1
                    : i == k + 1 ? k
                                 : i;
        assert(candidate->image[i] == range->lo + to);
      }
      if (!expected_verified)
        continue;
      assert(candidate->generator == generator &&
             generator < result->n_generators);
      const TlsfSymmetryGenerator *g = &result->generators[generator++];
      assert(g->range == r && g->kind == candidate->kind);
      size_t *expected = malloc(result->n_aps * sizeof(*expected));
      bool *seen = calloc(result->n_aps, sizeof(*seen));
      assert(expected && seen);
      for (size_t i = 0; i < result->n_aps; ++i)
        expected[i] = i;
      for (size_t f = 0; f < range->n_families; ++f) {
        assert(range->families[f] < c->n_indexed_families);
        const TlsfDecomposeIndexedFamily *family =
            &c->indexed_families[range->families[f]];
        assert(family->lo == range->lo && family->hi == range->hi);
        for (size_t i = 0; i < width; ++i)
          expected[ap_index(c, family->members[i])] =
              ap_index(c, family->members[candidate->image[i] - range->lo]);
      }
      for (size_t i = 0; i < result->n_aps; ++i) {
        size_t to = g->image[i];
        assert(to == expected[i] && to < result->n_aps && !seen[to]);
        assert((i < c->n_inputs) == (to < c->n_inputs));
        seen[to] = true;
      }
      free(seen);
      free(expected);
    }
  }
  assert(generator == result->n_generators);

  // Family membership cannot cross the partition, even with a constant or
  // otherwise invariant objective. Malformed metadata yields no generators.
  bool was_output = c->indexed_families[0].is_output;
  c->indexed_families[0].is_output = !was_output;
  assert(tlsf_symmetry_detect(c, &second) == TLSF_SYMMETRY_OK);
  assert(second->ranges[0].reason &&
         second->ranges[0].verdict == TLSF_SYMMETRY_NONE);
  for (size_t i = 0; i < second->n_generators; ++i)
    assert(second->generators[i].range != 0);
  tlsf_symmetry_result_free(second);
  c->indexed_families[0].is_output = was_output;

#ifdef SYMMETRY_ALLOC_FAILURE
  allocations = 0;
  assert(tlsf_symmetry_detect(c, &second) == TLSF_SYMMETRY_OK);
  size_t count = allocations;
  tlsf_symmetry_result_free(second);
  for (size_t i = 1; i <= count; ++i) {
    allocations = 0;
    fail_at = i;
    assert(tlsf_symmetry_detect(c, &second) == TLSF_SYMMETRY_NO_MEMORY);
    assert(!second);
  }
  fail_at = 0;
#endif

  // Result storage outlives the conversion, including candidate images and
  // full AP maps; freeing either owner does not affect the other.
  tlsf_conversion_result_free(c);
  for (size_t i = 0; i < result->n_generators; ++i)
    assert(result->generators[i].image[0] < result->n_aps);
  assert(result->ranges[0].candidates[0].image[0] >= result->ranges[0].lo);
  tlsf_symmetry_result_free(result);
}

int main(int argc, char **argv) {
  assert(argc == 2);
  const TlsfSymmetryVerdict symmetric[] = {TLSF_SYMMETRY_SYMMETRIC,
                                           TLSF_SYMMETRY_SYMMETRIC};
  const TlsfSymmetryVerdict cyclic[] = {TLSF_SYMMETRY_CYCLIC};
  const TlsfSymmetryVerdict none[] = {TLSF_SYMMETRY_NONE};
  const unsigned all[] = {7, 3}, rotate[] = {8}, one_swap[] = {2};
  check_fixture(argv[1], "symmetric", 1, symmetric, all);
  check_fixture(argv[1], "cyclic", 1, cyclic, rotate);
  check_fixture(argv[1], "asymmetric", 1, none, one_swap);
  check_fixture(argv[1], "mixed", 2, symmetric, all);
  TlsfSymmetryResult *result = NULL;
  assert(tlsf_symmetry_detect(NULL, &result) == TLSF_SYMMETRY_INVALID &&
         !result);
  assert(tlsf_symmetry_detect(NULL, NULL) == TLSF_SYMMETRY_INVALID);
  tlsf_symmetry_result_free(NULL);
}
