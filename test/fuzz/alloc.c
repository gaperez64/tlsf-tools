#define _POSIX_C_SOURCE 200809L
#include "decode.h"
#include "dpa_checks.h"
#include "tlsf/convert.h"
#include "tlsf/dpa.h"
#include "tlsf/spec.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>

/* Only caller-thread C allocations are refused, as in native_api_failure.
 * OxiDD owns its Rust allocator; tlsf_oxidd_manager_new uses one worker.
 * A fixed registry avoids allocating in the wrappers. Registry exhaustion is
 * itself ENOMEM. Frees after disarming still remove registered pointers. */
static _Thread_local void *live[8192];
static _Thread_local size_t live_count, calls, fail_at;
static _Thread_local bool armed, fired, host_only;

static bool refuse(void) {
  if (!armed)
    return false;
  if (++calls != fail_at && live_count < sizeof live / sizeof *live)
    return false;
  fired = true;
  errno = ENOMEM;
  return true;
}

static void remember(void *p) {
  if (armed && p)
    live[live_count++] = p;
}

static size_t find(void *p) {
  for (size_t i = 0; i < live_count; ++i)
    if (live[i] == p)
      return i;
  return live_count;
}

static void forget(size_t i) {
  if (i < live_count) {
    live[i] = live[--live_count];
    live[live_count] = NULL;
  }
}

void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void __real_free(void *);
void *__wrap_malloc(size_t);
void *__wrap_calloc(size_t, size_t);
void *__wrap_realloc(void *, size_t);
void __wrap_free(void *);

void *__wrap_malloc(size_t n) {
  if (host_only)
    return __real_malloc(n);
  if (refuse())
    return NULL;
  void *p = __real_malloc(n);
  remember(p);
  return p;
}

void *__wrap_calloc(size_t n, size_t size) {
  if (host_only)
    return __real_calloc(n, size);
  if (refuse())
    return NULL;
  void *p = __real_calloc(n, size);
  remember(p);
  return p;
}

void *__wrap_realloc(void *p, size_t n) {
  if (host_only)
    return __real_realloc(p, n);
  if (refuse())
    return NULL;
  size_t i = find(p);
  void *q = __real_realloc(p, n);
  if (q) {
    if (i < live_count)
      live[i] = q;
    else
      remember(q);
  } else if (!n)
    forget(i);
  return q;
}

void __wrap_free(void *p) {
  forget(find(p));
  __real_free(p);
}

/* Rust's infallible allocator also references malloc in the static archive.
 * During DPA work, inject/track only the project's existing host seam, as in
 * dpa_contract/native_api_failure; refusing Rust allocations just aborts Rust.
 * All DPA C allocations pass through oxidd_host_calloc (dpa.c). */
void *__wrap_oxidd_host_calloc(size_t n, size_t size);
void *__wrap_oxidd_host_calloc(size_t n, size_t size) {
  if (refuse())
    return NULL;
  void *p = __real_calloc(n, size);
  remember(p);
  return p;
}

void *__real_arena_alloc_aligned(Arena *, size_t, size_t);
void *__real_arena_alloc_array(Arena *, size_t, size_t, size_t);
void *__wrap_arena_alloc_aligned(Arena *, size_t, size_t);
void *__wrap_arena_alloc_array(Arena *, size_t, size_t, size_t);

/* A guaranteed array overflow uses the public API to mark the arena failed,
 * just like a real allocation failure. Slab failures use the heap wrappers. */
void *__wrap_arena_alloc_aligned(Arena *a, size_t size, size_t align) {
  if (refuse())
    return __real_arena_alloc_array(a, SIZE_MAX, 2, align);
  return __real_arena_alloc_aligned(a, size, align);
}

void *__wrap_arena_alloc_array(Arena *a, size_t size, size_t n, size_t align) {
  if (refuse())
    return __real_arena_alloc_array(a, SIZE_MAX, 2, align);
  return __real_arena_alloc_array(a, size, n, align);
}

static void arm(unsigned selected, unsigned phase) {
  armed = selected == phase;
  calls = 0;
  fired = false;
}

static bool dpa_ok(TlsfDpaStatus status) {
  // A1: Only reasons permitted by the configured limits may decline valid LTL.
  if (!(fuzz_dpa_reason(status, true)))
    abort();
  return status.code == TLSF_DPA_OK;
}

typedef struct {
  bool parsed, converted, refused;
  TlsfDpaStatus status;
} Result;

static Result run(char *text, size_t length, unsigned phase, bool general) {
  Result result = {.status = {TLSF_DPA_OK, TLSF_DPA_NONE}};
  size_t start = live_count;
  FILE *stream = fmemopen(text, length, "r");
  if (!stream)
    return result;
  arm(phase, 0);
  TlsfSpec *spec = spec_parse(stream, "fuzz-alloc");
  armed = false;
  result.refused |= fired;
  fclose(stream);
  // A2: Generator output must parse unless this run actually refused memory.
  if (!(spec || fired))
    abort();
  result.parsed = spec != NULL;
  spec_free(spec);
  if (!result.parsed)
    goto done;

  arm(phase, 1);
  TlsfConversionResult *converted = tlsf_convert(text, NULL);
  armed = false;
  result.refused |= fired;
  result.converted = converted != NULL;
  /* convert.h documents NULL for unsupported input/allocation failure.
   * Both results must clean up; an unfired run is compared with its baseline.
   */
  if (!converted)
    goto done;
  TlsfDpaBudget budget = {.max_states = 64,
                          .max_host_bytes = 4u << 20,
                          .bdd_nodes = 4096,
                          .bdd_cache = 1024,
                          .allow_unproved = general};
  TlsfDpa *dpa = (TlsfDpa *)(uintptr_t)1;
  arm(phase, 2);
  host_only = true;
  result.status = tlsf_dpa_create(
      tlsf_ast_root(converted->ast), (const char *const *)converted->inputs,
      converted->n_inputs, (const char *const *)converted->outputs,
      converted->n_outputs, &budget, &dpa);
  if (!dpa_ok(result.status)) {
    // A3: dpa.h:66 requires failed construction to leave the output NULL.
    if (!(!dpa))
      abort();
  } else {
    FuzzDpaChecks checks;
    fuzz_dpa_checks_init(&checks, dpa, converted, budget.max_states);
    TlsfDpaState queue[64] = {tlsf_dpa_initial(dpa)};
    size_t count = 1;
    for (size_t at = 0; at < count; ++at) {
      const TlsfDpaEdge *edges = (const TlsfDpaEdge *)(uintptr_t)1;
      size_t n = SIZE_MAX;
      result.status = tlsf_dpa_successors(dpa, queue[at], &edges, &n);
      bool success = dpa_ok(result.status);
      // Snapshot storage belongs to the harness, outside allocation injection.
      bool was_armed = armed;
      armed = false;
      if (!success) {
        // A4: dpa.h:107 promises an empty row on failed expansion.
        if (!(!edges && !n))
          abort();
      } else {
        // A8: Success must publish a whole nonempty row (dpa.h:107).
        if (!(edges && n))
          abort();
      }
      fuzz_dpa_post(&checks, result.status, queue[at], edges, n);
      armed = was_armed;
      if (!success)
        break;
      for (size_t e = 0; e < n; ++e) {
        size_t i = 0;
        while (i < count && queue[i] != edges[e].successor)
          ++i;
        if (i == count) {
          // A5: The max_states budget bounds even lazily discovered states.
          if (!(count < 64))
            abort();
          queue[count++] = edges[e].successor;
        }
      }
    }
    armed = false;
    fuzz_dpa_checks_free(&checks);
  }
  armed = false;
  result.refused |= fired;
  tlsf_dpa_free(dpa);
  host_only = false;
  tlsf_conversion_result_free(converted);
done:
  // A6: Every C heap allocation made while armed must be released on all exits.
  if (!(live_count == start))
    abort();
  return result;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  unsigned phase = size ? data[0] % 3 : 0;
  bool general = size && (data[0] & 4);
  fail_at = size > 1 ? data[1] : 0;
  if (size > 2)
    fail_at |= (size_t)data[2] << 8;
  size_t prefix = size < 3 ? size : 3;
  char text[TLSF_FUZZ_TEXT_CAPACITY];
  size_t length =
      tlsf_fuzz_decode(data ? data + prefix : data, size - prefix, text);
  Result baseline = run(text, length, 3, general); // No phase is armed.
  Result injected = run(text, length, phase, general);
  // A7: An unfired refusal cannot change parse/conversion results or DPA
  // status.
  if (!(injected.refused || (injected.parsed == baseline.parsed &&
                             injected.converted == baseline.converted &&
                             injected.status.code == baseline.status.code &&
                             injected.status.reason == baseline.status.reason)))
    abort();
  return 0;
}
