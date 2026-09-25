#include "tlsf/gr1_check.h"
#include "tlsf/native.h"
#include <oxidd/capi.h>

/* Test assertions also perform checked I/O; keep them active in release builds. */
#undef NDEBUG
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __linux__
#include <dirent.h>
#include <errno.h>
#include <sched.h>
#include <unistd.h>
#endif

#ifdef __linux__
/* Observe the GC task itself so asynchronous retirement is an immediate test
 * failure even when the allocation error is timing dependent. */
static long gc_thread_tid(void) {
  DIR *tasks = opendir("/proc/self/task");
  assert(tasks);
  long tid = 0;
  struct dirent *entry;
  while ((entry = readdir(tasks))) {
    if (entry->d_name[0] == '.')
      continue;
    char path[128];
    int len = snprintf(path, sizeof path, "/proc/self/task/%s/comm",
                       entry->d_name);
    assert(len > 0 && (size_t)len < sizeof path);
    FILE *comm = fopen(path, "r");
    if (!comm) /* A thread may exit between readdir and fopen. */
      continue;
    char name[32];
    bool match = fgets(name, sizeof name, comm) &&
                 strcmp(name, "oxidd mi gc\n") == 0;
    assert(fclose(comm) == 0);
    if (match) {
      tid = strtol(entry->d_name, NULL, 10);
      break;
    }
  }
  assert(closedir(tasks) == 0);
  return tid;
}

static bool gc_thread_alive(long tid) {
  char path[128];
  int len = snprintf(path, sizeof path, "/proc/self/task/%ld", tid);
  assert(len > 0 && (size_t)len < sizeof path);
  if (access(path, F_OK) == 0)
    return true;
  assert(errno == ENOENT);
  return false;
}
#endif

/* Both loops deliberately stay on the calling thread. Each check constructs
 * and destroys its own OxiDD manager, as the native certificate checker does. */
static void manager_lifetimes(void) {
  for (unsigned i = 0; i < 1000; ++i) {
    oxidd_bdd_manager_t manager = oxidd_bdd_manager_new(4096, 256, 1);
    assert(manager._p);
    oxidd_bdd_manager_add_vars(manager, 3);
    oxidd_bdd_t x = oxidd_bdd_var(manager, 0);
    oxidd_bdd_t y = oxidd_bdd_var(manager, 1);
    oxidd_bdd_t both = oxidd_bdd_and(x, y);
    assert(both._p && oxidd_bdd_satisfiable(both));
#ifdef __linux__
    long gc_tid = 0;
    for (unsigned attempt = 0; attempt < 1000 && !gc_tid; ++attempt) {
      gc_tid = gc_thread_tid();
      if (!gc_tid)
        sched_yield();
    }
    assert(gc_tid);
#endif
    oxidd_bdd_unref(both);
    oxidd_bdd_unref(y);
    oxidd_bdd_unref(x);
    oxidd_bdd_manager_unref(manager);
#ifdef __linux__
    /* /proc can retain a task entry briefly even after pthread_join. */
    for (unsigned attempt = 0; attempt < 1000 && gc_thread_alive(gc_tid);
         ++attempt)
      sched_yield();
    assert(!gc_thread_alive(gc_tid));
#endif
  }
}

static TlsfGr1Bytes load(const char *directory, const char *name) {
  char path[1024];
  int len = snprintf(path, sizeof path, "%s/%s", directory, name);
  assert(len > 0 && (size_t)len < sizeof path);
  FILE *file = fopen(path, "rb");
  assert(file);
  assert(fseek(file, 0, SEEK_END) == 0);
  long size = ftell(file);
  assert(size > 0);
  rewind(file);
  uint8_t *data = malloc((size_t)size);
  assert(data && fread(data, 1, (size_t)size, file) == (size_t)size);
  assert(fclose(file) == 0);
  return (TlsfGr1Bytes){data, (size_t)size};
}

static void checker_lifetimes(const char *directory, unsigned iterations) {
  TlsfGr1CheckInput input = {
      .game_aag = load(directory, "target.game.aag"),
      .certificate_aag = load(directory, "target.certificate.aag"),
      .certificate_json = load(directory, "target.certificate.aag.json"),
      .policy_aag = load(directory, "target.policy.aag"),
      .policy_json = load(directory, "target.policy.aag.json"),
  };
  TlsfGr1CheckOptions options = {
      .abi_version = TLSF_NATIVE_ABI_VERSION,
      .method = TLSF_GR1_CHECK_CERTIFICATE,
      .node_cap = 1u << 22,
      .cache_cap = 1u << 20,
      .max_artifact_bytes = 64u << 20,
  };
  for (unsigned i = 0; i < iterations; ++i) {
    if (i % 100 == 0)
      fprintf(stderr, "checker lifetime %u/%u\n", i, iterations);
    TlsfGr1CheckResult result = {0};
    TlsfGr1CheckStatus status = tlsf_gr1_check(&input, &options, &result);
    if (status != TLSF_GR1_CHECK_OK ||
        result.verdict != TLSF_GR1_CHECK_VERIFIED) {
      fprintf(stderr, "check %u: status=%d verdict=%d stage=%s message=%s\n",
              i, status, result.verdict, result.stage, result.message);
      abort();
    }
    tlsf_gr1_check_result_clear(&result);
  }
  free((void *)input.game_aag.data);
  free((void *)input.certificate_aag.data);
  free((void *)input.certificate_json.data);
  free((void *)input.policy_aag.data);
  free((void *)input.policy_json.data);
}

int main(int argc, char **argv) {
  assert(argc == 3 || argc == 4);
  if (strcmp(argv[1], "manager") == 0)
    manager_lifetimes();
  else if (strcmp(argv[1], "checker") == 0)
    checker_lifetimes(argv[2], argc == 4 ? (unsigned)strtoul(argv[3], NULL, 10)
                                           : 300);
  else
    abort();
  return 0;
}
