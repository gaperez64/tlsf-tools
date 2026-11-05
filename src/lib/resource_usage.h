#ifndef TLSF_RESOURCE_USAGE_H
#define TLSF_RESOURCE_USAGE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/resource.h>
#ifdef __APPLE__
#include <mach/mach.h>
#endif

static inline uint64_t tlsf_rss_kib_to_bytes(uint64_t kib) {
  return kib > UINT64_MAX / 1024u ? UINT64_MAX : kib * 1024u;
}

static inline bool tlsf_peak_rss_bytes(uint64_t *bytes) {
  struct rusage usage;
  if (getrusage(RUSAGE_SELF, &usage) != 0)
    return false;
  uint64_t peak = usage.ru_maxrss > 0 ? (uint64_t)usage.ru_maxrss : 0;
#ifdef __APPLE__
  *bytes = peak; // Darwin reports bytes; Linux and BSD report KiB.
#else
  *bytes = tlsf_rss_kib_to_bytes(peak);
#endif
  return true;
}

// Current RSS, not the high-water mark: released candidate memory must not
// consume the next solve's allowance. Both backends return bytes, independent
// of the allocator and the system's page size.
static inline bool tlsf_current_rss_bytes(uint64_t *bytes) {
#ifdef __APPLE__
  mach_task_basic_info_data_t info;
  mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;
  if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, (task_info_t)&info,
                &count) != KERN_SUCCESS)
    return false;
  *bytes = (uint64_t)info.resident_size;
  return true;
#elif defined(__linux__)
  FILE *file = fopen("/proc/self/status", "r");
  if (!file)
    return false;
  char line[256];
  bool found = false;
  while (fgets(line, sizeof line, file)) {
    unsigned long long kib = 0;
    if (sscanf(line, "VmRSS: %llu kB", &kib) == 1) {
      *bytes = tlsf_rss_kib_to_bytes((uint64_t)kib);
      found = true;
      break;
    }
  }
  fclose(file);
  return found;
#else
  (void)bytes;
  return false;
#endif
}

#endif
