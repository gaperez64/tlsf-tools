#ifndef TLSF_GR1_CHECK_INTERNAL_H
#define TLSF_GR1_CHECK_INTERNAL_H

/// gr1_check_internal.h — the checker engine shared by the tlsf_gr1_check()
/// library entry point and the tlsfcertcheck command line.

#include "tlsf/oxidd_options.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/// Process exit codes; the library maps them to TlsfGr1CheckVerdict.
enum {
  EXIT_VERIFIED = 0,
  EXIT_REFUTED = 1,
  EXIT_ERROR = 2,
  EXIT_UNKNOWN = 3,
  EXIT_INVALID = 4,
  EXIT_INTERNAL = 5,
  EXIT_CERT_FAILED = 6,
};

typedef enum {
  METHOD_AUTO,
  METHOD_CERTIFICATE,
  METHOD_CLOSED_LOOP,
  METHOD_BOTH,
  METHOD_REGION
} Method;

typedef struct {
  const char *game_path;
  const char *policy_path;
  const char *policy_json_path;
  const char *certificate_path;
  const char *certificate_json_path;
  const char *json_out_path;
  const char *emit_path;
  Method method;
  double timeout;
  size_t node_cap, cache_cap;
  size_t effective_node_cap, effective_cache_cap;
  bool cache_cap_explicit;
  bool stats;
  bool test_unspecialized_policy;
  bool test_rebuild_successor;
  const uint8_t *game_bytes, *policy_bytes, *certificate_bytes;
  size_t game_size, policy_size, certificate_size;
  const char *policy_json_text, *certificate_json_text;
  char **json_bytes;
  size_t *json_size;
  size_t max_artifact_bytes;
  bool *json_limited;
  bool *json_allocation_failed;
  uint64_t deadline_mono_ns;
  int (*cancelled)(void *);
  void *cancel_ctx;
  bool quiet;
} Options;

/// The inner-node and apply-cache capacities OxiDD actually allocates for a
/// requested cap, or false when the request exceeds its limits.
[[nodiscard]] bool gr1_check_node_capacity(size_t requested, size_t *effective);
[[nodiscard]] bool gr1_check_cache_capacity(size_t requested,
                                            size_t *effective);

/// Run the configured methods and return an exit code.  Takes ownership of
/// the two optional sidecar path strings.  Unless `options.quiet`, prints the
/// verdict lines to stdout and diagnostics to stderr.
int gr1_check_run(Options options, char *owned_policy_json,
                  char *owned_cert_json, size_t *peak_out,
                  OxiddFailure *failure_out);

#endif // TLSF_GR1_CHECK_INTERNAL_H
