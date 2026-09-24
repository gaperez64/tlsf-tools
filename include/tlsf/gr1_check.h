#ifndef TLSF_GR1_CHECK_H
#define TLSF_GR1_CHECK_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  const uint8_t *data;
  size_t size;
} TlsfGr1Bytes;

typedef enum {
  TLSF_GR1_CHECK_AUTO = 0,
  TLSF_GR1_CHECK_CERTIFICATE = 1,
  TLSF_GR1_CHECK_REGION = 2,
  TLSF_GR1_CHECK_CLOSED_LOOP = 3,
  TLSF_GR1_CHECK_BOTH = 4,
} TlsfGr1CheckMethod;

typedef enum {
  TLSF_GR1_CHECK_VERIFIED,
  TLSF_GR1_CHECK_REGION_VERIFIED,
  TLSF_GR1_CHECK_CERT_FAILED,
  TLSF_GR1_CHECK_REFUTED,
  TLSF_GR1_CHECK_UNKNOWN,
  TLSF_GR1_CHECK_INVALID,
} TlsfGr1CheckVerdict;

typedef enum {
  TLSF_GR1_CHECK_OK,
  TLSF_GR1_CHECK_BAD_ARGUMENT,
  TLSF_GR1_CHECK_LIMIT,
  TLSF_GR1_CHECK_DEADLINE,
  TLSF_GR1_CHECK_CANCELLED,
  TLSF_GR1_CHECK_ERROR,
} TlsfGr1CheckStatus;

typedef struct {
  TlsfGr1Bytes game_aag;
  TlsfGr1Bytes certificate_aag;
  TlsfGr1Bytes certificate_json;
  TlsfGr1Bytes policy_aag;
  TlsfGr1Bytes policy_json;
} TlsfGr1CheckInput;

typedef struct {
  uint32_t abi_version;
  TlsfGr1CheckMethod method;
  size_t node_cap, cache_cap, max_artifact_bytes;
  uint64_t deadline_mono_ns;
  int (*cancelled)(void *);
  void *cancel_ctx;
} TlsfGr1CheckOptions;

typedef struct {
  TlsfGr1CheckVerdict verdict;
  char *json; /* malloc-owned, NUL terminated; clear once after use */
  size_t json_size, peak_nodes;
  TlsfGr1CheckStatus status;
  char stage[48], message[256];
} TlsfGr1CheckResult;

/* The checker validates sidecars and game structure independently of the
 * solver. Non-OK status never carries a verified verdict or JSON artifact. */
TlsfGr1CheckStatus tlsf_gr1_check(const TlsfGr1CheckInput *input,
                                  const TlsfGr1CheckOptions *options,
                                  TlsfGr1CheckResult *result);
void tlsf_gr1_check_result_clear(TlsfGr1CheckResult *result);

#ifdef __cplusplus
}
#endif
#endif
