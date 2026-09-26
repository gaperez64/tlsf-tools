#ifndef TLSF_LIVENESS_CLASS_H
#define TLSF_LIVENESS_CLASS_H

#include "tlsf/ast.h"

#include <stdbool.h>
#include <stdint.h>

typedef enum {
  LIVE_NONE,
  LIVE_GF_ATOM_OR_BOOL,
  LIVE_RESPONSE,
  LIVE_EVENTUAL,
  LIVE_UNTIL,
  LIVE_MIXED_BUCHI,
  LIVE_NESTED_UNSUPPORTED,
  LIVE_UNKNOWN,
} LivenessClass;

typedef struct {
  LivenessClass kind;
  uint32_t n_eventual;
  uint32_t n_response;
  uint32_t n_recurrence;
  uint32_t n_until;
  bool has_nested_temporal;
} LivenessSummary;

LivenessSummary liveness_classify(const Node *root);
const char *liveness_class_name(LivenessClass k);

#endif // TLSF_LIVENESS_CLASS_H
