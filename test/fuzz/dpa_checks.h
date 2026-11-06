#ifndef TLSF_FUZZ_DPA_CHECKS_H
#define TLSF_FUZZ_DPA_CHECKS_H
#include "tlsf/convert.h"
#include "tlsf/dpa.h"

typedef struct {
  const TlsfDpaLabelNode *borrowed;
  TlsfDpaLabelNode copy;
  unsigned char visit, value;
  unsigned assignment;
} FuzzLabel;

typedef struct {
  const TlsfDpaEdge *borrowed;
  TlsfDpaEdge *copy;
  size_t count;
} FuzzRow;

typedef struct {
  TlsfDpa *dpa;
  const TlsfConversionResult *spec;
  size_t max_states;
  const char *names[8];
  FuzzRow rows[64];
  size_t row_count;
  FuzzLabel *labels;
  size_t label_capacity;
  unsigned assignment;
} FuzzDpaChecks;

bool fuzz_dpa_reason(TlsfDpaStatus status, bool host_limit);
void fuzz_dpa_checks_init(FuzzDpaChecks *checks, TlsfDpa *dpa,
                          const TlsfConversionResult *spec, size_t max_states);
bool fuzz_dpa_label(FuzzDpaChecks *checks, TlsfDpaLabel label);
void fuzz_dpa_post(FuzzDpaChecks *checks, TlsfDpaStatus status,
                   TlsfDpaState state, const TlsfDpaEdge *edges, size_t count);
void fuzz_dpa_checks_free(FuzzDpaChecks *checks);
#endif
