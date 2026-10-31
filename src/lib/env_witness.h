#ifndef TLSF_ENV_WITNESS_H
#define TLSF_ENV_WITNESS_H

#include "section_pattern.h"

enum { ENV_WITNESS_MAX_APS = 8, ENV_WITNESS_MAX_LENGTH = 4 };
enum { ENV_WITNESS_WORK_BUDGET = 200000 };

typedef enum {
  ENV_WITNESS_UNKNOWN,
  ENV_WITNESS_SATISFIABLE,
} EnvWitnessResult;

// An infinite word: letters[0..length), then letters[loop..length) forever.
// Each letter is a bitset indexed by aps; unlisted atoms are false.
typedef struct {
  const char *const *aps;
  const uint8_t *letters;
  unsigned ap_count, length, loop;
} EnvLasso;

// Certify INITIALLY && G REQUIRE && ASSUMPTIONS on this infinite word.
// False on a word, unsupported syntax and exhausted budgets all mean UNKNOWN.
EnvWitnessResult env_lasso_check(const SectionPatternView *dropped,
                                 const EnvLasso *word, uint32_t work_budget);

// Search bounded lassos. Only a completed positive check returns SATISFIABLE;
// UNKNOWN must keep the group. The budget counts node and fixpoint updates.
EnvWitnessResult env_witness_search(const SectionPatternView *dropped,
                                    uint32_t work_budget);

#endif
