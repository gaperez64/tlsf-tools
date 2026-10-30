#ifndef TLSF_RESIDUAL_SAT_H
#define TLSF_RESIDUAL_SAT_H

#include "section_pattern.h"

// True only on a completed, positive infinite-word satisfiability check of
// INITIALLY && G REQUIRE && ASSUMPTIONS. All failures retain the dropped set.
bool residual_env_satisfiable(const SectionPatternView *dropped);

#endif
