#ifndef TLSF_DECOMPOSE_INTERNAL_H
#define TLSF_DECOMPOSE_INTERNAL_H

#include "tlsf/cover.h"
#include "tlsf/decompose.h"
#include "tlsf/residual_plan.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

[[nodiscard]] TlsfDecomposeResult *
tlsf_decompose_result_from_plan(TlsfSpec *spec, ConstraintCover *cov,
                                const Csnf *csnf,
                                const CsnfComposition *comp,
                                const ResidualPlan *rplan,
                                const TlsfDecomposeOptions *opts);

#endif // TLSF_DECOMPOSE_INTERNAL_H
