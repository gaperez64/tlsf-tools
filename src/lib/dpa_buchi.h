#ifndef TLSF_DPA_BUCHI_H
#define TLSF_DPA_BUCHI_H
#include "tlsf/dpa.h"
#ifdef __cplusplus
extern "C" {
#endif
// Private Stage 1/2 view: HasTag Pi2 plus the budget's admission policy.
// Production selects the proved default. States remember the prior mark.
// The ordinary DPA successor/label APIs apply; edge priorities are 0/1 and
// every row has the same priority as its source state's acceptance mark.
TlsfDpaStatus dpa_buchi_create(const TlsfAstNode *root,
                               const char *const *names, uint32_t count,
                               const TlsfDpaBudget *budget, TlsfDpa **out,
                               char *klass);
// Boolean equality first, then optional language equality in the proved DPA
// fragment. Outside it, unknown is false: never manufacture source bindings.
TlsfDpaStatus dpa_formula_equal(const TlsfAstNode *a, const TlsfAstNode *b,
                                const char *const *names, uint32_t count,
                                const TlsfDpaBudget *budget, bool temporal,
                                bool *equal);
bool dpa_labels_partition(TlsfDpa *ctx, const uint32_t *labels, size_t count);
#ifdef __cplusplus
}
#endif
#endif
