#ifndef TLSF_CONVERSION_INTERNAL_H
#define TLSF_CONVERSION_INTERNAL_H

#include "tlsf/apset.h"
#include "tlsf/decompose.h"
#include "tlsf/expand.h"
#include "print_ltlxba.h"

// Shared conversion steps and metadata producers; none builds a decomposition.
bool conversion_prepare(TlsfSpec *spec, const char *semantics,
                        const char *target, const ParamOverride *overrides,
                        size_t count, bool fair_environment, const char *tool);
const char *conversion_semantics_name(Semantics semantics);
const char *conversion_target_name(Target target);
char *conversion_dup_cstr(const char *text);
void conversion_free_strings(char **items, uint32_t count);
void conversion_seed_signals(ApTable *aps, const TlsfSpec *spec);
void conversion_intern_aps(ApTable *aps, const Node *node);
bool conversion_collect_signals(const ApTable *aps, const bool *seen,
                                uint8_t flag, bool lower, char ***items,
                                uint32_t *count);
bool conversion_collect_families(TlsfDecomposeIndexedFamily **families,
                                 uint32_t *count, const TlsfSpec *spec,
                                 bool lower);
char *conversion_render_ltl(const Node *root, LtlFormat format, bool finite,
                            bool lower);
#endif
