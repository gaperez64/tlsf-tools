#ifndef TLSF_EXPAND_CHECK_H
#define TLSF_EXPAND_CHECK_H

#include "tlsf/spec.h"

// Check the unexpanded syntax, including unused definitions and dead branches.
bool expand_check(const TlsfSpec *spec);
// Complete, interned §4.5 flattened name, shared by validation and expansion.
const char *expand_signal_name(const TlsfSpec *spec, const char *bus,
                               int64_t index);
// Check flattened names and exact §4.4 comparisons (direct buses and lexical
// aliases) after resolving bounds. Other widths use the expanded actual bus.
bool expand_check_resolved(const TlsfSpec *spec);

#endif
