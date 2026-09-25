#ifndef TLSF_SPEC_INTERNAL_H
#define TLSF_SPEC_INTERNAL_H

#include "tlsf/spec.h"

/// Append environment-fairness assumptions for every declared input.
///
/// Scalar inputs receive `G F i` and `G F !i`.  Bus inputs receive equivalent
/// inclusive quantified assumptions over their original declaration bounds so
/// a later expand() turns them into per-bit formulas.  Returns false on OOM.
[[nodiscard]] bool spec_add_fair_environment(TlsfSpec *spec);

/// The spellings parse_semantics() and parse_target() accept, e.g.
/// "Strict,Mealy" and "Moore".
[[nodiscard]] const char *spec_semantics_name(Semantics s);
[[nodiscard]] const char *spec_target_name(Target t);

#endif // TLSF_SPEC_INTERNAL_H
