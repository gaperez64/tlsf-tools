#ifndef TLSF_REWRITE_H
#define TLSF_REWRITE_H

/// rewrite.h — meaning-preserving LTL formula transformations.
///
/// These operate on a fully-expanded formula tree (no high-level nodes) and
/// mirror the corresponding `syfco` transformations.  Each pass allocates new
/// nodes from the arena; the input tree is left untouched.  Every transform is
/// equivalence-preserving, so the rewritten formula can be checked against the
/// original with `ltlfilt --equivalent-to`.
///
/// Operator replacement:
///   RW_NO_WEAK_UNTIL : a W b => (a U b) || G a
///   RW_NO_RELEASE    : a R b => b W (a && b)
///   RW_NO_FINALLY    : F a   => true U a
///   RW_NO_GLOBALLY   : G a   => false R a
/// Push inwards:
///   RW_PUSH_G_IN     : G(a && b) => G a && G b
///   RW_PUSH_F_IN     : F(a || b) => F a || F b
///   RW_PUSH_X_IN     : X(a && b) => X a && X b,  X(a || b) => X a || X b
/// Pull outwards:
///   RW_PULL_G_OUT    : G a && G b => G(a && b)
///   RW_PULL_F_OUT    : F a || F b => F(a || b)
///   RW_PULL_X_OUT    : X a && X b => X(a && b),  X a || X b => X(a || b)
/// Other:
///   RW_NNF           : convert to negation normal form (applied first)
///   RW_SIMPLIFY_WEAK : constant folding / redundancy removal (`syfco -s0`)
///
/// `syfco -s1` (strong simplify) is the combination
///   RW_SIMPLIFY_WEAK | RW_NNF | RW_NO_WEAK_UNTIL | RW_NO_RELEASE |
///   RW_PULL_G_OUT | RW_PULL_F_OUT | RW_PULL_X_OUT
/// (see RW_STRONG_SIMPLIFY).

#include "tlsf/arena.h"
#include "tlsf/ast.h"

typedef enum RewriteFlags {
  RW_NONE = 0,
  RW_NNF = 1u << 0,
  RW_NO_WEAK_UNTIL = 1u << 1,
  RW_NO_RELEASE = 1u << 2,
  RW_NO_FINALLY = 1u << 3,
  RW_NO_GLOBALLY = 1u << 4,
  RW_PUSH_G_IN = 1u << 5,
  RW_PUSH_F_IN = 1u << 6,
  RW_PUSH_X_IN = 1u << 7,
  RW_PULL_G_OUT = 1u << 8,
  RW_PULL_F_OUT = 1u << 9,
  RW_PULL_X_OUT = 1u << 10,
  RW_SIMPLIFY_WEAK = 1u << 11,

  /// `syfco -nd`: replace weak-until, finally and globally.
  RW_NO_DERIVED = RW_NO_WEAK_UNTIL | RW_NO_FINALLY | RW_NO_GLOBALLY,

  /// `syfco -s1`: weak-simplify, NNF, then the standard replace/pull set.
  RW_STRONG_SIMPLIFY = RW_SIMPLIFY_WEAK | RW_NNF | RW_NO_WEAK_UNTIL |
                       RW_NO_RELEASE | RW_PULL_G_OUT | RW_PULL_F_OUT |
                       RW_PULL_X_OUT,
} RewriteFlags;

/// Apply the selected transformations to `root` and return the result.
/// `flags` is a bitwise-or of RewriteFlags.  Returns nullptr on OOM.
/// If `flags == RW_NONE` the input is returned unchanged.
[[nodiscard]] Node *apply_rewrites(Arena *a, Node *root, unsigned flags);

#endif // TLSF_REWRITE_H
