#ifndef TLSF_INTERN_H
#define TLSF_INTERN_H

/// intern.h — string interning table.
///
/// All identifier strings (signal names, definition names, parameter names)
/// are interned: intern() returns a canonical const char * such that
///   intern(a, s1) == intern(a, s2)  ⟺  strcmp(s1, s2) == 0
///
/// The interned string storage lives in the arena; the hash table itself is
/// heap-allocated (separate lifetime so it can be freed after expansion
/// without touching the arena strings that the AST still references).

#include "tlsf/arena.h"

typedef struct InternTable InternTable;

/// Create an intern table.  Strings are copied into `arena`.
[[nodiscard]] InternTable *intern_table_new(Arena *arena);

/// Free the hash table structure (not the strings — those are in the arena).
void intern_table_free(InternTable *t);

/// Intern a NUL-terminated string.  Returns a canonical pointer valid for
/// the lifetime of the arena.  Returns nullptr on OOM.
[[nodiscard]] const char *intern(InternTable *t, const char *s);

/// Intern a string of known length (need not be NUL-terminated).
[[nodiscard]] const char *intern_n(InternTable *t, const char *s, size_t len);

#endif // TLSF_INTERN_H
