#ifndef TLSF_ARENA_H
#define TLSF_ARENA_H

/// arena.h — slab-based bump allocator.
///
/// All AST nodes, interned strings, and temporary expansion data are
/// allocated from a single Arena.  Teardown is a single arena_free() call.
///
/// Usage:
///   Arena *a = arena_new(ARENA_DEFAULT_SLAB_SIZE);
///   Foo   *f = ARENA_ALLOC(a, Foo);   // zero-initialised
///   arena_free(a);

#include <stdbool.h>
#include <stddef.h>

/// Default slab size: 4 MiB — large enough for typical TLSF specs.
#define ARENA_DEFAULT_SLAB_SIZE ((size_t)(4u * 1024u * 1024u))

typedef struct ArenaSlabArena Arena;

/// Allocate a new arena.  Returns nullptr on allocation failure.
[[nodiscard]] Arena *arena_new(size_t slab_size);

/// Allocate `size` bytes aligned to `align` from the arena.
/// Returns nullptr on allocation failure.
[[nodiscard]] void *arena_alloc_aligned(Arena *a, size_t size, size_t align);

/// Checked array allocation; multiplication overflow is an allocation failure.
[[nodiscard]] void *arena_alloc_array(Arena *a, size_t size, size_t count,
                                      size_t align);

/// Sticky for the lifetime of the arena, even if later allocations succeed.
[[nodiscard]] bool arena_failed(const Arena *a);

/// Free the arena and all memory it owns.  Safe to call with nullptr.
void arena_free(Arena *a);

/// Typed allocation macro: ARENA_ALLOC(arena, Type) → Type *
/// The returned pointer is zero-initialised.
#define ARENA_ALLOC(arena, Type)                                               \
  ((Type *)arena_alloc_aligned((arena), sizeof(Type), _Alignof(Type)))

/// Typed array allocation: ARENA_ALLOC_N(arena, Type, n) → Type *
#define ARENA_ALLOC_N(arena, Type, n)                                          \
  ((Type *)arena_alloc_array((arena), sizeof(Type), (n), _Alignof(Type)))

#endif // TLSF_ARENA_H
