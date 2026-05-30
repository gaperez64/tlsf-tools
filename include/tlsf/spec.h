#ifndef TLSF_SPEC_H
#define TLSF_SPEC_H

/// spec.h — top-level TLSF specification structure.
///
/// After parsing, a TlsfSpec holds the full high-level AST.
/// After expand(), the global/parameter/definition tables are empty and
/// all formula lists contain only basic LTL nodes.
///
/// Semantics terminology follows TLSF v1.1/v1.2:
///   - INITIALLY / PRESET   : initial-state formulas (env / sys)
///   - REQUIRE  / ASSERT    : invariant formulas     (env / sys)
///   - ASSUME   / GUARANTEE : general LTL formulas   (env / sys)
///
/// (TLSF v1.0 names ASSUMPTIONS / GUARANTEES / INVARIANTS are aliases.)

#include "tlsf/arena.h"
#include "tlsf/ast.h"
#include "tlsf/intern.h"
#include <stdbool.h>
#include <stdint.h>

// ---------------------------------------------------------------------------
// Semantics / target enumerations
// ---------------------------------------------------------------------------

typedef enum Semantics {
  SEM_MEALY,        ///< standard Mealy semantics
  SEM_MOORE,        ///< standard Moore semantics
  SEM_MEALY_STRICT, ///< strict implication, Mealy
  SEM_MOORE_STRICT, ///< strict implication, Moore
  SEM_MEALY_FINITE, ///< LTLf, Mealy
  SEM_MOORE_FINITE, ///< LTLf, Moore
} Semantics;

typedef enum Target {
  TARGET_MEALY, ///< synthesise a Mealy machine
  TARGET_MOORE, ///< synthesise a Moore machine
} Target;

/// True for the Moore-family semantics (Moore / Strict,Moore / Finite,Moore).
static inline bool semantics_is_moore(Semantics s) {
  return s == SEM_MOORE || s == SEM_MOORE_STRICT || s == SEM_MOORE_FINITE;
}

/// True for the strict-implication semantics.
static inline bool semantics_is_strict(Semantics s) {
  return s == SEM_MEALY_STRICT || s == SEM_MOORE_STRICT;
}

/// True for the finite-word (LTLf) semantics.
static inline bool semantics_is_finite(Semantics s) {
  return s == SEM_MEALY_FINITE || s == SEM_MOORE_FINITE;
}

// ---------------------------------------------------------------------------
// Signal declarations
// ---------------------------------------------------------------------------

typedef struct {
  const char *name; ///< interned signal name
  uint16_t bus_lo;  ///< bus range low  (resolved value; 0 for scalar signals)
  uint16_t bus_hi;  ///< bus range high (resolved value; 0 for scalar signals)
  bool is_bus;      ///< true if this is a bus declaration
  // Parametric bounds: when non-null these integer expressions are evaluated
  // during expand() to fill bus_lo / bus_hi.  Literal ranges leave them null.
  struct Node *bus_lo_expr;
  struct Node *bus_hi_expr;
} SignalDecl;

// ---------------------------------------------------------------------------
// Parameter / definition tables (pre-expansion)
// ---------------------------------------------------------------------------

typedef struct {
  const char *name;    ///< interned parameter name
  int64_t value;       ///< resolved integer value (set during expand())
  int64_t default_val; ///< default value from spec
  bool has_default;
} ParamDecl;

typedef struct {
  const char *name;    ///< interned definition name
  const char **params; ///< interned parameter names (may be nullptr)
  uint16_t param_count;
  Node *body; ///< formula body (pre-expansion)
} DefDecl;

// ---------------------------------------------------------------------------
// Formula lists (one per subsection)
// ---------------------------------------------------------------------------

typedef struct {
  Node **formulas; ///< arena-allocated array of formula pointers
  uint32_t count;
  uint32_t capacity; ///< allocated slots (internal, not serialised)
} FormulaList;

// ---------------------------------------------------------------------------
// Info block
// ---------------------------------------------------------------------------

typedef struct {
  const char *title;         ///< may be nullptr
  const char *description;   ///< may be nullptr
  const char *semantics_str; ///< raw string from spec (for round-trip)
  const char *target_str;
  const char **tags; ///< arena-allocated array of interned tag strings
  uint16_t tag_count;
  Semantics semantics;
  Target target;
} InfoBlock;

// ---------------------------------------------------------------------------
// Top-level specification
// ---------------------------------------------------------------------------

typedef struct {
  Arena *arena;
  InternTable *intern;

  // INFO block
  InfoBlock info;

  // GLOBAL section (pre-expansion; empty after expand())
  ParamDecl *params;
  uint16_t param_count;
  DefDecl *defs;
  uint16_t def_count;

  // MAIN section: signal declarations
  SignalDecl *inputs;
  uint32_t input_count;
  SignalDecl *outputs;
  uint32_t output_count;

  // MAIN section: formula subsections
  // Environment side (assumptions)
  FormulaList initially; ///< INITIALLY
  FormulaList require;   ///< REQUIRE
  FormulaList assume;    ///< ASSUME (a.k.a. ASSUMPTIONS in v1.0)

  // System side (guarantees)
  FormulaList preset;    ///< PRESET
  FormulaList assert_;   ///< ASSERT (a.k.a. INVARIANTS in v1.0)
  FormulaList guarantee; ///< GUARANTEE (a.k.a. GUARANTEES in v1.0)

  // -- Parse-time scratch (capacities for the grow-by-doubling helpers, plus
  //    "current subsection" pointers threaded through the bison actions) --
  uint32_t input_cap;
  uint32_t output_cap;
  uint16_t param_cap;
  uint16_t def_cap;
  uint16_t tag_cap;
  FormulaList *cur_list; ///< formula subsection currently being parsed
  bool cur_is_output;    ///< true while inside an OUTPUTS subsection
} TlsfSpec;

// ---------------------------------------------------------------------------
// Spec lifecycle
// ---------------------------------------------------------------------------

/// Allocate a fresh TlsfSpec with its own arena and intern table.
/// Returns nullptr on OOM.
[[nodiscard]] TlsfSpec *spec_new(void);

/// Free the spec and all arena memory it owns.
void spec_free(TlsfSpec *s);

// ---------------------------------------------------------------------------
// FormulaList helpers
// ---------------------------------------------------------------------------

/// Append a formula to a list.  Returns false on OOM.
[[nodiscard]] bool formula_list_push(TlsfSpec *s, FormulaList *list,
                                     Node *formula);

// ---------------------------------------------------------------------------
// Signal / parameter / definition / tag helpers (used by the parser actions)
// ---------------------------------------------------------------------------

/// Append a signal declaration to the inputs (is_output=false) or outputs
/// (is_output=true) list.  For a bus, lo_expr/hi_expr are the range-bound
/// integer expressions (literal NODE_INT bounds are resolved immediately;
/// parametric bounds are resolved during expand()).  For a scalar pass
/// is_bus=false and null bounds.  Returns false on OOM.
[[nodiscard]] bool spec_add_signal(TlsfSpec *s, bool is_output,
                                   const char *name, bool is_bus,
                                   struct Node *lo_expr, struct Node *hi_expr);

/// Append a parameter declaration.  Returns false on OOM.
[[nodiscard]] bool spec_add_param(TlsfSpec *s, const char *name,
                                  bool has_default, int64_t default_val);

/// Append a definition declaration.  `params` may be nullptr for a nullary
/// definition.  Returns false on OOM.
[[nodiscard]] bool spec_add_def(TlsfSpec *s, const char *name,
                                const char **params, uint16_t param_count,
                                Node *body);

/// Append an INFO tag string.  Returns false on OOM.
[[nodiscard]] bool spec_add_tag(TlsfSpec *s, const char *tag);

// ---------------------------------------------------------------------------
// Semantics / target string parsing (for CLI overrides)
// ---------------------------------------------------------------------------

/// Parse a SEMANTICS value (e.g. "Mealy", "Strict,Moore", "Moore,Finite";
/// qualifiers may appear in either order).  Returns false if unrecognised.
[[nodiscard]] bool parse_semantics(const char *s, Semantics *out);

/// Parse a TARGET value ("Mealy" or "Moore").  Returns false if unrecognised.
[[nodiscard]] bool parse_target(const char *s, Target *out);

#endif // TLSF_SPEC_H
