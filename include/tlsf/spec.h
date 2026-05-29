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
  SEM_MEALY,            ///< standard Mealy semantics
  SEM_MOORE,            ///< standard Moore semantics
  SEM_MEALY_STRICT,     ///< strict implication, Mealy
  SEM_MOORE_STRICT,     ///< strict implication, Moore
  SEM_MEALY_FINITE,     ///< LTLf, Mealy
  SEM_MOORE_FINITE,     ///< LTLf, Moore
} Semantics;

typedef enum Target {
  TARGET_MEALY,         ///< synthesise a Mealy machine
  TARGET_MOORE,         ///< synthesise a Moore machine
} Target;

// ---------------------------------------------------------------------------
// Signal declarations
// ---------------------------------------------------------------------------

typedef struct {
  const char *name; ///< interned signal name
  uint16_t bus_lo;  ///< bus range low  (0 for scalar signals)
  uint16_t bus_hi;  ///< bus range high (0 for scalar signals)
  bool is_bus;      ///< true if this is a bus declaration
} SignalDecl;

// ---------------------------------------------------------------------------
// Parameter / definition tables (pre-expansion)
// ---------------------------------------------------------------------------

typedef struct {
  const char *name;   ///< interned parameter name
  int64_t value;      ///< resolved integer value (set during expand())
  int64_t default_val;///< default value from spec
  bool has_default;
} ParamDecl;

typedef struct {
  const char *name;     ///< interned definition name
  const char **params;  ///< interned parameter names (may be nullptr)
  uint16_t param_count;
  Node *body;           ///< formula body (pre-expansion)
} DefDecl;

// ---------------------------------------------------------------------------
// Formula lists (one per subsection)
// ---------------------------------------------------------------------------

typedef struct {
  Node **formulas;   ///< arena-allocated array of formula pointers
  uint32_t count;
  uint32_t capacity; ///< allocated slots (internal, not serialised)
} FormulaList;

// ---------------------------------------------------------------------------
// Info block
// ---------------------------------------------------------------------------

typedef struct {
  const char *title;       ///< may be nullptr
  const char *description; ///< may be nullptr
  const char *semantics_str; ///< raw string from spec (for round-trip)
  const char *target_str;
  const char **tags;       ///< arena-allocated array of interned tag strings
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

#endif // TLSF_SPEC_H
