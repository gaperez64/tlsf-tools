#ifndef TLSF_AIGER_H
#define TLSF_AIGER_H

/// aiger.h — a minimal ASCII-AIGER (`aag`) toolkit: build an and-inverter graph
/// (inputs / latches / and-gates / named outputs), compile a temporal-free
/// Boolean formula into it, read an `aag` (e.g. from `ltlsynt --aiger`), and
/// merge one AIG into another by signal name (shared inputs, outputs wired by
/// name).  Enough to stitch certified combinational controllers and per-cluster
/// synthesized strategies into one controller circuit.
///
/// Literals follow the AIGER convention: even = variable*2 (positive), odd =
/// its negation; 0 = false, 1 = true.

#include "tlsf/ast.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

#define AIG_FALSE 0u
#define AIG_TRUE 1u

typedef struct Aig Aig;

[[nodiscard]] Aig *aig_new(void);
void aig_free(Aig *g);

/// Add an input named `name`; returns its (positive) literal.  Also registers
/// it as an available signal for `aig_compile`/`aig_merge` lookups.
uint32_t aig_input(Aig *g, const char *name);

/// Add a latch with next-state function `next` and reset value 0/1; returns its
/// current-state positive literal.  AIGER 1.9 also permits self-literal
/// uninitialised resets when reading external files; solvers decide whether
/// those are supported for their profile.
uint32_t aig_latch(Aig *g, uint32_t next, uint32_t reset);

/// Add a named latch.  The name is emitted as an AIGER latch symbol and is
/// available through `aig_latch_name`; unlike input/output names it is not
/// registered as a combinational lookup signal.
uint32_t aig_latch_named(Aig *g, uint32_t next, uint32_t reset,
                         const char *name);

/// Update the next-state function of an existing latch literal.
bool aig_set_latch_next(Aig *g, uint32_t latch_lit, uint32_t next);

static inline uint32_t aig_not(uint32_t lit) { return lit ^ 1u; }
uint32_t aig_and(Aig *g, uint32_t a, uint32_t b);
uint32_t aig_or(Aig *g, uint32_t a, uint32_t b);

/// Look up an available signal's literal by name, or UINT32_MAX if absent.
uint32_t aig_lookup(const Aig *g, const char *name);

/// True when `name` is a named output of `g`.
bool aig_has_output(const Aig *g, const char *name);

/// Drive output `name` with `lit`; registers `name` as available too.
void aig_set_output(Aig *g, const char *name, uint32_t lit);

/// Remove every output named `name`.  Registered lookup signals are left
/// intact.
void aig_remove_output(Aig *g, const char *name);

/// Add a GR(1) justice property: a generalized-Buchi set of `n` literals, each
/// required to hold infinitely often.  Emitted as an AIGER 1.9 justice record.
void aig_add_justice(Aig *g, const uint32_t *lits, uint32_t n,
                     const char *name);

/// Add an AIGER 1.9 bad-state property.
void aig_add_bad(Aig *g, uint32_t lit, const char *name);

/// Add an AIGER 1.9 invariant constraint.
void aig_add_constraint(Aig *g, uint32_t lit, const char *name);

/// Add a GR(1) fairness constraint `lit` (an environment `G F` assumption).
/// Emitted as an AIGER 1.9 fairness record.
void aig_add_fairness(Aig *g, uint32_t lit, const char *name);

/// For every output whose name starts with `prefix`, strip the prefix and
/// register the stripped name as an available signal.  This is useful for
/// backends that expose controllable outputs as `controllable_<name>`.
void aig_strip_output_prefix(Aig *g, const char *prefix);

/// Rename signal `from` to `to` wherever it appears (inputs, outputs, and the
/// lookup registry).  Used to map a controller a backend produced under
/// renamed atoms (e.g. lowercased for ltlsynt) back to the spec's names.
void aig_rename_signal(Aig *g, const char *from, const char *to);

/// Compile a temporal-free Boolean node into `g` (AP names resolved via
/// `aig_lookup`).  Returns the literal, or UINT32_MAX if a name is unknown or
/// the node is not Boolean.
uint32_t aig_compile(Aig *g, const Node *n);

/// Read accessors over an `Aig`'s structure, for in-process solvers that walk a
/// game's cones (inputs / latches / and-gates / the `bad` output) and compile
/// them into another representation (e.g. BDDs).  Indices are 0-based and in
/// construction order; `_at` getters ignore null out-pointers.
uint32_t aig_num_inputs(const Aig *g);
/// Name (borrowed; valid until `g` is freed) and positive literal of input `i`.
const char *aig_input_name(const Aig *g, uint32_t i, uint32_t *lit);
uint32_t aig_num_latches(const Aig *g);
/// Current-state literal, next-state function literal, and reset value (0/1) of
/// latch `i`.
void aig_latch_at(const Aig *g, uint32_t i, uint32_t *cur, uint32_t *next,
                  uint32_t *reset);
/// Latch symbol (borrowed), or nullptr when latch `i` is unnamed.
const char *aig_latch_name(const Aig *g, uint32_t i);
uint32_t aig_num_outputs(const Aig *g);
/// Name (borrowed; valid until `g` is freed) and literal of output `i`.
/// The name may be null when the source AIGER had no `oN` symbol.
const char *aig_output_at(const Aig *g, uint32_t i, uint32_t *lit);
uint32_t aig_num_ands(const Aig *g);
/// Output literal and the two input literals of and-gate `i` (`lhs = r0 & r1`).
void aig_and_at(const Aig *g, uint32_t i, uint32_t *lhs, uint32_t *r0,
                uint32_t *r1);
/// Literal driving output `name`, or UINT32_MAX if there is no such output.
uint32_t aig_output_lit(const Aig *g, const char *name);

/// Number of typed AIGER 1.9 bad-state properties.
uint32_t aig_num_bad(const Aig *g);
/// Name (borrowed and optional) plus literal of bad-state property `i`.
const char *aig_bad_at(const Aig *g, uint32_t i, uint32_t *lit);

/// Number of typed AIGER 1.9 invariant constraints.
uint32_t aig_num_constraints(const Aig *g);
/// Name (borrowed and optional) plus literal of constraint `i`.
const char *aig_constraint_at(const Aig *g, uint32_t i, uint32_t *lit);

/// Number of GR(1) justice properties.
uint32_t aig_num_justice(const Aig *g);
/// Pointer (borrowed) to the literals array and its length for justice `j`.
void aig_justice_at(const Aig *g, uint32_t j, const uint32_t **lits,
                    uint32_t *n);
/// Optional symbol name of justice property `j`.
const char *aig_justice_name(const Aig *g, uint32_t j);

/// Number of GR(1) fairness constraints.
uint32_t aig_num_fairness(const Aig *g);
/// Literal of fairness constraint `i`.
uint32_t aig_fairness_at(const Aig *g, uint32_t i);
/// Optional symbol name of fairness constraint `i`.
const char *aig_fairness_name(const Aig *g, uint32_t i);

/// Replace every justice/fairness literal whose combinational cone reads an
/// input with a fresh reset-0 latch whose next-state function is that literal.
/// State-only acceptance literals are unchanged.  This turns transition-level
/// AIGER acceptance into state predicates while preserving each GF property.
void aig_sample_input_dependent_acceptance(Aig *g);

/// Parse an ASCII `aag` from `in`, preserving AIGER 1.9 typed properties and
/// their symbols distinctly from ordinary outputs.
/// Returns nullptr on a malformed file.
[[nodiscard]] Aig *aig_read_aag(FILE *in);

/// Compatibility reader for legacy AbsSynthe controller artifacts that encode
/// controllable outputs in `controllable-gate` comments.  Solver-facing game
/// parsing should use `aig_read_aag()` so comments cannot change semantics.
[[nodiscard]] Aig *aig_read_aag_with_controller_comments(FILE *in);

/// Merge `src` into `dst`: map `src` inputs to `dst` signals by name, allocate
/// fresh variables for `src` latches and gates, and wire each `src` output to
/// the `dst` output of the same name.  Returns false if a `src` input name is
/// not available in `dst`.
bool aig_merge(Aig *dst, const Aig *src);

/// Emit `dst` as ASCII `aag` (variables renumbered to the canonical
/// inputs / latches / and-gates order).
void aig_write_aag(FILE *out, const Aig *g);

#ifdef __cplusplus
}
#endif

#endif // TLSF_AIGER_H
