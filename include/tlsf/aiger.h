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

#define AIG_FALSE 0u
#define AIG_TRUE 1u

typedef struct Aig Aig;

[[nodiscard]] Aig *aig_new(void);
void aig_free(Aig *g);

/// Add an input named `name`; returns its (positive) literal.  Also registers
/// it as an available signal for `aig_compile`/`aig_merge` lookups.
uint32_t aig_input(Aig *g, const char *name);

/// Add a latch with next-state function `next` and reset value 0/1; returns its
/// current-state positive literal.
uint32_t aig_latch(Aig *g, uint32_t next, uint32_t reset);

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
uint32_t aig_num_ands(const Aig *g);
/// Output literal and the two input literals of and-gate `i` (`lhs = r0 & r1`).
void aig_and_at(const Aig *g, uint32_t i, uint32_t *lhs, uint32_t *r0,
                uint32_t *r1);
/// Literal driving output `name`, or UINT32_MAX if there is no such output.
uint32_t aig_output_lit(const Aig *g, const char *name);

/// Number of GR(1) justice properties.
uint32_t aig_num_justice(const Aig *g);
/// Pointer (borrowed) to the literals array and its length for justice `j`.
void aig_justice_at(const Aig *g, uint32_t j, const uint32_t **lits,
                    uint32_t *n);

/// Number of GR(1) fairness constraints.
uint32_t aig_num_fairness(const Aig *g);
/// Literal of fairness constraint `i`.
uint32_t aig_fairness_at(const Aig *g, uint32_t i);

/// Parse an ASCII `aag` from `in` (inputs/latches/outputs/ands + i/o symbols).
/// Returns nullptr on a malformed file.
[[nodiscard]] Aig *aig_read_aag(FILE *in);

/// Merge `src` into `dst`: map `src` inputs to `dst` signals by name, allocate
/// fresh variables for `src` latches and gates, and wire each `src` output to
/// the `dst` output of the same name.  Returns false if a `src` input name is
/// not available in `dst`.
bool aig_merge(Aig *dst, const Aig *src);

/// Emit `dst` as ASCII `aag` (variables renumbered to the canonical
/// inputs / latches / and-gates order).
void aig_write_aag(FILE *out, const Aig *g);

#endif // TLSF_AIGER_H
