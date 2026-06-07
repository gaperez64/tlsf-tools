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

/// For every output whose name starts with `prefix`, strip the prefix and
/// register the stripped name as an available signal.  This is useful for
/// backends that expose controllable outputs as `controllable_<name>`.
void aig_strip_output_prefix(Aig *g, const char *prefix);

/// Compile a temporal-free Boolean node into `g` (AP names resolved via
/// `aig_lookup`).  Returns the literal, or UINT32_MAX if a name is unknown or
/// the node is not Boolean.
uint32_t aig_compile(Aig *g, const Node *n);

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
