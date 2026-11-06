#ifndef TLSF_FUZZ_DECODE_H
#define TLSF_FUZZ_DECODE_H

#include <stddef.h>
#include <stdint.h>

/* At most 18 formulas, each with 63 nodes and <64 bytes per node, plus
 * declarations: 128 KiB comfortably bounds the output including its NUL. */
#define TLSF_FUZZ_TEXT_CAPACITY (128 * 1024)

/* Total, deterministic byte grammar. Missing bytes are zero; trailing bytes
 * may be ignored. Caller supplies TLSF_FUZZ_TEXT_CAPACITY bytes. Returns the
 * text length, excluding NUL. No allocations, I/O or external state. */
size_t tlsf_fuzz_decode(const uint8_t *data, size_t size,
                        char text[TLSF_FUZZ_TEXT_CAPACITY]);

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size);

#endif
