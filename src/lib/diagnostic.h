#ifndef TLSF_DIAGNOSTIC_H
#define TLSF_DIAGNOSTIC_H

#include <stdio.h>

/* Parser and expander messages default to stderr in the CLI. Library entry
 * points install a thread-local memory stream and return its text as evidence.
 */
FILE *tlsf_diagnostic_stream(void);
FILE *tlsf_diagnostic_swap(FILE *stream);

#endif
