#ifndef TLSF_GR1_EXPORT_H
#define TLSF_GR1_EXPORT_H

#include "oxidd_common.h"
#include "tlsf/gr1_oxidd.h"

#ifdef __cplusplus
extern "C" {
#endif

// Internal export stream factory. A nonzero certificate cap overrides the run
// cap. Bounded streams publish a NUL-terminated buffer only on successful
// close; a failed write makes close fail and discard all output.
FILE *gr1_open_export_memstream(const OxiddRun *run,
                                const Gr1CertificateOptions *options,
                                char **output, size_t *size);

#ifdef TLSF_GR1_EXPORT_TEST_BSD
// Linux test seam: compile the production funopen branch with a stdio bridge.
FILE *gr1_export_test_funopen(const void *cookie,
                              int (*readfn)(void *, char *, int),
                              int (*writefn)(void *, const char *, int),
                              fpos_t (*seekfn)(void *, fpos_t, int),
                              int (*closefn)(void *));
FILE *gr1_export_test_open_memstream(char **output, size_t *size);
#endif

#ifdef __cplusplus
}
#endif

#endif // TLSF_GR1_EXPORT_H
