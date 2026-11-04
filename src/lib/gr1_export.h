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

#ifdef __cplusplus
}
#endif

#endif // TLSF_GR1_EXPORT_H
