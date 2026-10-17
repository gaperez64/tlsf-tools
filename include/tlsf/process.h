#ifndef TLSF_PROCESS_H
#define TLSF_PROCESS_H

#ifdef __cplusplus
extern "C" {
#endif

/// Call at process start, before creating any threads or OxiDD managers.
/// If OXIDD_STACK_SIZE is unset and RLIMIT_AS is finite, set it to
/// min(1 GiB, max(8 MiB, RLIMIT_AS / 16)). An explicit value always wins.
/// Leaves the environment unchanged for unlimited/unsupported limits.
/// Returns 0 on success (including no change), -1 on an OS error (see errno).
/// Library operations never call this function implicitly.
int tlsf_oxidd_configure_process_stack(void);

#ifdef __cplusplus
}
#endif
#endif
