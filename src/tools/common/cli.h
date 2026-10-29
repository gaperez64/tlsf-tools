#ifndef TLSF_CLI_H
#define TLSF_CLI_H

/// cli.h — shared command-line helpers for the tools.

#include "tlsf/expand.h"

#include <stdbool.h>
#include <stdio.h>

/// Open the input: `path`, or stdin when `path` is null.  On failure prints a
/// message prefixed with `prog` and returns null.
[[nodiscard]] FILE *cli_open_input(const char *path, const char *prog);

/// Open the output: `path`, or stdout when `path` is null.
[[nodiscard]] FILE *cli_open_output(const char *path, const char *prog);

/// Parse a writable `--param NAME=VALUE` argument, splitting it in place at
/// '='. The returned name borrows the argument's storage.  On a malformed
/// argument prints a message prefixed with `prog` and returns false.
[[nodiscard]] bool cli_parse_param(char *arg, const char *prog,
                                   ParamOverride *out);

#endif // TLSF_CLI_H
