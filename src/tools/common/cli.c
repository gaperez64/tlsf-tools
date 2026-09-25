#include "cli.h"

#include <stdlib.h>
#include <string.h>

FILE *cli_open_input(const char *path, const char *prog) {
  if (!path)
    return stdin;
  FILE *f = fopen(path, "r");
  if (!f) {
    fprintf(stderr, "%s: ", prog);
    perror(path);
  }
  return f;
}

FILE *cli_open_output(const char *path, const char *prog) {
  if (!path)
    return stdout;
  FILE *f = fopen(path, "w");
  if (!f) {
    fprintf(stderr, "%s: ", prog);
    perror(path);
  }
  return f;
}

bool cli_parse_param(const char *arg, const char *prog, ParamOverride *out) {
  const char *eq = strchr(arg, '=');
  if (!eq || eq == arg) {
    fprintf(stderr, "%s: bad --param argument '%s' (expect NAME=VALUE)\n", prog,
            arg);
    return false;
  }
  // Temporary copy of the name part (not interned yet).
  size_t nlen = (size_t)(eq - arg);
  char *name = malloc(nlen + 1);
  if (!name)
    return false;
  memcpy(name, arg, nlen);
  name[nlen] = '\0';
  char *end;
  long long val = strtoll(eq + 1, &end, 10);
  if (*end != '\0') {
    fprintf(stderr, "%s: non-integer value in --param '%s'\n", prog, arg);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}
