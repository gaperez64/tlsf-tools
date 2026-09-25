#include "cli.h"

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
