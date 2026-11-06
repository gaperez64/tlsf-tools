#define _POSIX_C_SOURCE 200809L
#include "decode.h"

#include <dirent.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

static int replay(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0)
    goto error;
  if (S_ISDIR(st.st_mode)) {
    DIR *dir = opendir(path);
    if (!dir)
      goto error;
    int result = 0;
    struct dirent *entry;
    while ((entry = readdir(dir))) {
      if (!strcmp(entry->d_name, ".") || !strcmp(entry->d_name, ".."))
        continue;
      size_t size = strlen(path) + strlen(entry->d_name) + 2;
      char *child = malloc(size);
      if (!child) {
        result = 1;
        break;
      }
      snprintf(child, size, "%s/%s", path, entry->d_name);
      result |= replay(child);
      free(child);
    }
    closedir(dir);
    return result;
  }
  if (!S_ISREG(st.st_mode)) {
    errno = EINVAL;
    goto error;
  }
  FILE *in = fopen(path, "rb");
  if (!in)
    goto error;
  size_t size = (size_t)st.st_size;
  uint8_t *data = malloc(size ? size : 1);
  int result = 1;
  if (data && fread(data, 1, size, in) == size) {
    LLVMFuzzerTestOneInput(data, size);
    result = 0;
  }
  free(data);
  fclose(in);
  if (!result)
    return 0;
error:
  perror(path);
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s FILE_OR_DIRECTORY...\n", argv[0]);
    return 1;
  }
  int result = 0;
  for (int i = 1; i < argc; ++i)
    result |= replay(argv[i]);
  return result;
}
