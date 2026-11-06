#define _POSIX_C_SOURCE 200809L
#include "check.h"
#include "decode.h"

#include <dirent.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

static size_t hits[FUZZ_CHECK_COUNT];
void fuzz_check_hit(FuzzCheck id) { ++hits[id]; }

static int witness(char group) {
#define FUZZ_NAME(id) #id,
  const char *names[] = {FUZZ_CHECKS(FUZZ_NAME)};
#undef FUZZ_NAME
  int result = 0;
  for (size_t i = 0; i < FUZZ_CHECK_COUNT; ++i) {
    if (names[i][0] != group && !(group != 'R' && names[i][0] == 'C'))
      continue;
    printf("%s %zu\n", names[i], hits[i]);
    if (!hits[i]) {
      fprintf(stderr, "unreached check: %s\n", names[i]);
      result = 1;
    }
  }
  return result;
}

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
  char group = 0;
  int first = 1;
  if (argc > 2 && !strcmp(argv[1], "--witness") && strlen(argv[2]) == 1 &&
      strchr("RAD", argv[2][0])) {
    group = argv[2][0];
    first = 3;
  }
  if (argc <= first) {
    fprintf(stderr, "usage: %s [--witness R|A|D] FILE_OR_DIRECTORY...\n",
            argv[0]);
    return 1;
  }
  int result = 0;
  for (int i = first; i < argc; ++i)
    result |= replay(argv[i]);
  if (group)
    result |= witness(group);
  return result;
}
