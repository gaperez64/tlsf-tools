#define _POSIX_C_SOURCE 200809L
#include "tlsf/convert.h"
#include "tlsf/dpa.h"
#include <stdlib.h>
#include <time.h>

// External inventories supply paths; admission never enumerates successors.
int main(int argc, char **argv) {
  unsigned admitted[2] = {0};
  for (int i = 1; i < argc; ++i) {
    FILE *fp = fopen(argv[i], "rb");
    if (!fp || fseek(fp, 0, SEEK_END))
      return 1;
    long length = ftell(fp);
    if (length < 0 || fseek(fp, 0, SEEK_SET))
      return 1;
    char *text = malloc((size_t)length + 1);
    if (!text || fread(text, 1, (size_t)length, fp) != (size_t)length)
      return 1;
    fclose(fp);
    text[length] = 0;
    TlsfConversionResult *converted = tlsf_convert(text, "Mealy");
    free(text);
    if (!converted)
      return 1;
    bool default_admitted = false;
    for (unsigned research = 0; research < 2; ++research) {
      struct timespec now;
      if (clock_gettime(CLOCK_MONOTONIC, &now))
        return 1;
      TlsfDpaBudget budget = {
          .max_host_bytes = 512u << 20,
          .bdd_nodes = 1u << 22,
          .deadline_mono_ns = (uint64_t)now.tv_sec * UINT64_C(1000000000) +
                              (uint64_t)now.tv_nsec + UINT64_C(10000000000)};
      budget.allow_unproved = research;
      TlsfDpa *c = nullptr;
      TlsfDpaStatus status = tlsf_dpa_create(
          tlsf_ast_root(converted->ast), (const char *const *)converted->inputs,
          converted->n_inputs, (const char *const *)converted->outputs,
          converted->n_outputs, &budget, &c);
      if (status.code == TLSF_DPA_OK && tlsf_dpa_state_count(c) == 1) {
        ++admitted[research];
        if (!research)
          default_admitted = true;
      } else if (status.code != TLSF_DPA_DECLINED ||
                 status.reason != TLSF_DPA_UNSUPPORTED || c ||
                 (research && default_admitted)) {
        fprintf(stderr, "unexpected admission result: %s (%u/%u)\n", argv[i],
                (unsigned)status.code, (unsigned)status.reason);
        tlsf_dpa_free(c);
        return 1;
      }
      tlsf_dpa_free(c);
    }
    tlsf_conversion_result_free(converted);
  }
  printf("admitted %u/%d default, %u/%d research; no expansion\n", admitted[0],
         argc - 1, admitted[1], argc - 1);
}
