#include "tlsf/aiger.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(expr)                                                            \
  do {                                                                         \
    if (!(expr)) {                                                             \
      fprintf(stderr, "check failed: %s:%d: %s\n", __FILE__, __LINE__, #expr); \
      abort();                                                                 \
    }                                                                          \
  } while (0)

static FILE *write_tmp(const char *s) {
  FILE *f = tmpfile();
  CHECK(f);
  fputs(s, f);
  rewind(f);
  return f;
}

int main(void) {
  const char *src = "aag 4 1 1 1 1 2 1 1 1\n"
                    "2\n"
                    "4 2 1\n"
                    "8\n"
                    "2\n"
                    "3\n"
                    "4\n"
                    "2\n"
                    "2\n"
                    "4\n"
                    "5\n"
                    "8 2 4\n"
                    "i0 env signal\n"
                    "o0 ordinary output\n"
                    "b0 bad one\n"
                    "b1 bad two\n"
                    "c0 invariant name\n"
                    "j0 justice pair\n"
                    "f0 fairness flag\n"
                    "c\n"
                    "STATUS this comment is harness metadata\n";

  FILE *in = write_tmp(src);
  Aig *g = aig_read_aag(in);
  fclose(in);
  CHECK(g);

  uint32_t lit = 0, reset = 0, n = 0;
  CHECK(aig_num_inputs(g) == 1);
  CHECK(strcmp(aig_input_name(g, 0, &lit), "env signal") == 0);
  CHECK(lit == 2);
  CHECK(aig_num_latches(g) == 1);
  aig_latch_at(g, 0, nullptr, nullptr, &reset);
  CHECK(reset == 1);
  CHECK(aig_num_outputs(g) == 1);
  CHECK(strcmp(aig_output_at(g, 0, &lit), "ordinary output") == 0);
  CHECK(lit == 8);
  CHECK(aig_num_bad(g) == 2);
  CHECK(strcmp(aig_bad_at(g, 0, &lit), "bad one") == 0 && lit == 2);
  CHECK(strcmp(aig_bad_at(g, 1, &lit), "bad two") == 0 && lit == 3);
  CHECK(aig_num_constraints(g) == 1);
  CHECK(strcmp(aig_constraint_at(g, 0, &lit), "invariant name") == 0 &&
        lit == 4);
  CHECK(aig_num_justice(g) == 1);
  const uint32_t *jlits = nullptr;
  aig_justice_at(g, 0, &jlits, &n);
  CHECK(n == 2 && jlits[0] == 2 && jlits[1] == 4);
  CHECK(strcmp(aig_justice_name(g, 0), "justice pair") == 0);
  CHECK(aig_num_fairness(g) == 1);
  CHECK(aig_fairness_at(g, 0) == 5);
  CHECK(strcmp(aig_fairness_name(g, 0), "fairness flag") == 0);

  FILE *out = tmpfile();
  CHECK(out);
  aig_write_aag(out, g);
  rewind(out);
  Aig *again = aig_read_aag(out);
  fclose(out);
  aig_free(g);
  CHECK(again);
  CHECK(aig_num_outputs(again) == 1);
  CHECK(aig_num_bad(again) == 2);
  CHECK(aig_num_constraints(again) == 1);
  CHECK(aig_num_justice(again) == 1);
  CHECK(aig_num_fairness(again) == 1);
  aig_free(again);
  return 0;
}
