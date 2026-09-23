#include "tlsf/aiger.h"
#include "tlsf/gr1_oxidd.h"

#include <stdio.h>

static Aig *make_game(void) {
  Aig *game = aig_new();
  uint32_t u = aig_input(game, "u");
  uint32_t c = aig_input(game, "controllable_c");
  uint32_t q = aig_latch(game, AIG_FALSE, 0);
  if (!aig_set_latch_next(game, q, u))
    return nullptr;
  aig_set_output(game, "bad", aig_and(game, u, c));
  uint32_t goals[] = {q, aig_not(q)};
  aig_add_justice(game, goals, 2, "both_q_values");
  aig_add_fairness(game, q, "q_high");
  aig_add_fairness(game, aig_not(q), "q_low");
  return game;
}

static bool same_properties(const Aig *left, const Aig *right) {
  if (aig_num_justice(left) != aig_num_justice(right) ||
      aig_num_fairness(left) != aig_num_fairness(right) ||
      aig_output_lit(left, "bad") != aig_output_lit(right, "bad"))
    return false;
  for (uint32_t j = 0; j < aig_num_justice(left); j++) {
    const uint32_t *llits, *rlits;
    uint32_t ln, rn;
    aig_justice_at(left, j, &llits, &ln);
    aig_justice_at(right, j, &rlits, &rn);
    if (ln != rn)
      return false;
    for (uint32_t k = 0; k < ln; k++)
      if (llits[k] != rlits[k])
        return false;
  }
  for (uint32_t i = 0; i < aig_num_fairness(left); i++)
    if (aig_fairness_at(left, i) != aig_fairness_at(right, i))
      return false;
  return true;
}

static bool same_files(FILE *left, FILE *right) {
  rewind(left);
  rewind(right);
  for (;;) {
    int lch = fgetc(left), rch = fgetc(right);
    if (lch != rch)
      return false;
    if (lch == EOF)
      return true;
  }
}

int main(void) {
  Aig *built = make_game();
  if (!built)
    return 1;
  FILE *serialized = tmpfile();
  if (!serialized)
    return 1;
  aig_write_aag(serialized, built);
  rewind(serialized);
  Aig *read = aig_read_aag(serialized);
  if (!read) {
    fprintf(stderr, "round-trip read failed\n");
    fclose(serialized);
    aig_free(built);
    return 1;
  }
  FILE *rewritten = tmpfile();
  if (!rewritten)
    return 1;
  aig_write_aag(rewritten, read);
  if (!same_properties(built, read) || !same_files(serialized, rewritten)) {
    fprintf(stderr, "justice/fairness/bad changed across AAG round-trip\n");
    fclose(serialized);
    fclose(rewritten);
    aig_free(built);
    aig_free(read);
    return 1;
  }
  fclose(serialized);
  fclose(rewritten);

  int built_unreal = 0, read_unreal = 0;
  Aig *built_strategy = solve_gr1_oxidd(built, &built_unreal);
  Aig *read_strategy = solve_gr1_oxidd(read, &read_unreal);
  if (built_unreal != read_unreal || !built_strategy || !read_strategy) {
    fprintf(stderr, "round-trip changed the solver verdict\n");
    aig_free(built_strategy);
    aig_free(read_strategy);
    return 1;
  }
  aig_free(built_strategy);
  aig_free(read_strategy);
  return 0;
}
