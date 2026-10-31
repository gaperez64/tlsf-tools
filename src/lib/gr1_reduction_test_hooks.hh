// Test-only mutation of the native component monitor. Kept beside its private
// representation so contract clients do not depend on construction types.
static bool reduction_test_mode(const char *value) {
  const char *selected = std::getenv("ACACIA_NATIVE_TEST_CONTRACT");
  return selected && std::strcmp(selected, value) == 0;
}
void reduction_test_monitor(const char *stage,
                            std::shared_ptr<Automaton> &aut) {
  if (!std::strcmp(stage, "complete")) {
    if (reduction_test_mode("monitor-incomplete"))
      aut->rows[0].clear();
    if (reduction_test_mode("monitor-nondeterministic")) {
      aut->rows[0].push_back({0, 1, false});
      aut->rows[0].push_back({unsigned(aut->num_states() - 1), 1, false});
    }
  } else {
    if (reduction_test_mode("monitor-empty"))
      aut->rows[0].clear();
    if (reduction_test_mode("monitor-acceptance")) {
      for (auto &row : aut->rows) {
        for (size_t i = 0; i < row.size(); ++i)
          row[i].acc = i != 0;
        if (row.size() > 1)
          break;
      }
    }
  }
}
void reduction_test_formula(const char *stage, Formula &formula) {
  if ((!std::strcmp(stage, "source") && reduction_test_mode("formula-ap")) ||
      (!std::strcmp(stage, "transition") &&
       reduction_test_mode("transition-ap")))
    formula = Formula::ap("undeclared_contract_ap");
  if ((!std::strcmp(stage, "transition") &&
       reduction_test_mode("transition-temporal")) ||
      (!std::strcmp(stage, "symmetric-body") &&
       reduction_test_mode("provenance-boolean")))
    formula = Formula::X(Formula::ap("contract_temporal_ap"));
}
