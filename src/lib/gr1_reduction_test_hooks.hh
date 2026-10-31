// Test-only adapter for the current reducer's monitor representation.
// Included exclusively by TLSF_GR1_REDUCTION_TEST_FAULT builds. The public
// contract tests remain independent of the monitor implementation's types.
static bool reduction_test_mode(const char *value) {
  const char *selected = std::getenv("ACACIA_NATIVE_TEST_CONTRACT");
  return selected && std::strcmp(selected, value) == 0;
}

void reduction_test_monitor(const char *stage, spot::twa_graph_ptr &aut) {
  if (!std::strcmp(stage, "complete")) {
    if (reduction_test_mode("monitor-incomplete"))
      aut->kill_state(0);
    if (reduction_test_mode("monitor-nondeterministic")) {
      aut->new_edge(0, 0, bddtrue);
      aut->new_edge(0, aut->num_states() - 1, bddtrue);
    }
  } else {
    if (reduction_test_mode("monitor-empty"))
      aut->kill_state(0);
    if (reduction_test_mode("monitor-acceptance")) {
      for (unsigned state = 0; state < aut->num_states(); ++state) {
        unsigned count = 0;
        for (auto &edge : aut->out(state))
          edge.acc =
              count++ ? spot::acc_cond::mark_t{} : spot::acc_cond::mark_t{0};
        if (count > 1)
          break;
      }
    }
  }
}

void reduction_test_formula(const char *stage, spot::formula &formula) {
  if ((!std::strcmp(stage, "source") && reduction_test_mode("formula-ap")) ||
      (!std::strcmp(stage, "transition") &&
       reduction_test_mode("transition-ap")))
    formula = spot::formula::ap("undeclared_contract_ap");
  if ((!std::strcmp(stage, "transition") &&
       reduction_test_mode("transition-temporal")) ||
      (!std::strcmp(stage, "symmetric-body") &&
       reduction_test_mode("provenance-boolean")))
    formula = spot::formula::X(spot::formula::ap("contract_temporal_ap"));
}
