#pragma once

// The combined API omits legacy seed values; the standalone half checks them.
static void legacy_axis_regressions(const char *path, bool both) {
  std::ifstream file(path);
  CHECK(file.good());
  const std::string source(std::istreambuf_iterator<char>{file}, {});
  const bool tied = source.find("a+n") != std::string::npos;
  const bool ordered = source.find("two live axes") != std::string::npos;
  const bool incomplete = source.find("unknown widths") != std::string::npos;
  const std::string axis = tied ? "a" : "n";
  auto renamed = fold_test::rename_identifier(source, "a", "z");
  const std::string renamed_axis = incomplete ? "span" : "b";
  renamed = fold_test::rename_identifier(renamed, "n", renamed_axis);
  auto observe = [&](const std::string &bytes, const std::string &selected,
                     TlsfGr1LiftProofOrder order = TLSF_GR1_LIFT_REGION_FIRST,
                     int fault = 0) {
    TlsfGr1LiftStats stats{};
    TlsfGr1LiftOptions o{};
    o.deadline_mono_ns = deadline(50);
    o.proof_order = order;
    // The first tied success must finish without discovering or solving its
    // sibling. Mixed provenance must find the proven axis under the default
    // cap.
    o.phase_budget.max_seed_probes = incomplete ? 0 : ordered ? 5 : 4;
    o.stats = &stats;
    TlsfGr1LiftTarget *target = nullptr;
    TlsfGr1LiftError e{};
    CHECK(tlsf_gr1_lift_target_prepare_exact_v1((const uint8_t *)bytes.data(),
                                                bytes.size(), &o, &target, &e,
                                                nullptr) == TLSF_GR1_LIFT_OK);
    TlsfGr1LiftResult solo{};
    TlsfGr1BothResult combined{};
    // A second seed solve window would cancel the call after the first proof.
    struct StopLater {
      const TlsfGr1LiftStats &stats;
      const TlsfGr1BothResult &combined;
    } stop{stats, combined};
    if (tied) {
      o.cancel_ctx = &stop;
      o.cancelled = [](void *raw) {
        const auto &s = *static_cast<StopLater *>(raw);
        return int(s.stats.seed_solves > 3 || s.combined.seed_solves > 3);
      };
    }
    tlsf_gr1_lift_test_set_fault(fault);
    const auto status =
        both ? tlsf_gr1_both_from_target(target, &o, &combined, &e)
             : tlsf_gr1_lift_from_target(target, &o, &solo, &e);
    tlsf_gr1_lift_test_set_fault(0);
    if (status != TLSF_GR1_LIFT_OK)
      std::fprintf(stderr, "%s: %s; %s\n", e.stage, e.message,
                   both ? combined.decline_detail : solo.decline_detail);
    CHECK(status == TLSF_GR1_LIFT_OK);
    const auto &r = both ? combined.proof : solo;
    const bool policy = fault || order == TLSF_GR1_LIFT_POLICY_FIRST;
    CHECK(r.verdict ==
          (policy ? TLSF_GR1_CHECK_VERIFIED : TLSF_GR1_CHECK_REGION_VERIFIED));
    CHECK(r.method ==
          (policy ? TLSF_GR1_CHECK_CERTIFICATE : TLSF_GR1_CHECK_REGION));
    if (policy)
      CHECK(r.policy_aag);
    CHECK(tlsf_gr1_lift_target_matches(target, &r));
    auto evidence =
        tlsf_json::parse(std::string_view(r.evidence_json, r.evidence_size))
            .as_object();
    std::vector<int64_t> seeds;
    if (both) {
      CHECK(combined.route == TLSF_GR1_BOTH_REAL_LIFT);
      CHECK(evidence.at("route").as_string() == "R");
      CHECK(combined.target_checks == 1);
    } else {
      CHECK(evidence.at("axis").as_string() == selected);
      for (const auto &value : evidence.at("seed_values").as_array())
        seeds.push_back(value.as_int64());
      CHECK(seeds == (tied ? std::vector<int64_t>{1, 2, 3}
                           : std::vector<int64_t>{2, 3, 4}));
    }
    const auto solves = both ? combined.seed_solves : stats.seed_solves;
    CHECK(solves == 3);
    const auto probes = both ? combined.seed_probes : stats.seed_probes;
    CHECK(ordered ? probes <= 5 : probes == 4);
    CHECK(probes <= (incomplete ? TLSF_GR1_LIFT_DEFAULT_SEED_PROBES
                                : o.phase_budget.max_seed_probes));
    CHECK(stats.internal_checks ==
          (fault && order == TLSF_GR1_LIFT_REGION_FIRST ? 2u : 1u));
    const std::vector<uint64_t> counts{
        stats.seed_probes,    stats.seed_solves,        stats.internal_checks,
        combined.seed_probes, combined.seed_reductions, combined.seed_solves,
        combined.seed_checks, combined.seed_cache_hits, combined.target_checks};
    std::fprintf(stderr, "%s %s: %s, %llu probes, %llu solves\n", path,
                 selected.c_str(), policy ? "VERIFIED" : "REGION_VERIFIED",
                 (unsigned long long)probes, (unsigned long long)solves);
    tlsf_gr1_lift_result_clear(&solo);
    tlsf_gr1_both_result_clear(&combined);
    if (tied && order == TLSF_GR1_LIFT_REGION_FIRST && !fault) {
      // Reject the first proof. Four probes must exhaust the aggregate cap;
      // eight allow the second axis to verify, with no work after its success.
      o.cancelled = nullptr;
      for (uint64_t cap : {4u, 8u}) {
        stats = {};
        o.phase_budget.max_seed_probes = cap;
        o.stats_callback = [](void *, TlsfGr1LiftStatsStage stage,
                              const TlsfGr1LiftStageStats *) {
          if (stage == TLSF_GR1_LIFT_STATS_INTERNAL_CHECK)
            tlsf_gr1_lift_test_set_fault(0);
        };
        tlsf_gr1_lift_test_set_fault(3);
        const auto limited =
            both ? tlsf_gr1_both_from_target(target, &o, &combined, &e)
                 : tlsf_gr1_lift_from_target(target, &o, &solo, &e);
        tlsf_gr1_lift_test_set_fault(0);
        CHECK((both ? combined.seed_probes : stats.seed_probes) == cap);
        CHECK((both ? combined.seed_solves : stats.seed_solves) ==
              (cap == 4 ? 3u : 6u));
        if (!both && cap == 4) {
          CHECK(limited == TLSF_GR1_LIFT_LIMIT);
          CHECK(!strcmp(e.stage, "seed_window"));
          CHECK(!solo.game_aag);
        } else {
          CHECK(limited == TLSF_GR1_LIFT_OK);
          CHECK((both ? combined.proof : solo).verdict ==
                (cap == 4 ? TLSF_GR1_CHECK_VERIFIED
                          : TLSF_GR1_CHECK_REGION_VERIFIED));
          if (both)
            CHECK(combined.route ==
                  (cap == 4 ? TLSF_GR1_BOTH_DIRECT : TLSF_GR1_BOTH_REAL_LIFT));
        }
        tlsf_gr1_lift_result_clear(&solo);
        tlsf_gr1_both_result_clear(&combined);
      }
    }
    tlsf_gr1_lift_target_free(target);
    return std::make_pair(seeds, counts);
  };
  CHECK(observe(source, axis) == observe(renamed, tied ? "z" : renamed_axis));
  if (tied && !both) {
    for (auto order : {TLSF_GR1_LIFT_POLICY_FIRST, TLSF_GR1_LIFT_REGION_FIRST})
      for (int fault : {0, 2}) {
        if (order == TLSF_GR1_LIFT_REGION_FIRST && !fault)
          continue; // Already covered above, including the aggregate cap.
        CHECK(observe(source, axis, order, fault) ==
              observe(renamed, "z", order, fault));
      }
  }
  if (!tied && !ordered && !incomplete) {
    // Barbosa's variant uses n directly in the generator bound.
    auto direct_bound = source;
    direct_bound.replace(direct_bound.find("SIZEOF response"),
                         strlen("SIZEOF response"), "n");
    CHECK(observe(direct_bound, "n") ==
          observe(fold_test::rename_identifier(direct_bound, "n", "b"), "b"));
  }
}
