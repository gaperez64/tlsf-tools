#pragma once

// The combined API omits legacy seed values; the standalone half checks them.
static void legacy_axis_regressions(const char *path, bool both) {
  std::ifstream file(path);
  CHECK(file.good());
  const std::string source(std::istreambuf_iterator<char>{file}, {});
  const bool tied = source.find("a+n") != std::string::npos;
  const bool ordered = source.find("two live axes") != std::string::npos;
  const std::string axis = tied ? "a" : "n";
  auto renamed = fold_test::rename_identifier(source, "a", "z");
  renamed = fold_test::rename_identifier(renamed, "n", "b");
  auto observe = [&](const std::string &bytes, const std::string &selected) {
    TlsfGr1LiftStats stats{};
    TlsfGr1LiftOptions o{};
    o.deadline_mono_ns = deadline(50);
    o.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
    // Each tied candidate needs four probes. A shared allowance would starve
    // the second; the two distinct live axes also exercise tight ordering.
    o.phase_budget.max_seed_probes = ordered ? 5 : 4;
    o.stats = &stats;
    TlsfGr1LiftTarget *target = nullptr;
    TlsfGr1LiftError e{};
    CHECK(tlsf_gr1_lift_target_prepare_exact_v1((const uint8_t *)bytes.data(),
                                                bytes.size(), &o, &target, &e,
                                                nullptr) == TLSF_GR1_LIFT_OK);
    TlsfGr1LiftResult solo{};
    TlsfGr1BothResult combined{};
    const auto status =
        both ? tlsf_gr1_both_from_target(target, &o, &combined, &e)
             : tlsf_gr1_lift_from_target(target, &o, &solo, &e);
    if (status != TLSF_GR1_LIFT_OK)
      std::fprintf(stderr, "%s: %s; %s\n", e.stage, e.message,
                   both ? combined.decline_detail : solo.decline_detail);
    CHECK(status == TLSF_GR1_LIFT_OK);
    const auto &r = both ? combined.proof : solo;
    CHECK(r.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
    CHECK(r.method == TLSF_GR1_CHECK_REGION);
    CHECK(tlsf_gr1_lift_target_matches(target, &r));
    auto evidence =
        tlsf_json::parse(std::string_view(r.evidence_json, r.evidence_size))
            .as_object();
    std::vector<int64_t> seeds;
    if (both) {
      CHECK(combined.route == TLSF_GR1_BOTH_REAL_LIFT);
      CHECK(evidence.at("route").as_string() == "R");
      CHECK(combined.target_checks == (tied ? 2 : 1));
    } else {
      CHECK(evidence.at("axis").as_string() == selected);
      for (const auto &value : evidence.at("seed_values").as_array())
        seeds.push_back(value.as_int64());
      CHECK(seeds == (tied ? std::vector<int64_t>{1, 2, 3}
                           : std::vector<int64_t>{2, 3, 4}));
    }
    const auto solves = both ? combined.seed_solves : stats.seed_solves;
    CHECK(solves == (tied ? 6 : 3));
    const auto probes = both ? combined.seed_probes : stats.seed_probes;
    CHECK(ordered ? probes <= 5 : probes == (tied ? 8 : 4));
    const std::vector<uint64_t> counts{
        stats.seed_probes,    stats.seed_solves,        stats.internal_checks,
        combined.seed_probes, combined.seed_reductions, combined.seed_solves,
        combined.seed_checks, combined.seed_cache_hits, combined.target_checks};
    std::fprintf(stderr, "%s %s: REGION_VERIFIED, %llu probes, %llu solves\n",
                 path, selected.c_str(), (unsigned long long)probes,
                 (unsigned long long)solves);
    tlsf_gr1_lift_result_clear(&solo);
    tlsf_gr1_both_result_clear(&combined);
    tlsf_gr1_lift_target_free(target);
    return std::make_pair(seeds, counts);
  };
  CHECK(observe(source, axis) == observe(renamed, tied ? "z" : "b"));
  if (!tied && !ordered) {
    // Barbosa's variant uses n directly in the generator bound.
    auto direct_bound = source;
    direct_bound.replace(direct_bound.find("SIZEOF response"),
                         strlen("SIZEOF response"), "n");
    CHECK(observe(direct_bound, "n") ==
          observe(fold_test::rename_identifier(direct_bound, "n", "b"), "b"));
  }
}
