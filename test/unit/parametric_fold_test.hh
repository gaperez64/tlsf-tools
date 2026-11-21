#include "yyjson_cpp.hh"
#include "fold_obfuscation_test.hh"

extern "C" unsigned tlsf_gr1_lift_test_pair_monitors(const TlsfGr1LiftTarget *);
extern "C" void
tlsf_gr1_lift_test_set_param_activation(void (*)(TlsfGr1LiftOptions *));
extern "C" void tlsf_gr1_lift_test_set_axis_scan(void (*)(TlsfGr1LiftOptions *,
                                                          bool));

// Standalone cases use this shared table; acacia-bonsai's attribution check
// inventories lift_fault_cases in native_both_api.cpp only.
static const std::pair<int, const char *> param_fault_cases[] = {
    {14, "param_state_growth"},       {15, "param_ordered_domain"},
    {16, "param_tag_transport"},      {17, "param_no_candidate"},
    {18, "param_seed_mismatch"},      {19, "param_region_failed(input-first)"},
    {20, "param_rank_depth_changed"}, {21, "param_fairness_changed"},
    {22, "host allocation failed"},   {23, "param_failed"},
    {24, "fold_region_stopped"},      {25, "fold_region_stopped"},
    {26, "host allocation failed"}};

struct ParamEvent {
  TlsfGr1BothEventKind kind;
  TlsfGr1BothEventRoute route;
  TlsfGr1LiftStatus cause;
  std::string stage;
};
static void parametric_activation_regressions(const char *path, bool both) {
  std::ifstream file(path);
  CHECK(file.good());
  const std::string source(std::istreambuf_iterator<char>{file}, {});
  enum class Boundary { activation, encoded_axes, element_axes };
  for (auto boundary :
       {Boundary::activation, Boundary::encoded_axes, Boundary::element_axes}) {
    for (bool real_only : {false, true}) {
      if (!both && real_only)
        continue;
      // Default combined routing returns U's window before the encoded scan.
      if (both && !real_only && boundary == Boundary::encoded_axes)
        continue;
      for (auto cause : {TLSF_GR1_LIFT_CANCELLED, TLSF_GR1_LIFT_DEADLINE,
                         TLSF_GR1_LIFT_LIMIT}) {
        TlsfGr1LiftOptions o{};
        o.deadline_mono_ns = deadline(50);
        o.disable_env_lift = real_only;
        struct Stop {
          TlsfGr1LiftOptions &options;
          TlsfGr1LiftStatus cause;
          Boundary boundary;
          unsigned activations = 0;
          std::vector<ParamEvent> events;
          void interrupt(TlsfGr1LiftOptions *active) {
            ++activations;
            if (cause == TLSF_GR1_LIFT_DEADLINE)
              active->deadline_mono_ns = 1;
            if (cause == TLSF_GR1_LIFT_LIMIT)
              options.budget.max_rss_bytes = 1;
          }
        } stop{o, cause, boundary, 0, {}};
        o.cancel_ctx = &stop;
        o.cancelled = [](void *raw) {
          auto &stop = *static_cast<Stop *>(raw);
          return int(stop.activations && stop.cause == TLSF_GR1_LIFT_CANCELLED);
        };
        TlsfGr1LiftTarget *target = nullptr;
        TlsfGr1LiftError e{};
        CHECK(tlsf_gr1_lift_target_prepare_exact_v1(
                  (const uint8_t *)source.data(), source.size(), &o, &target,
                  &e, nullptr) == TLSF_GR1_LIFT_OK);
        if (boundary == Boundary::activation)
          tlsf_gr1_lift_test_set_param_activation(
              [](TlsfGr1LiftOptions *active) {
                static_cast<Stop *>(active->cancel_ctx)->interrupt(active);
              });
        else
          tlsf_gr1_lift_test_set_axis_scan(
              [](TlsfGr1LiftOptions *active, bool encoded) {
                auto &stop = *static_cast<Stop *>(active->cancel_ctx);
                if (encoded == (stop.boundary == Boundary::encoded_axes))
                  stop.interrupt(active);
              });
        TlsfGr1BothObserverV1 observer{};
        observer.context = &stop;
        observer.event = [](void *raw, TlsfGr1BothEventKind kind,
                            TlsfGr1BothEventRoute route, int, const char *stage,
                            const char *, TlsfGr1LiftStatus cause) {
          static_cast<Stop *>(raw)->events.push_back(
              {kind, route, cause, stage});
        };
        TlsfGr1LiftResult solo{};
        TlsfGr1BothResult combined{};
        const TlsfGr1BothOptionsV2 routing{&o, &observer, 0};
        const auto status =
            both ? tlsf_gr1_both_from_target_v2(target, &routing, &combined, &e)
                 : tlsf_gr1_lift_from_target(target, &o, &solo, &e);
        tlsf_gr1_lift_test_set_param_activation(nullptr);
        tlsf_gr1_lift_test_set_axis_scan(nullptr);
        CHECK(stop.activations == 1);
        CHECK(status == cause);
        CHECK(e.status == cause);
        const char *scan_stage = boundary == Boundary::activation
                                     ? "param_discovery"
                                     : "fold_discovery";
        const char *stage =
            cause == TLSF_GR1_LIFT_LIMIT ? "budget-memory" : scan_stage;
        CHECK(!strcmp(e.stage, stage));
        const char *detail =
            both ? combined.decline_detail : solo.decline_detail;
        const char *reason = cause == TLSF_GR1_LIFT_CANCELLED ? "cancelled"
                             : cause == TLSF_GR1_LIFT_DEADLINE
                                 ? "deadline exceeded"
                                 : "memory_budget";
        const char *kind = cause == TLSF_GR1_LIFT_CANCELLED  ? "cancelled"
                           : cause == TLSF_GR1_LIFT_DEADLINE ? "deadline"
                                                             : "resource";
        const std::string expected =
            std::string(boundary == Boundary::encoded_axes ? "fold="
                                                           : "param=") +
            reason + "(stage=" + stage + ",cause=" + kind + ")";
        CHECK(strstr(detail, expected.c_str()));
        if (cause != TLSF_GR1_LIFT_LIMIT) {
          const std::string message =
              std::string(reason) + (both ? "" : ": " + std::string(detail));
          CHECK(message.substr(0, sizeof e.message - 1) == e.message);
        } else {
          const auto original =
              std::string("construction RSS exceeded arm memory share at ") +
              scan_stage;
          CHECK(strstr(detail, original.c_str()));
        }
        const auto &proof = both ? combined.proof : solo;
        CHECK(proof.verdict == TLSF_GR1_CHECK_UNKNOWN);
        CHECK(!proof.game_aag && !proof.certificate_aag &&
              !proof.evidence_json);
        if (both) {
          CHECK(combined.seed_solves == (real_only ? 0 : 3));
          CHECK(combined.seed_checks == combined.seed_solves);
          CHECK(combined.target_checks == 0);
          unsigned stops = 0;
          for (const auto &event : stop.events) {
            CHECK(event.kind != TLSF_GR1_BOTH_EVENT_VERIFIED);
            if (event.route == TLSF_GR1_BOTH_EVENT_SEEDS &&
                event.kind == TLSF_GR1_BOTH_EVENT_STOPPED) {
              CHECK(event.cause == cause && event.stage == stage);
              ++stops;
            }
          }
          CHECK(stops == 1);
        }
        tlsf_gr1_lift_result_clear(&solo);
        tlsf_gr1_both_result_clear(&combined);
        tlsf_gr1_lift_target_free(target);
      }
    }
  }
}
static void parametric_regressions(
    const char *path, bool both,
    const std::vector<std::pair<int, const char *>> &faults,
    void (*check_events)(int, const std::vector<ParamEvent> &) = nullptr) {
  std::ifstream file(path);
  CHECK(file.good());
  std::string source(std::istreambuf_iterator<char>{file}, {});
  auto attempt = [&](const std::string &bytes, int fault, const char *reason,
                     const char *axis = "n", unsigned arity = 4,
                     bool acacia_defaults = false, bool real_only = false,
                     unsigned target_size = 6) {
    TlsfGr1LiftStats stats{};
    TlsfGr1LiftOptions o{};
    o.deadline_mono_ns = deadline(50);
    o.solver_nodes = o.schema_nodes = 1u << 20;
    o.checker_nodes = 1u << 22;
    o.solver_cache = o.schema_cache = o.checker_cache = 1u << 16;
    o.max_monitor_states = 1000;
    o.max_artifact_bytes = 8u << 20;
    o.max_predicate_arity = arity;
    o.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
    o.env_candidate_ns = 12000000000ull;
    if (acacia_defaults) {
      o = {};
      o.deadline_mono_ns = deadline(50);
      o.proof_order = TLSF_GR1_LIFT_REGION_FIRST;
      o.env_candidate_ns = 12000000000ull;
      o.budget.max_formula_nodes = 4096;
      o.budget.max_ap_count = 2048;
      o.budget.max_conjuncts = o.budget.max_conjunct_nodes = 1024;
      o.budget.max_temporal_depth = 16;
      o.budget.max_predicted_monitor_states = 1u << 24;
      o.budget.max_total_states = 10000;
      o.budget.max_total_edges = 150000;
      o.budget.max_rss_bytes = uint64_t(5) << 29;
      o.env_budget.max_rss_bytes = o.budget.max_rss_bytes;
      o.stats = &stats;
    }
    o.disable_env_lift = real_only;
    struct Stop {
      bool direct = false;
      bool verified = false;
      std::vector<ParamEvent> events;
    } stop;
    if (!acacia_defaults) {
      o.cancelled = [](void *raw) {
        return int(static_cast<Stop *>(raw)->direct);
      };
      o.cancel_ctx = &stop;
    }
    TlsfGr1BothObserverV1 observer{};
    observer.context = &stop;
    observer.event = [](void *raw, TlsfGr1BothEventKind kind,
                        TlsfGr1BothEventRoute route, int, const char *stage,
                        const char *, TlsfGr1LiftStatus cause) {
      static_cast<Stop *>(raw)->events.push_back({kind, route, cause, stage});
      if (kind == TLSF_GR1_BOTH_EVENT_VERIFIED)
        static_cast<Stop *>(raw)->verified = true;
      if (kind == TLSF_GR1_BOTH_EVENT_SELECTED &&
          route == TLSF_GR1_BOTH_EVENT_DIRECT)
        static_cast<Stop *>(raw)->direct = true;
    };
    ParamOverride param{axis, target_size};
    TlsfGr1LiftError e{};
    TlsfGr1LiftResult solo{};
    TlsfGr1BothResult combined{};
    TlsfGr1LiftTarget *target = nullptr;
    tlsf_gr1_lift_test_set_fault(fault);
    TlsfGr1LiftStatus status;
    if (both && acacia_defaults) {
      auto prepare_options = o;
      prepare_options.max_artifact_bytes = 64u << 20;
      CHECK(tlsf_gr1_lift_target_prepare_exact_v1(
                (const uint8_t *)bytes.data(), bytes.size(), &prepare_options,
                &target, &e, nullptr) == TLSF_GR1_LIFT_OK);
    } else
      CHECK(tlsf_gr1_lift_target_prepare((const uint8_t *)bytes.data(),
                                         bytes.size(), &param, 1, &o, &target,
                                         &e) == TLSF_GR1_LIFT_OK);
    const auto pairs = tlsf_gr1_lift_test_pair_monitors(target);
    if (both) {
      const TlsfGr1BothOptionsV2 routing{&o, &observer, 0};
      status = tlsf_gr1_both_from_target_v2(target, &routing, &combined, &e);
    } else
      status = tlsf_gr1_lift_from_target(target, &o, &solo, &e);
    if (both && fault && check_events)
      check_events(fault, stop.events);
    CHECK(tlsf_gr1_lift_test_pair_monitors(target) == pairs);
    if (bytes.find("i < j < n") != std::string::npos)
      CHECK(pairs == 15);
    auto &r = both ? combined.proof : solo;
    const char *detail = both ? combined.decline_detail : solo.decline_detail;
    if (!reason) {
      if (status != TLSF_GR1_LIFT_OK)
        std::fprintf(stderr, "parametric: %s: %s; %s\n", e.stage, e.message,
                     detail);
      CHECK(status == TLSF_GR1_LIFT_OK);
      CHECK(r.verdict == TLSF_GR1_CHECK_REGION_VERIFIED);
      auto evidence =
          tlsf_json::parse(std::string_view(r.evidence_json, r.evidence_size))
              .as_object();
      if (!both)
        CHECK(tlsf_json::serialize(evidence.at("seed_values")) ==
              (target_size == 7 ? "[4,5,6]" : "[3,4,5]"));
      CHECK(evidence.at("checker_order").as_string() == "input-first");
      auto fold = evidence.at("fold").as_object();
      CHECK(fold.at("generator").as_string() == "parametric-support-fold-v1");
      int64_t expected = 103;
      int64_t seed_size = target_size == 7 ? 4 : 3;
      for (const auto &v : fold.at("seeds").as_array()) {
        CHECK(v.as_object().at("exact_predicates").as_bool());
        CHECK(v.as_object().at("parameters").as_object().at(axis).as_int64() ==
              seed_size++);
        if (target_size != 7)
          CHECK(v.as_object().at("predicate_count").as_int64() == expected);
        expected += 31;
      }
      if (both) {
        CHECK(combined.route == TLSF_GR1_BOTH_REAL_LIFT);
        CHECK(combined.seed_solves == (target_size == 7 ? 4 : 3));
        CHECK(combined.seed_checks == combined.seed_solves);
        if (target_size == 7) {
          CHECK(combined.seed_probes == 6 && combined.seed_reductions == 5);
          CHECK(combined.seed_cache_hits == 2);
        }
        CHECK(combined.target_checks == 1);
        CHECK(tlsf_gr1_lift_target_matches(target, &r));
      }
    } else {
      if (!strstr(detail, reason))
        std::fprintf(stderr, "fault %d: %s: %s; %s\n", fault, e.stage,
                     e.message, detail);
      CHECK(status != TLSF_GR1_LIFT_OK);
      CHECK(!stop.verified);
      CHECK(strstr(detail, reason));
      CHECK(r.verdict == TLSF_GR1_CHECK_UNKNOWN && !r.certificate_aag);
      if (fault == 26) {
        CHECK(status == TLSF_GR1_LIFT_LIMIT);
        CHECK(!strcmp(e.stage, "allocation"));
        CHECK(strstr(detail, "stage=param_discovery,cause=resource"));
        CHECK(!r.game_aag && !r.evidence_json);
        if (both)
          CHECK(combined.target_checks == 0 && combined.seed_solves == 3);
      }
      if (fault == 25)
        CHECK(tlsf_gr1_lift_test_check_json_clears() == 1);
    }
    tlsf_gr1_lift_result_clear(&solo);
    tlsf_gr1_both_result_clear(&combined);
    tlsf_gr1_lift_target_free(target);
    tlsf_gr1_lift_test_set_fault(0);
  };
  attempt(source, 0, nullptr, "n", 4, true);
  attempt(source, 0, nullptr, "n", 4, true, true);
  auto unused_axis = source;
  unused_axis.insert(unused_axis.find("PARAMETERS {") + strlen("PARAMETERS {"),
                     " a = 2;");
  attempt(unused_axis, 0, nullptr, "n", 4, true);
  auto two_constants = source;
  two_constants.replace(two_constants.find("n = 6;"), strlen("n = 6;"),
                        "n = 7;");
  two_constants.insert(two_constants.find("ASSUMPTIONS {") +
                           strlen("ASSUMPTIONS {"),
                       " G F request[1];");
  attempt(two_constants, 0, nullptr, "n", 4, true, false, 7);
  for (const auto &[fault, reason] : faults)
    attempt(source, fault, reason);
  // The actual unreal2 pair obligations remain in the prepared target.
  auto unreal = source;
  const auto at = unreal.find("GUARANTEES {");
  CHECK(at != std::string::npos);
  unreal.insert(
      at, "ASSERT { &&[0 <= i < n] &&[i < j < n] "
          "(request[i] && X request[j] -> F (grant[i] && grant[j])); }\n");
  // These assert R discovery reasons; default routing may select U first.
  attempt(unreal, 0, "param_ordered_domain", "n", 4, false, true);
  const std::string fixture_path(path);
  std::ifstream growing_file(
      fixture_path.substr(0, fixture_path.find_last_of('/') + 1) +
      "parametric_growing.tlsf");
  CHECK(growing_file.good());
  const std::string growing(std::istreambuf_iterator<char>{growing_file}, {});
  attempt(growing, 0, "param_state_growth", "n", 4, false, true);
  // Raising just the arity bound reaches the same support fallback.
  attempt(source, 0, nullptr, "n", 8);
  fold_test::obfuscation_regression(source, both, "parametric-support-fold-v1");
  auto tied = source;
  tied.insert(tied.find("PARAMETERS {") + strlen("PARAMETERS {"), " a=6;");
  tied = fold_test::rename_identifier(tied, "n", "(n+a)");
  // Restore the parameter declaration after changing all extent/generator uses.
  tied.replace(tied.find("(n+a) = 6;"), strlen("(n+a) = 6;"), "n = 6;");
  attempt(tied, 0, "param_axis_ambiguous", "n", 4, false, true);
}

static void parametric_axis_regressions(const char *path, bool both) {
  std::ifstream file(path);
  CHECK(file.good());
  const std::string source(std::istreambuf_iterator<char>{file}, {});
  fold_test::axis_regressions(source, both, "parametric-support-fold-v1");
  auto several = source;
  several.insert(several.find("PARAMETERS {") + strlen("PARAMETERS {"),
                 " a=2;");
  several.insert(several.find("INPUTS {") + strlen("INPUTS {"),
                 " auxiliary[a];");
  fold_test::obfuscation_regression(several, both,
                                    "parametric-support-fold-v1");
  if (both) {
    auto early = source;
    early.insert(early.find("PARAMETERS {") + strlen("PARAMETERS {"), " a=6;");
    early.insert(early.find("INPUTS {") + strlen("INPUTS {"), " auxiliary[a];");
    const auto a = fold_test::observe(early, true);
    const auto z =
        fold_test::observe(fold_test::rename_identifier(early, "a", "z"), true);
    CHECK(a.generator == "parametric-support-fold-v1");
    CHECK(z.generator == a.generator);
    CHECK(a.seeds == std::vector<int64_t>({3, 4, 5}));
    CHECK(z.seeds == a.seeds);
    // Known legacy-order cost: U probes a first, but z follows n.
    CHECK(a.seed_solves == 6);
    CHECK(z.seed_solves == 3);
  }
}
