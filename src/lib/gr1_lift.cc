#include "oxidd_runtime.h"
#include "tlsf/gr1_lift.h"
#include "gr1_shared.hh"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/oxidd_options.h"
#include "tlsf/templates.h"
#include "oxidd_common.h"
#include "pipeline_source_internal.h"
extern "C" {
#include "sha256.h"
}

#include "yyjson_cpp.hh"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <functional>
#include <iterator>
#ifdef __GLIBC__
#include <malloc.h>
#endif
#include <map>
#include <memory>
#include <new>
#include <numeric>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#ifdef TLSF_GR1_LIFT_TEST_FAULT
#include <thread>
#endif
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <sys/resource.h>

using namespace gr1_lift_internal;

namespace gr1_lift_internal {
const char env_stage_seed_window[] = "seed_window";
const char env_side_system[] = "system";
#ifdef TLSF_GR1_LIFT_TEST_FAULT
thread_local uint64_t lift_test_reduction_calls = 0;
thread_local unsigned lift_test_check_json_clears = 0;
thread_local int both_test_seed_fault = 0;
thread_local uint64_t both_test_candidate_ns = 0;
thread_local int both_test_check_fault = 0;
thread_local size_t both_test_env_rss_spike_bytes = 0;
#endif
namespace j = tlsf_json;
using namespace oxidd::capi;
using J = j::value;
using O = j::object;
using A = j::array;
// The observer is scoped to a combined call, including exceptional returns.
thread_local const TlsfGr1BothObserverV1 *phase_observer = nullptr;
struct BothPhase {
  const TlsfGr1BothObserverV1 *observer;
  const char *name;
  bool active;
  BothPhase(const char *value, const char *artifact = nullptr)
      : observer(phase_observer), name(value),
        active(observer && observer->phase) {
    if (active) {
      try {
        observer->phase(observer->context, name, 1, artifact);
      } catch (...) {
        active = false;
      }
    }
  }
  void finish() {
    if (active) {
      try {
        observer->phase(observer->context, name, 0, nullptr);
      } catch (...) {
      }
    }
    active = false;
  }
  ~BothPhase() { finish(); }
};
uint64_t now_ns() {
  timespec ts{};
  if (clock_gettime(CLOCK_MONOTONIC, &ts))
    throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "clock",
                  "CLOCK_MONOTONIC failed");
  return uint64_t(ts.tv_sec) * 1000000000ull + uint64_t(ts.tv_nsec);
}
uint64_t stats_clock(clockid_t clock) noexcept {
  timespec ts{};
  return clock_gettime(clock, &ts) == 0
             ? uint64_t(ts.tv_sec) * 1000000000ull + uint64_t(ts.tv_nsec)
             : 0;
}
struct StatsScope {
  TlsfGr1LiftStats *stats;
  TlsfGr1LiftStatsStage stage;
  void (*callback)(void *, TlsfGr1LiftStatsStage,
                   const TlsfGr1LiftStageStats *);
  void *context;
  uint64_t wall = 0, cpu = 0;
  const size_t *work_counter = nullptr;
  size_t work_start = 0;
  StatsScope(const Config &cfg, TlsfGr1LiftStatsStage which) noexcept
      : stats(cfg.stats), stage(which), callback(cfg.stats_callback),
        context(cfg.stats_context) {
    if (stats) {
      wall = stats_clock(CLOCK_MONOTONIC);
      cpu = stats_clock(CLOCK_PROCESS_CPUTIME_ID);
    }
  }
  ~StatsScope() noexcept { finish(); }
  void count_bdd_ops(const size_t *counter) noexcept {
    work_counter = counter;
    work_start = *counter;
  }
  void finish() noexcept {
    if (!stats || !wall)
      return;
    TlsfGr1LiftStageStats event{};
    event.wall_ns = stats_clock(CLOCK_MONOTONIC) - wall;
    event.cpu_ns = stats_clock(CLOCK_PROCESS_CPUTIME_ID) - cpu;
    event.calls = work_counter ? *work_counter - work_start : 1;
    auto &row = stats->stages[stage];
    event.rss_kb = -1;
    uint64_t rss_bytes = 0;
    if (tlsf_current_rss_bytes(&rss_bytes))
      event.rss_kb = (long)(rss_bytes / 1024u);
    rusage usage{};
    getrusage(RUSAGE_SELF, &usage);
    event.peak_rss_kb = usage.ru_maxrss;
#ifdef __APPLE__
    event.peak_rss_kb /= 1024;
#endif
#if defined(__GLIBC__) &&                                                      \
    (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 33))
    const auto heap = mallinfo2();
    event.arena = heap.arena;
    event.hblkhd = heap.hblkhd;
    event.uordblks = heap.uordblks;
    event.fordblks = heap.fordblks;
#endif
    row.wall_ns += event.wall_ns;
    row.cpu_ns += event.cpu_ns;
    row.calls += event.calls;
    row.rss_kb = event.rss_kb;
    row.peak_rss_kb = event.peak_rss_kb;
    row.arena = event.arena;
    row.hblkhd = event.hblkhd;
    row.uordblks = event.uordblks;
    row.fordblks = event.fordblks;
    wall = 0;
    if (callback)
      callback(context, stage, &event);
  }
};
std::string str(const J &v) { return std::string(v.as_string()); }
std::string s(const O &o, const char *k) { return str(o.at(k)); }
int64_t num(const J &v) {
  return v.is_int64() ? v.as_int64() : int64_t(v.as_uint64());
}
int64_t n(const O &o, const char *k) { return num(o.at(k)); }
std::string dump(const J &v) { return j::serialize(v); }
std::vector<int> ints(const A &a) {
  std::vector<int> x;
  for (const auto &v : a)
    x.push_back(int(num(v)));
  return x;
}
std::string join(const std::vector<std::string> &v) {
  std::string x;
  for (const auto &part : v) {
    x += std::to_string(part.size()) + ":" + part;
  }
  return x;
}
std::string key(std::initializer_list<std::string> parts) {
  return join(std::vector<std::string>(parts));
}

std::unique_ptr<Aig, decltype(&aig_free)> parse_aig(const char *bytes,
                                                    size_t size) {
  FILE *fp = fmemopen(const_cast<char *>(bytes), size, "r");
  if (!fp)
    throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "aag",
                  "cannot open memory stream");
  Aig *raw = aig_read_aag(fp);
  fclose(fp);
  if (!raw)
    decline(FailureCause::error, "aag", "invalid AAG artifact");
  return {raw, &aig_free};
}
std::string render_aig(const Aig *game, const Config &cfg) {
  char *bytes = nullptr;
  size_t size = 0;
  FILE *fp = open_memstream(&bytes, &size);
  if (!fp)
    throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "aag",
                  "cannot allocate memory stream");
  aig_write_aag(fp, game);
  if (fclose(fp)) {
    free(bytes);
    throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "aag",
                  "write failed");
  }
  std::string out(bytes, size);
  free(bytes);
  cfg.bytes(out.size(), "aag");
  return out;
}

// The C frontend cannot unwind callbacks. Preserve the arm's exact failure
// until its arena has stopped expansion and the pipeline has cleaned up.
struct FrontendBudget {
  const Config &cfg;
  std::exception_ptr failure;
  static int cancelled(void *raw, size_t bytes) noexcept {
    auto &self = *static_cast<FrontendBudget *>(raw);
    if (self.failure)
      return 1;
    try {
      self.cfg.check("expand", bytes != 0);
      uint64_t limit = self.cfg.budget ? self.cfg.budget->max_rss_bytes : 0;
      if (self.cfg.env_budget && self.cfg.env_budget->max_rss_bytes &&
          (!limit || self.cfg.env_budget->max_rss_bytes < limit))
        limit = self.cfg.env_budget->max_rss_bytes;
      if (bytes && limit) {
        uint64_t current = 0;
        if (!tlsf_current_rss_bytes(&current))
          throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error,
                        "budget-memory", "cannot measure frontend RSS");
        if (current > limit || bytes > limit - current)
          throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                        "budget-memory", "frontend allocation exceeds arm RSS");
      }
      return 0;
    } catch (...) {
      self.failure = std::current_exception();
      return 1;
    }
  }
};

std::unique_ptr<Instance> lower(const uint8_t *source, size_t size,
                                const std::map<std::string, int64_t> &overrides,
                                TlsfGr1ReductionSemantics semantics,
                                const Config &cfg, bool fold_seed) {
  BothPhase phase("native_candidate_reduction");
  cfg.check("expand");
  auto instance = std::make_unique<Instance>();
  instance->overrides = overrides;
  std::vector<ParamOverride> params;
  params.reserve(overrides.size());
  for (const auto &[name, value] : overrides)
    params.push_back({name.c_str(), value});
  TlsfPipelineError perr{};
  TlsfPipelineOptions popts{};
  popts.certify = true;
  popts.template_mask = TPL_ALL;
  popts.overrides = params.data();
  popts.n_overrides = params.size();
  popts.require_unambiguous_origin = true;
  popts.error = &perr;
  FrontendBudget frontend_budget{cfg, {}};
  if (cfg.effective_deadline() || cfg.o.cancelled ||
      (cfg.budget && cfg.budget->max_rss_bytes) ||
      (cfg.env_budget && cfg.env_budget->max_rss_bytes)) {
    popts.frontend_cancelled = FrontendBudget::cancelled;
    popts.frontend_cancel_ctx = &frontend_budget;
  }
  popts.limit_generated_depth = fold_seed;
  auto pipeline = std::unique_ptr<TlsfPipeline, decltype(&tlsf_pipeline_free)>(
      tlsf_pipeline_load_frontend_bytes(source, size, &popts),
      &tlsf_pipeline_free);
  if (frontend_budget.failure)
    std::rethrow_exception(frontend_budget.failure);
  if (!pipeline) {
    if (perr.status == TLSF_PIPELINE_LIMIT)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "expand",
                    perr.message);
    decline(perr.status == TLSF_PIPELINE_DECLINED ? FailureCause::applicability
                                                  : FailureCause::error,
            perr.status == TLSF_PIPELINE_DECLINED ? "expand" : "expand_error",
            perr.message[0] ? perr.message : "source expansion failed");
  }
  cfg.check("reduce");
  TlsfGr1ReductionOptions ro{};
  ro.semantics = semantics;
  ro.deadline_mono_ns = cfg.effective_deadline();
  ro.cancelled = cfg.o.cancelled;
  ro.cancel_ctx = cfg.o.cancel_ctx;
  ro.max_artifact_bytes = cfg.o.max_artifact_bytes;
  ro.max_monitor_states = cfg.o.max_monitor_states;
  ro.budget = *cfg.budget;
  if (cfg.env_budget && cfg.env_budget->max_rss_bytes &&
      (!ro.budget.max_rss_bytes ||
       cfg.env_budget->max_rss_bytes < ro.budget.max_rss_bytes))
    ro.budget.max_rss_bytes = cfg.env_budget->max_rss_bytes;
  TlsfGr1ReductionStats reduction_stats{};
  ro.stats = cfg.stats ? &reduction_stats : nullptr;
  TlsfGr1ReductionError err{};
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  lift_test_reduction_calls++;
#endif
  TlsfGr1ReductionStatus reduction_cause = TLSF_GR1_REDUCE_OK;
  auto status = tlsf_gr1_reduce_v1(pipeline.get(), &ro, &instance->r, &err,
                                   &reduction_cause);
  const TlsfGr1ConstructionWork &reduction_work = reduction_stats.work;
  if (cfg.work) {
    auto add = [](uint64_t &dst, uint64_t value) {
      dst = value > UINT64_MAX - dst ? UINT64_MAX : dst + value;
    };
    add(cfg.work->formula_nodes, reduction_work.formula_nodes);
    cfg.work->ap_count = std::max(cfg.work->ap_count, reduction_work.ap_count);
    add(cfg.work->conjuncts, reduction_work.conjuncts);
    cfg.work->max_conjunct_nodes = std::max(cfg.work->max_conjunct_nodes,
                                            reduction_work.max_conjunct_nodes);
    cfg.work->max_temporal_depth = std::max(cfg.work->max_temporal_depth,
                                            reduction_work.max_temporal_depth);
    add(cfg.work->predicted_monitor_states,
        reduction_work.predicted_monitor_states);
    add(cfg.work->monitors_completed, reduction_work.monitors_completed);
    add(cfg.work->states, reduction_work.states);
    add(cfg.work->edges, reduction_work.edges);
    cfg.work->peak_rss_bytes =
        std::max(cfg.work->peak_rss_bytes, reduction_work.peak_rss_bytes);
  }
  if (cfg.stats) {
    cfg.stats->monitor_count_total += reduction_stats.monitor_count;
    cfg.stats->monitor_states_total += reduction_stats.monitor_states;
  }
  if (status != TLSF_GR1_REDUCE_OK) {
    TlsfGr1LiftStatus mapped = TLSF_GR1_LIFT_DECLINED;
    if (status == TLSF_GR1_REDUCE_LIMIT)
      mapped = TLSF_GR1_LIFT_LIMIT;
    if (status == TLSF_GR1_REDUCE_DEADLINE)
      throw cfg.deadline_failure(err.stage[0] ? err.stage : "reduce");
    if (status == TLSF_GR1_REDUCE_CANCELLED)
      mapped = TLSF_GR1_LIFT_CANCELLED;
    const bool internal =
        status == TLSF_GR1_REDUCE_ERROR || status == TLSF_GR1_REDUCE_INVALID;
    const auto cause = reduction_cause == TLSF_GR1_REDUCE_ERROR ||
                               reduction_cause == TLSF_GR1_REDUCE_INVALID
                           ? FailureCause::error
                           : failure_cause(mapped);
    throw Failure(mapped, cause,
                  internal       ? "reduce_error"
                  : err.stage[0] ? err.stage
                                 : "reduce",
                  err.message[0] ? err.message : "reduction failed");
  }
  cfg.check("provenance");
  instance->data = j::parse(std::string_view(instance->r.provenance_json,
                                             instance->r.provenance_size))
                       .as_object();
  const O &d = instance->data;
  const O &origin = d.at("source_origin_metadata").as_object();
  if (s(d, "provenance_source") != "frontend" ||
      !origin.at("available").as_bool() ||
      s(origin, "provenance_source") != "frontend")
    decline(FailureCause::applicability, "provenance",
            "ambiguous or source-unbound frontend provenance");
  if (s(origin, "source_sha256") != pipeline->source_sha256)
    decline(FailureCause::error, "target_binding",
            "frontend provenance source hash differs");
  std::set<std::string> signals;
  for (const char *kind : {"inputs", "outputs"})
    for (const auto &v : d.at(kind).as_array()) {
      const O &row = v.as_object();
      if (s(row, "provenance_source") != "frontend" ||
          !signals.insert(s(row, "name")).second)
        decline(FailureCause::error, "provenance",
                "duplicate or non-frontend signal");
    }
  std::set<std::string> origins;
  for (const auto &v : d.at("source_conjuncts").as_array()) {
    const O &row = v.as_object();
    if (!origins
             .insert(key({s(row, "source_formula_id"),
                          field(n(row, "generated_position"))}))
             .second)
      decline(FailureCause::error, "provenance",
              "duplicate source conjunct origin");
  }
  for (const auto &v : d.at("monitors").as_array()) {
    const O &row = v.as_object();
    if (s(row, "provenance_source") != "frontend" ||
        !row.contains("source_origin") || row.at("source_origin").is_null())
      decline(FailureCause::applicability, "provenance",
              "missing monitor source origin");
  }
  return instance;
}
std::map<std::string, int64_t> parameters(const Instance &i) {
  std::map<std::string, int64_t> out;
  for (const auto &v : i.data.at("source_parameters").as_array()) {
    const O &r = v.as_object();
    if (!out.emplace(s(r, "name"), n(r, "value")).second)
      decline(FailureCause::error, "parameters", "duplicate source parameter");
  }
  return out;
}
std::map<std::string, std::vector<const O *>>
declarations(const Instance &i, const Config *cfg = nullptr) {
  std::map<std::string, std::vector<const O *>> groups;
  for (const char *kind : {"inputs", "outputs"})
    for (const auto &v : i.data.at(kind).as_array()) {
      if (cfg)
        cfg->check("param_inventory");
      const O &r = v.as_object();
      groups[s(r, "declaration_id")].push_back(&r);
    }
  return groups;
}
std::pair<std::vector<int>, std::vector<int>>
axis_members(const Instance &target, const Instance &probe, const Config *cfg) {
  auto tg = declarations(target, cfg), pg = declarations(probe, cfg);
  if (tg.size() != pg.size())
    decline(FailureCause::applicability, "axis", "declaration_abi_changed");
  std::vector<int> target_members, probe_members;
  bool changed = false;
  for (const auto &[id, trows] : tg) {
    if (cfg)
      cfg->check("param_domain");
    auto iter = pg.find(id);
    if (iter == pg.end())
      decline(FailureCause::applicability, "axis", "declaration_abi_changed");
    const auto &prows = iter->second;
    if (trows.size() == prows.size())
      continue;
    changed = true;
    std::vector<int> ti, pi;
    for (const auto *r : trows) {
      if (cfg)
        cfg->check("param_domain");
      if (s(*r, "index_role") != "element" || n(*r, "dimensions") != 1)
        decline(FailureCause::applicability, "axis", "encoding_width");
      ti.push_back(ints(r->at("index_tuple").as_array()).at(0));
    }
    for (const auto *r : prows) {
      if (cfg)
        cfg->check("param_domain");
      if (s(*r, "index_role") != "element" || n(*r, "dimensions") != 1)
        decline(FailureCause::applicability, "axis", "encoding_width");
      pi.push_back(ints(r->at("index_tuple").as_array()).at(0));
    }
    std::sort(ti.begin(), ti.end());
    std::sort(pi.begin(), pi.end());
    if (!target_members.empty() && target_members != ti)
      decline(FailureCause::applicability, "axis", "inconsistent_coordinates");
    if (!probe_members.empty() && probe_members != pi)
      decline(FailureCause::applicability, "axis", "inconsistent_coordinates");
    target_members = std::move(ti);
    probe_members = std::move(pi);
  }
  if (!changed)
    decline(FailureCause::applicability, "axis", "parameter_not_indexed");
  return {target_members, probe_members};
}
std::pair<std::vector<int>, std::vector<int>>
axis_members(const Instance &target, const Instance &probe) {
  return axis_members(target, probe, nullptr);
}
std::vector<int> monitor_indices(const O &record, const Config *cfg = nullptr) {
  const O &origin = record.at("source_origin").as_object();
  auto bound = ints(origin.at("index_tuple").as_array());
  if (!bound.empty())
    return bound;
  std::set<int> result;
  for (const J &v : origin.at("signal_refs").as_array()) {
    if (cfg)
      cfg->check("param_inventory");
    const O &ref = v.as_object();
    if (s(ref, "index_role") == "element")
      for (int coord : ints(ref.at("index_tuple").as_array()))
        result.insert(coord);
  }
  return {result.begin(), result.end()};
}
std::string monitor_identity(const O &r) {
  const O &o = r.at("source_origin").as_object();
  return key({s(o, "source_formula_id"), field(n(o, "source_node_id"))});
}
std::optional<std::string> symmetric_key(const O &r, const Instance &instance,
                                         const Config *cfg = nullptr) {
  auto sig = r.if_contains("symmetric_signature");
  if (!sig || !sig->is_object())
    return std::nullopt;
  auto groups = declarations(instance, cfg);
  std::vector<std::string> entries;
  for (const auto &[id, value] : sig->as_object()) {
    if (cfg)
      cfg->check("param_inventory");
    auto iter = groups.find(std::string(id));
    if (iter == groups.end() || !value.is_array())
      return std::nullopt;
    std::vector<int> counts = ints(value.as_array());
    int width = int(iter->second.size());
    std::string normal;
    if (counts.empty())
      normal = "empty";
    else {
      bool interval = true;
      for (size_t k = 1; k < counts.size(); k++)
        interval &= counts[k] == counts[0] + int(k);
      if (interval)
        normal = key({"interval", field(counts.front()),
                      counts.back() == width ? "all" : field(counts.back())});
      else {
        std::vector<std::string> bits{"set"};
        for (int x : counts)
          bits.push_back(x == width ? "all" : field(x));
        normal = join(bits);
      }
    }
    entries.push_back(key({std::string(id), normal}));
  }
  std::sort(entries.begin(), entries.end());
  return join(entries);
}
struct Modes {
  std::map<std::string, bool> symmetric;
};
Modes target_modes(const Instance &target) {
  Modes modes;
  for (const J &v : target.data.at("monitors").as_array()) {
    const O &r = v.as_object();
    modes.symmetric[monitor_identity(r)] = s(r, "arity_kind") == "bus_wide" &&
                                           symmetric_key(r, target).has_value();
  }
  return modes;
}
std::string monitor_key(const O &r, const Instance &i, const Modes &m,
                        const Config &cfg) {
  const O &o = r.at("source_origin").as_object();
  bool symmetric = false;
  auto mode = m.symmetric.find(monitor_identity(r));
  if (mode != m.symmetric.end())
    symmetric = mode->second;
  else
    symmetric = s(r, "arity_kind") == "bus_wide";
  std::string semantic;
  std::string kind = "bounded_support";
  if (symmetric) {
    auto signature = symmetric_key(r, i);
    if (signature) {
      semantic = *signature;
      kind = "symmetric";
    }
  }
  if (kind == "bounded_support") {
    const auto arity = monitor_indices(r).size();
    if (arity > cfg.o.max_predicate_arity) {
      char reason[96];
      snprintf(reason, sizeof reason, "large_template(arity %zu>%u)", arity,
               cfg.o.max_predicate_arity);
      decline(FailureCause::applicability, "bus_schema", reason);
    }
    semantic = s(r, "template");
  }
  return key({s(o, "source_formula_id"), field(n(o, "source_node_id")),
              s(r, "side"), s(r, "role"), s(r, "mp_class"), kind,
              field(n(r, "state_count")), semantic});
}
bool monitor_is_symmetric(const O &r, const Instance &i, const Modes &m) {
  auto mode = m.symmetric.find(monitor_identity(r));
  bool requested = mode != m.symmetric.end() ? mode->second
                                             : s(r, "arity_kind") == "bus_wide";
  return requested && symmetric_key(r, i).has_value();
}
std::string structural_shape(const Instance &i, const Modes &m,
                             const Config &cfg) {
  std::set<std::string> decls, sources, monitors;
  for (const char *kind : {"inputs", "outputs"})
    for (const J &v : i.data.at(kind).as_array()) {
      const O &r = v.as_object();
      decls.insert(key({s(r, "declaration_id"), s(r, "direction"),
                        field(n(r, "dimensions")), s(r, "index_role"),
                        s(r, "width_kind")}));
    }
  for (const J &v : i.data.at("source_conjuncts").as_array()) {
    const O &r = v.as_object();
    std::vector<std::string> binders;
    for (const J &b : r.at("bindings").as_array())
      binders.push_back(field(n(b.as_object(), "binder_id")));
    sources.insert(key({s(r, "source_formula_id"),
                        field(n(r, "source_node_id")), join(binders)}));
  }
  for (const J &v : i.data.at("monitors").as_array())
    monitors.insert(monitor_key(v.as_object(), i, m, cfg));
  return key({join({decls.begin(), decls.end()}),
              join({sources.begin(), sources.end()}),
              join({monitors.begin(), monitors.end()}),
              s(i.data, "latch_encoding")});
}
using Roles = std::map<int, std::string>;
Roles role_signatures(const Instance &i, const Modes &m, const Config &cfg,
                      const std::vector<int> *coordinates = nullptr) {
  const auto &members = coordinates ? *coordinates : i.members;
  struct Count {
    int count = 0;
    int arity = 0;
    bool normalize = false;
  };
  std::map<int, std::map<std::string, Count>> incidents;
  for (int coord : members)
    incidents[coord];
  auto add = [&](int coord, std::string k, int arity, bool normalize) {
    auto it = incidents.find(coord);
    if (it != incidents.end()) {
      auto &c = it->second[k];
      c.count++;
      c.arity = arity;
      c.normalize = normalize;
    }
  };
  for (const char *kind : {"inputs", "outputs"})
    for (const J &v : i.data.at(kind).as_array()) {
      const O &r = v.as_object();
      if (s(r, "index_role") == "element" &&
          r.at("index_tuple").as_array().size() == 1)
        add(ints(r.at("index_tuple").as_array())[0],
            key({"declaration", s(r, "declaration_id")}), 1, false);
    }
  for (const J &v : i.data.at("monitors").as_array()) {
    const O &r = v.as_object();
    std::string mk = monitor_key(r, i, m, cfg);
    if (monitor_is_symmetric(r, i, m))
      continue;
    auto indices = monitor_indices(r);
    int arity = int(
        r.at("source_origin").as_object().at("index_tuple").as_array().size());
    for (size_t p = 0; p < indices.size(); p++)
      add(indices[p], key({"monitor", mk, field(p), field(arity)}), arity,
          true);
  }
  for (const J &v : i.data.at("source_conjuncts").as_array()) {
    const O &r = v.as_object();
    std::vector<int> bindings;
    for (const J &b : r.at("bindings").as_array())
      bindings.push_back(int(n(b.as_object(), "value")));
    std::vector<std::string> shapes;
    for (const J &ref : r.at("signal_refs").as_array()) {
      const O &sr = ref.as_object();
      std::vector<std::string> relation;
      for (int coordinate : ints(sr.at("index_tuple").as_array())) {
        std::vector<std::string> positions;
        for (size_t p = 0; p < bindings.size(); p++)
          if (bindings[p] == coordinate)
            positions.push_back(field(p));
        if (!positions.empty())
          relation.push_back(key({"bound", join(positions)}));
        else if (!bindings.empty()) {
          std::vector<std::string> offsets;
          for (int bound : bindings)
            offsets.push_back(field(coordinate - bound));
          relation.push_back(key({"relative", join(offsets)}));
        } else
          relation.push_back(key({"fixed", field(coordinate)}));
      }
      shapes.push_back(key({s(sr, "declaration_id"), join(relation)}));
    }
    std::sort(shapes.begin(), shapes.end());
    std::string shape = key({s(r, "source_formula_id"),
                             field(n(r, "source_node_id")), join(shapes)});
    for (size_t p = 0; p < bindings.size(); p++)
      add(bindings[p],
          key({"conjunct", shape, field(p), field(bindings.size())}),
          int(bindings.size()), true);
  }
  Roles out;
  for (auto &[coord, counts] : incidents) {
    std::vector<std::string> bits;
    for (const auto &[k, c] : counts) {
      std::string degree =
          c.normalize && c.arity > 1 && c.count == int(members.size()) - 1
              ? "all_except_self"
          : c.count == 1                   ? "one"
          : c.count == int(members.size()) ? "all"
                                           : key({"count", field(c.count)});
      bits.push_back(key({k, degree}));
    }
    out[coord] = join(bits);
  }
  return out;
}

struct Window {
  std::string axis;
  std::vector<int> sizes;
  std::vector<int> target_members;
  std::vector<std::unique_ptr<Instance>> seeds;
  Modes modes;
  bool fold = false;
  bool param = false;
  uint64_t fold_probes = 0, fold_reductions = 0;
};
#ifdef TLSF_GR1_LIFT_TEST_FAULT
thread_local int lift_test_fault = 0;
thread_local std::string lift_test_generated_certificate_json;
thread_local std::string lift_test_checked_game_aag;
thread_local bool lift_test_fallback_started_before_deadline = false;
thread_local void (*lift_test_param_activation)(TlsfGr1LiftOptions *) = nullptr;
thread_local void (*lift_test_axis_scan)(TlsfGr1LiftOptions *, bool) = nullptr;
#endif
void validate_window(const Window &window, const Instance &target) {
  if (window.sizes.size() != window.seeds.size() || window.sizes.size() < 2)
    decline(FailureCause::error, "seed_window", "invalid selected seed count");
  for (size_t p = 0; p < window.seeds.size(); p++) {
    const Instance &seed = *window.seeds[p];
    auto choice = seed.overrides.find(window.axis);
    if (choice == seed.overrides.end() || choice->second != window.sizes[p] ||
        seed.members != axis_members(target, seed).second)
      decline(FailureCause::error, "seed_window",
              "selected seed choice disagrees with artifact");
    if (p && window.sizes[p] != window.sizes[p - 1] + 1)
      decline(FailureCause::error, "seed_window",
              "selected seeds are not consecutive");
  }
}
// Keep failure diagnostics allocation-free, including the current axis/window.
struct SeedDeclines {
  char *detail;
  char candidate[TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE] = "parameters";
  void at(const std::string &axis, int first = 0, int last = 0,
          const char *side = "") noexcept {
    if (!first)
      snprintf(candidate, sizeof candidate, "%s%s", axis.c_str(), side);
    else if (first == last)
      snprintf(candidate, sizeof candidate, "%s[%d]%s", axis.c_str(), first,
               side);
    else
      snprintf(candidate, sizeof candidate, "%s[%d..%d]%s", axis.c_str(), first,
               last, side);
  }
  void note(const char *reason) const noexcept {
    constexpr size_t cap = TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE;
    constexpr char marker[] = "; [truncated]";
    const size_t used = strlen(detail);
    if (used >= sizeof marker - 1 &&
        !strcmp(detail + used - (sizeof marker - 1), marker))
      return;
    char entry[cap];
    const int length = snprintf(entry, sizeof entry, "%s%s=%s",
                                used ? "; " : "", candidate, reason);
    if (length < 0 || size_t(length) + used + sizeof marker > cap) {
      snprintf(detail + used, cap - used, "%s", marker);
      return;
    }
    memcpy(detail + used, entry, size_t(length) + 1);
  }
  void failure(const Failure &e) const noexcept {
    const char *cause = "error";
    switch (e.cause) {
    case FailureCause::applicability:
      cause = "applicability";
      break;
    case FailureCause::unsupported:
      cause = "unsupported";
      break;
    case FailureCause::resource:
      cause = "resource";
      break;
    case FailureCause::deadline:
      cause = "deadline";
      break;
    case FailureCause::cancelled:
      cause = "cancelled";
      break;
    case FailureCause::invalid:
      cause = "invalid";
      break;
    case FailureCause::error:
      break;
    }
    const bool reason_code = e.stage == "axis" || e.stage == "bus_schema" ||
                             e.stage.compare(0, 4, "fold") == 0 ||
                             e.stage.compare(0, 5, "param") == 0;
    const char *kind = reason_code                  ? e.what()
                       : e.stage == "budget-memory" ? "memory_budget"
                       : e.cause == FailureCause::deadline ||
                               !strcmp(e.what(), "fixed phase budget exhausted")
                           ? "time_budget"
                           : "probe_failure";
    char reason[TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE];
    snprintf(reason, sizeof reason, "%s(stage=%s,cause=%s)%s%s", kind,
             e.stage.c_str(), cause, reason_code ? "" : ":",
             reason_code ? "" : e.what());
    note(reason);
  }
  void exception(const char *stage, const char *cause,
                 const char *message) const noexcept {
    char reason[TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE];
    snprintf(reason, sizeof reason, "probe_failure(stage=%s,cause=%s):%s",
             stage, cause, message);
    note(reason);
  }
};

// IDs locate provenance rows, but cannot order axes: declaration/source IDs
// change under reordering. Compare multisets of structural incidence instead.
// Legacy/U also admit monitor-support widths; unused parameters have no
// incidence. All discovery paths decline structural ties.
std::vector<std::string> fold_axes(const Instance &target, const Config &config,
                                   SeedDeclines log, bool encoded,
                                   bool legacy = false) {
  log.at(encoded ? "fold" : "param");
  try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    Config cfg = config;
#else
    const Config &cfg = config;
#endif
    std::map<int64_t, std::string> names;
    for (const J &v : target.data.at("source_parameters").as_array())
      names.emplace(n(v.as_object(), "id"), s(v.as_object(), "name"));
    std::map<std::string, std::vector<std::string>> occurrences;
    for (const J &v : target.data.at("monitors").as_array()) {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      if (lift_test_axis_scan && !legacy)
        lift_test_axis_scan(&cfg.o, encoded);
#endif
      cfg.check("fold_discovery");
      const O &m = v.as_object();
      const O &o = m.at("source_origin").as_object();
      std::map<std::string, size_t> refs;
      for (const J &ref : o.at("signal_refs").as_array()) {
        cfg.check("fold_discovery");
        ++refs[s(ref.as_object(), "declaration_id")];
      }
      for (const auto &[id, count] : refs)
        occurrences[id].push_back(
            key({s(m, "side"), s(m, "role"), s(m, "mp_class"),
                 field(n(m, "state_count")),
                 field(o.at("bindings").as_array().size()), field(count)}));
    }
    std::map<int64_t, std::vector<std::string>> incidence;
    for (const auto &[id, rows] : declarations(target, &cfg)) {
      cfg.check("fold_discovery");
      const O &r = *rows.front();
      const auto role = s(r, "index_role");
      if (occurrences[id].empty() ||
          (!legacy &&
           (role != (encoded ? "representation-bit" : "element") ||
            (encoded && s(r, "width_kind") != "proved-logarithmic-encoding") ||
            (!encoded && !r.at("width_binding_complete").as_bool()))))
        continue;
      auto &uses = occurrences[id];
      std::sort(uses.begin(), uses.end());
      const auto signature = key({s(r, "direction"), role, s(r, "width_kind"),
                                  dump(r.at("bounds")), join(uses)});
      for (const J &p : r.at("width_parameter_ids").as_array())
        incidence[num(p)].push_back(signature);
    }
    if (legacy)
      for (const auto &[id, name] : names)
        if (!incidence.contains(id)) {
          log.at(name);
          log.note("parameter_not_indexed");
        }
    std::map<std::string, std::vector<std::string>> ordered;
    for (auto &[id, uses] : incidence) {
      std::sort(uses.begin(), uses.end());
      ordered[join(uses)].push_back(names.at(id));
    }
    std::vector<std::string> axes;
    for (const auto &[signature, tied] : ordered) {
      if (tied.size() == 1)
        axes.push_back(tied.front());
      else {
        // Decline indistinguishable axes rather than breaking ties by spelling.
        log.at(encoded ? "fold" : "param");
        log.note(encoded ? "fold_axis_ambiguous" : "param_axis_ambiguous");
      }
    }
    return axes;
  } catch (const Failure &e) {
    log.failure(e);
    throw;
  } catch (const std::bad_alloc &) {
    log.exception("fold_discovery", "resource", "host allocation failed");
    throw;
  } catch (const std::exception &e) {
    log.exception("fold_discovery", "error", e.what());
    throw;
  }
}

struct FoldProbes {
  uint64_t tried = 0, reductions = 0;
};
bool legacy_probe_limit(const Failure &e) {
  return e.stage == "seed_window" &&
         !strcmp(e.what(),
                 "probe_budget_exhausted: fixed seed probe budget exhausted");
}

// Representation bits are never client coordinates. These profiles use only
// the frontend's structural width proof and parameter IDs, never source names.
std::vector<int> fold_widths(const Instance &i, const std::string &axis) {
  int64_t parameter = -1;
  for (const auto &v : i.data.at("source_parameters").as_array())
    if (s(v.as_object(), "name") == axis)
      parameter = n(v.as_object(), "id");
  std::vector<int> widths;
  for (const auto &[id, rows] : declarations(i)) {
    const O &r = *rows.front();
    if (s(r, "index_role") != "representation-bit")
      continue;
    for (const O *row : rows)
      if (s(*row, "width_kind") != "proved-logarithmic-encoding" ||
          n(*row, "dimensions") != 1 ||
          ints(row->at("width_parameter_ids").as_array()) !=
              std::vector<int>{int(parameter)})
        decline(FailureCause::applicability, "fold_detection",
                "fold_unproved_width");
    widths.push_back(int(rows.size()));
  }
  if (widths.empty())
    decline(FailureCause::applicability, "fold_detection",
            "fold_unproved_width");
  return widths;
}
std::vector<int> fold_profile(std::vector<int> widths) {
  const int smallest = *std::min_element(widths.begin(), widths.end());
  for (int &w : widths)
    w -= smallest;
  return widths;
}
std::string fold_key(const O &r) {
  std::vector<std::string> parts{monitor_identity(r), s(r, "side"),
                                 s(r, "role"), s(r, "mp_class")};
  const O &origin = r.at("source_origin").as_object();
  std::vector<int> bound;
  for (const J &v : origin.at("bindings").as_array()) {
    const O &binding = v.as_object();
    parts.push_back(field(n(binding, "binder_id")));
    bound.push_back(int(n(binding, "value")));
  }
  if (bound != ints(origin.at("index_tuple").as_array()) || bound.size() > 1)
    decline(FailureCause::applicability, "fold_detection",
            "fold_generator_binding");
  return join(parts);
}
using FoldInventory = std::map<std::string, std::vector<const O *>>;
FoldInventory fold_inventory(const Instance &i) {
  FoldInventory out;
  std::set<int> latches;
  std::set<std::string> occurrences;
  for (const J &v : i.data.at("monitors").as_array()) {
    const O &r = v.as_object();
    const auto schema = fold_key(r);
    const auto &o = r.at("source_origin").as_object();
    if (!occurrences
             .insert(key({schema, dump(o.at("index_tuple")),
                          field(n(o, "generated_position"))}))
             .second)
      decline(FailureCause::applicability, "fold_detection",
              "fold_generator_binding");
    auto lits = ints(r.at("latch_literals").as_array());
    if (lits.empty() || lits.size() != size_t(n(r, "state_count")))
      decline(FailureCause::applicability, "fold_detection",
              "fold_monitor_inventory");
    for (int lit : lits)
      if (!latches.insert(lit).second)
        decline(FailureCause::error, "fold_detection",
                "fold_monitor_inventory");
    out[schema].push_back(&r);
  }
  for (uint32_t p = 0; p < aig_num_latches(i.r.game); p++) {
    uint32_t lit;
    aig_latch_at(i.r.game, p, &lit, nullptr, nullptr);
    if (!latches.erase(int(lit)))
      decline(FailureCause::applicability, "fold_detection",
              "fold_monitor_inventory");
  }
  if (!latches.empty() || out.empty())
    decline(FailureCause::applicability, "fold_detection",
            "fold_monitor_inventory");
  return out;
}

// Route B uses only frontend occurrence/binder identities and concrete
// inventories. It generates candidates; only the unchanged target region check
// proves a verdict.
std::string param_key(const O &r, const Config *cfg = nullptr) {
  const O &o = r.at("source_origin").as_object();
  std::vector<std::string> parts{monitor_identity(r), s(r, "side"),
                                 s(r, "role"), s(r, "mp_class")};
  for (const J &b : o.at("bindings").as_array()) {
    if (cfg)
      cfg->check("param_inventory");
    parts.push_back(field(n(b.as_object(), "binder_id")));
  }
  return join(parts);
}
FoldInventory param_inventory(const Instance &i, const Config &cfg) {
  FoldInventory out;
  for (const J &v : i.data.at("monitors").as_array()) {
    cfg.check("param_inventory");
    out[param_key(v.as_object(), &cfg)].push_back(&v.as_object());
  }
  return out;
}
std::string param_sources(const Instance &i, const Config &cfg) {
  std::set<std::string> out;
  for (const J &v : i.data.at("source_conjuncts").as_array()) {
    cfg.check("param_inventory");
    const O &r = v.as_object();
    std::vector<std::string> parts{s(r, "source_formula_id"),
                                   field(n(r, "source_node_id"))};
    for (const J &b : r.at("bindings").as_array()) {
      cfg.check("param_inventory");
      parts.push_back(field(n(b.as_object(), "binder_id")));
    }
    out.insert(join(parts));
  }
  return join({out.begin(), out.end()});
}
[[noreturn]] void param_decline(const char *reason) {
  decline(FailureCause::applicability, "param_schema", reason);
}
struct ParamDomain {
  std::set<int> constants;
  std::map<std::string, std::set<std::string>> features;
};
template <class T> bool param_equal(const T &a, const T &b, const Config &cfg) {
  if (a.size() != b.size())
    return false;
  auto right = b.begin();
  for (const auto &left : a) {
    cfg.check("param_domain");
    if (left != *right++)
      return false;
  }
  return true;
}
ParamDomain param_domain(const Instance &i, const FoldInventory &inventory,
                         const std::vector<int> &members, const Config &cfg) {
  ParamDomain out;
  std::map<std::string, std::set<int>> domains;
  for (const char *kind : {"inputs", "outputs"})
    for (const J &v : i.data.at(kind).as_array()) {
      cfg.check("param_domain");
      const O &r = v.as_object();
      if (s(r, "index_role") == "representation-bit")
        param_decline("param_encoding");
      if (s(r, "index_role") == "element")
        domains[s(r, "declaration_id")].insert(
            ints(r.at("index_tuple").as_array()).at(0));
    }
  for (const auto &[family, monitors] : inventory) {
    cfg.check("param_domain");
    std::set<int> domain;
    std::optional<std::set<std::string>> expected;
    for (const O *m : monitors) {
      cfg.check("param_domain");
      const O &o = m->at("source_origin").as_object();
      auto bound = ints(o.at("index_tuple").as_array());
      if (bound.size() > 1)
        param_decline("param_ordered_domain");
      if (!bound.empty() && !domain.insert(bound[0]).second)
        param_decline("param_monitor_inventory");
      std::map<std::string, std::set<int>> refs;
      std::set<std::string> features;
      for (const J &v : o.at("signal_refs").as_array()) {
        cfg.check("param_domain");
        const O &r = v.as_object();
        auto coords = ints(r.at("index_tuple").as_array());
        if (s(r, "index_role") == "scalar")
          features.insert(key({s(r, "declaration_id"), "scalar"}));
        else if (s(r, "index_role") != "element" || coords.size() != 1)
          param_decline("param_encoding");
        else
          refs[s(r, "declaration_id")].insert(coords[0]);
      }
      for (const auto &[id, coords] : refs) {
        cfg.check("param_domain");
        bool whole = bound.empty() && coords.size() > 1 &&
                     param_equal(coords, domains.at(id), cfg);
        if (whole) {
          features.insert(key({id, "count0"}));
          features.insert(key({id, "count01"}));
        } else
          for (int c : coords) {
            cfg.check("param_domain");
            if (!bound.empty() && c == bound[0])
              features.insert(key({id, "owner"}));
            else {
              features.insert(key({id, "constant", field(c)}));
              out.constants.insert(c);
            }
          }
      }
      if (expected) {
        if (!param_equal(*expected, features, cfg))
          param_decline("param_ordered_domain");
      } else
        expected = std::move(features);
    }
    if (!domain.empty()) {
      std::set<int> omitted;
      for (int c : members) {
        cfg.check("param_domain");
        omitted.insert(c);
      }
      for (int c : domain) {
        cfg.check("param_domain");
        if (!omitted.erase(c))
          param_decline("param_ordered_domain");
      }
      // Only whole element domains with fixed exclusions; no ordered pairs,
      // prefixes, suffixes, or moving endpoints in this first slice.
      for (int c : omitted) {
        cfg.check("param_domain");
        out.constants.insert(c);
        expected->insert(key({"excluded", field(c)}));
      }
    }
    out.features[family] = std::move(*expected);
  }
  return out;
}
// Ineligible declines retain their historical trace, without entering route B.
bool param_support(const Instance &target, const Config &config,
                   SeedDeclines log) {
  log.at("param");
  try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    Config cfg = config;
    if (lift_test_param_activation)
      lift_test_param_activation(&cfg.o);
#else
    const Config &cfg = config;
#endif
    for (const J &v : target.data.at("monitors").as_array()) {
      cfg.check("param_discovery");
      const O &m = v.as_object();
      if (m.at("source_origin").as_object().at("bindings").as_array().empty() &&
          s(m, "arity_kind") == "bus_wide" &&
          monitor_indices(m, &cfg).size() > 1 &&
          !symmetric_key(m, target, &cfg))
        return true;
    }
    return false;
  } catch (const Failure &e) {
    log.failure(e);
    throw;
  } catch (const std::bad_alloc &) {
    log.exception("param_discovery", "resource", "host allocation failed");
    throw;
  }
}
std::map<std::string, std::set<int64_t>>
param_state_counts(const FoldInventory &inventory, const Config &cfg) {
  std::map<std::string, std::set<int64_t>> counts;
  for (const auto &[family, monitors] : inventory)
    for (const O *m : monitors) {
      cfg.check("param_inventory");
      counts[family].insert(n(*m, "state_count"));
    }
  return counts;
}
Window select_param(const Instance &target, const std::string &axis,
                    const std::vector<std::pair<int, Instance *>> &probes,
                    const Config &cfg, SeedDeclines log) {
  log.at(axis, 0, 0, ":param");
  try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 22)
      throw std::bad_alloc();
    if (lift_test_fault == 14)
      param_decline("param_state_growth");
    if (lift_test_fault == 15)
      param_decline("param_ordered_domain");
#endif
    if (s(target.data, "semantics") != "exact")
      param_decline("param_semantics");
    const auto ti = param_inventory(target, cfg);
    const auto target_counts = param_state_counts(ti, cfg);
    const auto sources = param_sources(target, cfg);
    std::optional<ParamDomain> td;
    Window w;
    w.axis = axis;
    w.fold = w.param = true;
    for (const auto &[size, seed] : probes) {
      cfg.check("param_discovery");
      if (param_sources(*seed, cfg) != sources)
        continue; // Singleton expansion can change the source occurrence set.
      auto si = param_inventory(*seed, cfg);
      if (si.size() != ti.size())
        continue;
      bool same_keys = true;
      const auto seed_counts = param_state_counts(si, cfg);
      for (const auto &[family, monitors] : ti) {
        cfg.check("param_inventory");
        if (!si.count(family)) {
          same_keys = false;
          break;
        }
        const auto &counts = target_counts.at(family);
        if (counts.size() != 1 || seed_counts.at(family) != counts)
          param_decline("param_state_growth");
      }
      if (!same_keys)
        continue;
      bool growing_support = false;
      for (const auto &[family, monitors] : ti)
        for (const O *m : monitors) {
          cfg.check("param_inventory");
          if (m->at("source_origin")
                  .as_object()
                  .at("bindings")
                  .as_array()
                  .empty())
            growing_support |=
                monitor_indices(*m, &cfg).size() >
                monitor_indices(*si.at(family).front(), &cfg).size();
        }
      if (!growing_support)
        continue;
      auto coords = axis_members(target, *seed, &cfg);
      if (!td)
        td = param_domain(target, ti, coords.first, cfg);
      const auto sd = param_domain(*seed, si, coords.second, cfg);
      bool same_domain = param_equal(td->constants, sd.constants, cfg) &&
                         td->features.size() == sd.features.size();
      for (const auto &[family, features] : td->features) {
        cfg.check("param_domain");
        auto actual = sd.features.find(family);
        if (!same_domain || actual == sd.features.end() ||
            !param_equal(features, actual->second, cfg)) {
          same_domain = false;
          break;
        }
      }
      if (!same_domain)
        continue;
      if (coords.second.size() <= td->constants.size() + 1)
        continue; // Leave a fold witness even when a nonconstant goal owns one.
      w.target_members = coords.first;
      w.sizes.push_back(size);
      if (w.sizes.size() == 3)
        return w;
    }
    param_decline("param_insufficient_seeds");
  } catch (const Failure &e) {
    log.failure(e);
    throw;
  } catch (const std::bad_alloc &) {
    log.note("param_discovery_failed");
    log.exception("param_discovery", "resource", "host allocation failed");
    throw;
  }
}

// A budgeted heuristic, not a cutoff: plateau witnesses (e.g. 5/6/7) or
// different-width witnesses with the same relative profile (e.g. 4/8).
// shortcut: probe only 3..9; extend when other strata justify their solve cost.
Window discover_fold(const uint8_t *source, size_t size, const Instance &target,
                     const std::string &axis, const Config &cfg,
                     FoldProbes &budget, SeedDeclines log,
                     uint64_t *reductions = nullptr,
                     uint64_t *total_probes = nullptr) {
  log.at(axis, 0, 0, ":fold");
  try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 10)
      throw std::bad_alloc();
#endif
    if (s(target.data, "semantics") != "exact")
      decline(FailureCause::applicability, "fold_discovery", "fold_semantics");
    auto widths = fold_widths(target, axis);
    auto profile = fold_profile(widths);
    auto inventory = fold_inventory(target);
    auto axes = parameters(target);
    std::map<std::vector<int>, Window> plateaus;
    Window crossing;
    const size_t wanted = cfg.o.seed_confirmation == 2 ? 2 : 3;
    uint32_t tried = 0;
    for (int k = 3; k <= 9 && k < axes.at(axis); k++) {
      log.at(axis, k, k, ":fold");
      cfg.check("fold_discovery");
      if (tried++ >= cfg.o.max_sizes_per_axis)
        break;
      if (budget.tried >= cfg.max_seed_probes)
        throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                      "fold_discovery", "fold_probe_budget");
      ++budget.tried;
      if (total_probes)
        ++*total_probes;
      if (cfg.stats)
        cfg.stats->seed_probes++;
      auto values = axes;
      values[axis] = k;
      auto seed = lower(source, size, values, TLSF_GR1_EXACT, cfg, true);
      ++budget.reductions;
      if (reductions)
        ++*reductions;
      char hash[65]{};
      sha256_hex(seed->r.aag, seed->r.aag_size, hash);
      auto metadata = j::parse(std::string_view(seed->r.metadata_json,
                                                seed->r.metadata_size))
                          .as_object();
      if (s(metadata, "semantics") != "exact" ||
          s(metadata, "game_sha256") != hash ||
          s(metadata, "source_sha256") !=
              s(target.data.at("source_origin_metadata").as_object(),
                "source_sha256"))
        decline(FailureCause::error, "fold_binding", "fold_seed_binding");
      auto sw = fold_widths(*seed, axis);
      if (fold_profile(sw) != profile)
        continue;
      auto si = fold_inventory(*seed);
      if (si.size() != inventory.size() ||
          !std::equal(
              si.begin(), si.end(), inventory.begin(),
              [](const auto &a, const auto &b) { return a.first == b.first; }))
        decline(FailureCause::applicability, "fold_discovery",
                "fold_schema_mismatch");
      // Distinct widths need not have consecutive parameter values.
      bool unequal = std::any_of(profile.begin(), profile.end(),
                                 [](int w) { return w != 0; });
      Window &w = unequal ? crossing : plateaus[sw];
      if (unequal && !w.seeds.empty() &&
          fold_widths(*w.seeds.back(), axis) == sw)
        continue;
      w.axis = axis;
      w.fold = true;
      w.sizes.push_back(k);
      w.seeds.push_back(std::move(seed));
      if (w.seeds.size() >= (unequal ? 2 : wanted)) {
        w.fold_probes = budget.tried;
        w.fold_reductions = budget.reductions;
        return std::move(w);
      }
    }
    for (auto &[_, w] : plateaus)
      if (w.seeds.size() >= 2) {
        w.fold_probes = budget.tried;
        w.fold_reductions = budget.reductions;
        return std::move(w);
      }
    decline(FailureCause::applicability, "fold_discovery",
            "fold_insufficient_strata");
  } catch (const Failure &e) {
    log.failure(e);
    throw;
  } catch (const std::bad_alloc &) {
    log.note("fold_discovery_failed");
    log.exception("fold_discovery", "resource", "host allocation failed");
    throw;
  } catch (const std::exception &e) {
    log.note("fold_discovery_failed");
    log.exception("fold_discovery", "error", e.what());
    throw;
  }
}

// Recreate probes only after legacy/encoded discovery has released its state.
using ParamProbes = std::vector<std::pair<int, std::unique_ptr<Instance>>>;
Window discover_param(const uint8_t *source, size_t size,
                      const Instance &target,
                      TlsfGr1ReductionSemantics semantics, const Config &cfg,
                      FoldProbes &budget, SeedDeclines log,
                      uint64_t *reductions = nullptr,
                      uint64_t *total_probes = nullptr,
                      const std::string &cached_axis = {},
                      ParamProbes *cached = nullptr) {
  log.at("param");
  try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 26)
      throw std::bad_alloc();
#endif
    const auto values = parameters(target);
    for (const auto &axis : fold_axes(target, cfg, log, false)) {
      ParamProbes probes;
      const bool reuse = cached && axis == cached_axis;
      for (int k = 1; k < values.at(axis) && k <= int(cfg.o.max_sizes_per_axis);
           k++) {
        log.at(axis, k, k, ":param");
        try {
          cfg.check("param_discovery");
          if (budget.tried >= cfg.max_seed_probes)
            throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                          "param_discovery", "probe_budget_exhausted");
          ++budget.tried;
          if (reuse) {
            for (auto &[size, seed] : *cached)
              if (size == k) {
                probes.emplace_back(k, std::move(seed));
                ++budget.reductions;
                break;
              }
            continue; // Missing cached sizes already failed legacy lowering.
          }
          if (total_probes)
            ++*total_probes;
          if (cfg.stats)
            cfg.stats->seed_probes++;
          auto overrides = values;
          overrides[axis] = k;
          auto seed = lower(source, size, overrides, semantics, cfg);
          if (reductions)
            ++*reductions;
          seed->members = axis_members(target, *seed, &cfg).second;
          ++budget.reductions;
          probes.emplace_back(k, std::move(seed));
        } catch (const Failure &e) {
          log.failure(e);
          if (!is_applicability(e.cause))
            throw;
        }
      }
      try {
        std::vector<std::pair<int, Instance *>> views;
        for (auto &[k, seed] : probes)
          views.emplace_back(k, seed.get());
        auto window = select_param(target, axis, views, cfg, log);
        for (int k : window.sizes)
          for (auto &[size, seed] : probes)
            if (size == k)
              window.seeds.push_back(std::move(seed));
        window.fold_probes = budget.tried;
        window.fold_reductions = budget.reductions;
        return window;
      } catch (const Failure &e) {
        if (!is_applicability(e.cause))
          throw;
      }
    }
    cfg.decline_search("seed_window", "no stable index axis");
  } catch (const std::bad_alloc &) {
    log.exception("param_discovery", "resource", "host allocation failed");
    throw;
  }
}

Window discover(const uint8_t *source, size_t size, const Instance &target,
                TlsfGr1ReductionSemantics semantics, const Config &cfg,
                SeedDeclines log) try {
  auto axes = parameters(target);
  if (axes.empty())
    decline(FailureCause::applicability, "parameters", "absent");
  uint64_t probes_tried = 0;
  bool param_activation = false;
  std::exception_ptr legacy_shape_failure;
  try {
    for (const auto &axis : fold_axes(target, cfg, log, false, true)) {
      const auto value = axes.at(axis);
      log.at(axis);
      struct Probe {
        int size;
        std::unique_ptr<Instance> inst;
      };
      std::vector<Probe> probes;
      for (int k = 1; k < value && k <= int(cfg.o.max_sizes_per_axis); k++) {
        log.at(axis, k, k);
        try {
          cfg.check("seed_window");
          if (probes_tried >= cfg.max_seed_probes)
            throw Failure(
                TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "seed_window",
                "probe_budget_exhausted: fixed seed probe budget exhausted");
          ++probes_tried;
          if (cfg.stats)
            cfg.stats->seed_probes++;
          auto values = axes;
          values[axis] = k;
          auto probe = lower(source, size, values, semantics, cfg);
          auto coords = axis_members(target, *probe);
          probe->members = std::move(coords.second);
          probes.push_back({k, std::move(probe)});
        } catch (const Failure &e) {
          log.failure(e);
          if (e.status == TLSF_GR1_LIFT_DEADLINE ||
              e.status == TLSF_GR1_LIFT_CANCELLED ||
              e.status == TLSF_GR1_LIFT_LIMIT)
            throw;
          cfg.note_failure(e);
        }
      }
      log.at(axis);
      Modes modes = target_modes(target);
      std::string target_shape;
      std::exception_ptr shape_failure;
      try {
        target_shape = structural_shape(target, modes, cfg);
      } catch (const Failure &e) {
        log.failure(e);
        if (e.stage != "bus_schema")
          throw;
        shape_failure = std::current_exception();
        param_activation = true;
      }
      if (probes.size() < 2)
        log.note("insufficient_sizes");
      for (size_t p = 1; !shape_failure && p < probes.size(); p++) {
        log.at(axis, probes[p - 1].size, probes[p].size);
        if (probes[p].size != probes[p - 1].size + 1) {
          log.note("nonconsecutive_sizes");
          continue;
        }
        try {
          Instance &left = *probes[p - 1].inst, &right = *probes[p].inst;
          if (structural_shape(left, modes, cfg) != target_shape ||
              structural_shape(right, modes, cfg) != target_shape) {
            log.note("structural_shape_mismatch");
            param_activation = true;
            continue;
          }
          auto coords = axis_members(target, left);
          auto target_members = std::move(coords.first);
          if (left.members.size() >= right.members.size()) {
            log.note("members_not_growing");
            continue;
          }
          if (right.members.size() >= target_members.size()) {
            log.note("target_not_larger");
            continue;
          }
          std::vector<size_t> selected{p - 1, p};
          if (cfg.o.seed_confirmation != 2 && p + 1 < probes.size() &&
              probes[p + 1].size == probes[p].size + 1) {
            log.at(axis, probes[p - 1].size, probes[p + 1].size);
            if (structural_shape(*probes[p + 1].inst, modes, cfg) !=
                target_shape) {
              log.note("structural_shape_mismatch");
              continue;
            }
            selected.push_back(p + 1);
          }
          auto classes = [&](Instance &i) {
            Roles roles = role_signatures(i, modes, cfg);
            std::set<std::string> x;
            for (const auto &[index, signature] : roles)
              x.insert(signature);
            return x;
          };
          auto expected = classes(left);
          bool stable = true;
          for (size_t pos : selected)
            stable &= classes(*probes[pos].inst) == expected;
          if (!stable) {
            log.note("unstable_role_classes");
            continue;
          }
          (void)role_signatures(target, modes, cfg, &target_members);
          Window result;
          result.axis = axis;
          result.modes = modes;
          result.target_members = std::move(target_members);
          for (size_t pos : selected) {
            result.sizes.push_back(probes[pos].size);
            result.seeds.push_back(std::move(probes[pos].inst));
          }
          return result;
        } catch (const Failure &e) {
          log.failure(e);
          if (e.status == TLSF_GR1_LIFT_DEADLINE ||
              e.status == TLSF_GR1_LIFT_CANCELLED ||
              e.status == TLSF_GR1_LIFT_LIMIT)
            throw;
          cfg.note_failure(e);
        }
      }
      if (shape_failure) {
        legacy_shape_failure = shape_failure;
        break;
      }
    }
  } catch (const Failure &e) {
    if (!legacy_probe_limit(e))
      throw;
    legacy_shape_failure = std::current_exception();
    try {
      (void)structural_shape(target, target_modes(target), cfg);
    } catch (const Failure &shape) {
      if (shape.stage != "bus_schema")
        throw;
      param_activation = true;
    }
  }
  // A/B share a fresh max_seed_probes allowance, while the arm's deadline/RSS
  // and the public totals still cover all actual work.
  FoldProbes budget;
  for (const auto &axis : fold_axes(target, cfg, log, true)) {
    try {
      return discover_fold(source, size, target, axis, cfg, budget, log);
    } catch (const Failure &e) {
      if (!is_applicability(e.cause))
        throw;
    }
  }
  if (param_activation && param_support(target, cfg, log)) {
    try {
      return discover_param(source, size, target, semantics, cfg, budget, log);
    } catch (const Failure &e) {
      if (!is_applicability(e.cause))
        throw;
    }
  }
  if (legacy_shape_failure)
    std::rethrow_exception(legacy_shape_failure);
  cfg.decline_search("seed_window", "no stable index axis");
} catch (const std::bad_alloc &) {
  log.exception("allocation", "resource", "host allocation failed");
  throw;
} catch (const Failure &) {
  throw;
} catch (const std::exception &e) {
  log.exception("internal", "error", e.what());
  throw;
} catch (...) {
  log.exception("internal", "error", "unknown exception");
  throw;
}

struct SharedSeeds {
  struct Entry {
    std::unique_ptr<Instance> instance;
    std::string key;
  };
  std::string axis;
  std::map<int, Entry> entries;
  std::vector<int> real_sizes, env_sizes, target_members;
  Modes modes;
  bool fold = false;
  bool param = false;
  bool param_pending = false;
  uint64_t fold_probes = 0, fold_reductions = 0;
};

SharedSeeds shared_window(Window window, const TrustedTarget &trusted) {
  SharedSeeds found;
  found.axis = window.axis;
  found.fold_probes = window.fold_probes;
  found.fold_reductions = window.fold_reductions;
  found.fold = window.fold;
  found.param = window.param;
  found.real_sizes = window.sizes;
  found.target_members = window.target_members;
  for (size_t p = 0; p < window.sizes.size(); p++) {
    auto &seed = window.seeds[p];
    char hash[65]{};
    sha256_hex(seed->r.aag, seed->r.aag_size, hash);
    found.entries.emplace(
        window.sizes[p],
        SharedSeeds::Entry{std::move(seed),
                           key({trusted.source_hash, found.axis, hash})});
  }
  return found;
}

SharedSeeds discover_shared(const TrustedTarget &trusted, const Config &cfg,
                            TlsfGr1BothResult &out, bool disable_real_lift,
                            SeedDeclines log) try {
  BothPhase phase("native_r_discovery");
  const Instance &target = *trusted.instance;
  auto axes = parameters(target);
  if (axes.empty()) {
    log.note("absent");
    return {};
  }
  bool param_activation = false;
  std::exception_ptr legacy_probe_failure;
  try {
    for (const auto &axis : fold_axes(target, cfg, log, false, true)) {
      const auto value = axes.at(axis);
      log.at(axis);
      if (value <= 1) {
        log.note("insufficient_sizes");
        continue;
      }
      SharedSeeds found;
      found.axis = axis;
      found.modes = target_modes(target);
      const int last = std::min<int>(value - 1, cfg.o.max_sizes_per_axis);
      for (int k = 1; k <= last; k++) {
        log.at(axis, k, k);
        try {
          cfg.check("seed_window");
          if (out.seed_probes >= cfg.max_seed_probes)
            throw Failure(
                TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "seed_window",
                "probe_budget_exhausted: fixed seed probe budget exhausted");
          out.seed_probes++;
          auto values = axes;
          values[axis] = k;
          auto probe =
              lower((const uint8_t *)trusted.snapshot.data(),
                    trusted.snapshot.size(), values, TLSF_GR1_EXACT, cfg);
          out.seed_reductions++;
          char hash[65]{};
          sha256_hex(probe->r.aag, probe->r.aag_size, hash);
          auto metadata = j::parse(std::string_view(probe->r.metadata_json,
                                                    probe->r.metadata_size))
                              .as_object();
          if (s(metadata, "semantics") != "exact" ||
              s(metadata, "source_sha256") != trusted.source_hash ||
              s(metadata, "game_sha256") != hash)
            decline(FailureCause::error, "seed_binding",
                    "seed reduction hash differs");
          auto members = axis_members(target, *probe);
          probe->members = std::move(members.second);
          std::vector<std::string> parts{trusted.source_hash, axis, field(k),
                                         "exact", hash};
          for (const auto &[name, number] : axes)
            if (name != axis) {
              parts.push_back(name);
              parts.push_back(field(number));
            }
          found.entries.emplace(
              k, SharedSeeds::Entry{std::move(probe), join(parts)});
        } catch (const Failure &e) {
          log.failure(e);
          if (e.status == TLSF_GR1_LIFT_DEADLINE ||
              e.status == TLSF_GR1_LIFT_CANCELLED ||
              e.status == TLSF_GR1_LIFT_LIMIT)
            throw;
          cfg.note_failure(e);
        }
      }
      if (!disable_real_lift) {
        log.at(axis);
        try {
          const auto shape = structural_shape(target, found.modes, cfg);
          if (last < 2)
            log.note("insufficient_sizes");
          for (int k = 1; k + 1 <= last; k++) {
            log.at(axis, k, k + 1);
            auto left = found.entries.find(k),
                 right = found.entries.find(k + 1);
            if (left == found.entries.end() || right == found.entries.end()) {
              log.note("probe_unavailable");
              continue;
            }
            auto &a = *left->second.instance, &b = *right->second.instance;
            if (structural_shape(a, found.modes, cfg) != shape ||
                structural_shape(b, found.modes, cfg) != shape) {
              param_activation = true;
              log.note("structural_shape_mismatch");
              continue;
            }
            if (a.members.size() >= b.members.size()) {
              log.note("members_not_growing");
              continue;
            }
            auto coords = axis_members(target, a);
            if (b.members.size() >= coords.first.size()) {
              log.note("target_not_larger");
              continue;
            }
            std::vector<int> sizes{k, k + 1};
            if (cfg.o.seed_confirmation != 2 && k + 2 <= last &&
                found.entries.count(k + 2)) {
              log.at(axis, k, k + 2);
              if (structural_shape(*found.entries.at(k + 2).instance,
                                   found.modes, cfg) != shape) {
                log.note("structural_shape_mismatch");
                continue;
              }
              sizes.push_back(k + 2);
            }
            std::set<std::string> expected;
            bool stable = true;
            for (int size : sizes) {
              auto roles = role_signatures(*found.entries.at(size).instance,
                                           found.modes, cfg);
              std::set<std::string> signatures;
              for (const auto &[_, signature] : roles)
                signatures.insert(signature);
              if (expected.empty())
                expected = signatures;
              else if (expected != signatures)
                stable = false;
            }
            if (!stable) {
              log.note("unstable_role_classes");
              continue;
            }
            (void)role_signatures(target, found.modes, cfg, &coords.first);
            found.real_sizes = std::move(sizes);
            found.target_members = std::move(coords.first);
            break;
          }
        } catch (const Failure &e) {
          param_activation |= e.stage == "bus_schema";
          log.failure(e);
          if (e.status == TLSF_GR1_LIFT_DEADLINE ||
              e.status == TLSF_GR1_LIFT_CANCELLED ||
              e.status == TLSF_GR1_LIFT_LIMIT)
            throw;
          cfg.note_failure(e);
        }
      }
      if (!cfg.o.disable_env_lift && value > 5 && found.entries.count(3) &&
          found.entries.count(4) && found.entries.count(5)) {
        log.at(axis, 3, 5, ":U");
        try {
          env_typed_axis(target, axis);
          const auto classes = env_typed_classes(*found.entries.at(3).instance);
          std::vector<int> target_members;
          bool stable = true;
          for (int size : {3, 4, 5}) {
            auto &seed = *found.entries.at(size).instance;
            env_typed_axis(seed, axis);
            auto coords = axis_members(target, seed);
            if (seed.members.size() != size_t(size)) {
              log.note("member_counts");
              stable = false;
            } else if (coords.first.size() <= seed.members.size()) {
              log.note("target_not_larger");
              stable = false;
            } else if (env_typed_classes(seed) != classes) {
              log.note("unstable_role_classes");
              stable = false;
            }
            if (target_members.empty())
              target_members = coords.first;
            else if (target_members != coords.first) {
              log.note("inconsistent_coordinates");
              stable = false;
            }
          }
          if (env_typed_classes(target) != classes) {
            log.note("unstable_role_classes");
            stable = false;
          }
          if (stable) {
            found.env_sizes = {3, 4, 5};
            if (found.target_members.empty())
              found.target_members = std::move(target_members);
          }
        } catch (const Failure &e) {
          log.failure(e);
          if (e.status == TLSF_GR1_LIFT_DEADLINE ||
              e.status == TLSF_GR1_LIFT_CANCELLED ||
              e.status == TLSF_GR1_LIFT_LIMIT)
            throw;
          cfg.note_failure(e);
        }
      } else if (!cfg.o.disable_env_lift) {
        log.at(axis, 3, 5, ":U");
        log.note(value <= 5 ? "insufficient_sizes" : "probe_unavailable");
      }
      if (!found.real_sizes.empty() || !found.env_sizes.empty()) {
        found.param_pending = !disable_real_lift && param_activation;
        return found;
      }
    }
  } catch (const Failure &e) {
    if (!legacy_probe_limit(e) || disable_real_lift)
      throw;
    legacy_probe_failure = std::current_exception();
    try {
      (void)structural_shape(target, target_modes(target), cfg);
    } catch (const Failure &shape) {
      if (shape.stage != "bus_schema")
        throw;
      param_activation = true;
    }
  }
  // Same independent fold allowance as standalone discovery; totals include
  // legacy work, but only canonical fallback probes spend this allowance.
  FoldProbes budget;
  if (!disable_real_lift)
    for (const auto &axis : fold_axes(target, cfg, log, true)) {
      Window window;
      try {
        window =
            discover_fold((const uint8_t *)trusted.snapshot.data(),
                          trusted.snapshot.size(), target, axis, cfg, budget,
                          log, &out.seed_reductions, &out.seed_probes);
      } catch (const Failure &e) {
        if (!is_applicability(e.cause))
          throw;
        continue;
      }
      return shared_window(std::move(window), trusted);
    }
  if (param_activation && param_support(target, cfg, log)) {
    try {
      return shared_window(
          discover_param((const uint8_t *)trusted.snapshot.data(),
                         trusted.snapshot.size(), target, TLSF_GR1_EXACT, cfg,
                         budget, log, &out.seed_reductions, &out.seed_probes),
          trusted);
    } catch (const Failure &e) {
      if (!is_applicability(e.cause))
        throw;
    }
  }
  if (legacy_probe_failure)
    std::rethrow_exception(legacy_probe_failure);
  if (cfg.search_cause)
    cfg.decline_search("seed_window", "no stable index axis");
  return {};
} catch (const std::bad_alloc &) {
  log.exception("allocation", "resource", "host allocation failed");
  throw;
} catch (const Failure &) {
  throw;
} catch (const std::exception &e) {
  log.exception("internal", "error", e.what());
  throw;
} catch (...) {
  log.exception("internal", "error", "unknown exception");
  throw;
}
// Cooperate with the arm's live RSS/deadline budget inside C solver/checker
// loops; exceptions must not unwind through their cancellation callbacks.
struct FoldBudget {
  const Config &cfg;
  std::exception_ptr failure;
  static int cancelled(void *raw) noexcept {
    auto &self = *static_cast<FoldBudget *>(raw);
    try {
      self.cfg.check("fold_budget");
      return 0;
    } catch (...) {
      self.failure = std::current_exception();
      return 1;
    }
  }
  void finish() const {
    if (failure)
      std::rethrow_exception(failure);
    cfg.check("fold_budget");
  }
};
void solve_seed(Instance &i, const Config &cfg, bool fold) {
  cfg.check("seed_solve");
  char reason[256]{};
  if (!tlsf_gr1_validate_game(i.r.game, reason, sizeof reason))
    decline(FailureCause::error, "seed_solve", reason);
  auto copy = parse_aig(i.r.aag, i.r.aag_size);
  OxiddFailure failure{};
  char *cert = nullptr, *meta = nullptr;
  size_t cert_size = 0, meta_size = 0;
  Gr1CertificateOptions export_options{};
  export_options.semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
  export_options.aag_bytes = &cert;
  export_options.aag_size = &cert_size;
  export_options.json_bytes = &meta;
  export_options.json_size = &meta_size;
  export_options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  Gr1SolveOptions options{};
  options.oxidd = oxidd_solve_options_default();
  options.oxidd.node_cap = cfg.o.solver_nodes;
  options.oxidd.cache_cap = cfg.o.solver_cache;
  options.oxidd.deadline_mono_ns = cfg.o.deadline_mono_ns;
  options.oxidd.cancelled = cfg.o.cancelled;
  options.oxidd.cancel_ctx = cfg.o.cancel_ctx;
  options.oxidd.max_artifact_bytes = cfg.o.max_artifact_bytes;
  options.oxidd.failure = &failure;
  options.certificate = &export_options;
  FoldBudget budget{cfg, {}};
  if (fold) {
    options.oxidd.deadline_mono_ns = cfg.effective_deadline();
    options.oxidd.cancelled = FoldBudget::cancelled;
    options.oxidd.cancel_ctx = &budget;
  }
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd(copy.release(), &unreal, &options);
  aig_free(strategy);
  std::unique_ptr<char, decltype(&free)> cert_guard(cert, &free),
      meta_guard(meta, &free);
  if (fold)
    budget.finish();
  if (!strategy || unreal || export_options.failed || !cert || !meta) {
    if (failure.kind == OXIDD_FAILURE_DEADLINE)
      throw Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline,
                    "seed_solve", "deadline exceeded");
    if (failure.kind == OXIDD_FAILURE_CANCELLED)
      throw Failure(TLSF_GR1_LIFT_CANCELLED, FailureCause::cancelled,
                    "seed_solve", "cancelled");
    if (failure.kind == OXIDD_FAILURE_BDD ||
        failure.kind == OXIDD_FAILURE_ARTIFACT_LIMIT ||
        failure.kind == OXIDD_FAILURE_HOST)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "seed_solve",
                    "solver capacity exhausted");
    decline(unreal ? FailureCause::applicability : FailureCause::error,
            unreal ? "seed_solve" : "seed_error", "no system certificate");
  }
  cfg.bytes(cert_size, "seed_solve");
  cfg.bytes(meta_size, "seed_solve");
  i.cert_aag.assign(cert, cert_size);
  i.cert_json.assign(meta, meta_size);
  i.cert_meta = j::parse(i.cert_json).as_object();
  if (s(i.cert_meta, "status") != "realizable" ||
      s(i.cert_meta, "side") != "system" ||
      s(i.cert_meta, "reduction_semantics") != "exact")
    decline(FailureCause::error, "seed_metadata",
            "certificate metadata mismatch");
  i.cert = parse_aig(i.cert_aag.data(), i.cert_aag.size());
}
void solve_seed(Instance &i, const Config &cfg) { solve_seed(i, cfg, false); }

FailureCause solver_failure_cause(OxiddFailureKind kind) {
  switch (kind) {
  case OXIDD_FAILURE_BDD:
  case OXIDD_FAILURE_HOST:
  case OXIDD_FAILURE_ARTIFACT_LIMIT:
    return FailureCause::resource;
  case OXIDD_FAILURE_DEADLINE:
    return FailureCause::deadline;
  case OXIDD_FAILURE_CANCELLED:
    return FailureCause::cancelled;
  case OXIDD_FAILURE_NONE:
    return FailureCause::error;
  default:
    return FailureCause::error;
  }
}
FailureCause check_failure_cause(TlsfGr1CheckStatus status,
                                 TlsfGr1CheckVerdict verdict) {
  switch (status) {
  case TLSF_GR1_CHECK_LIMIT:
    return FailureCause::resource;
  case TLSF_GR1_CHECK_DEADLINE:
    return FailureCause::deadline;
  case TLSF_GR1_CHECK_CANCELLED:
    return FailureCause::cancelled;
  case TLSF_GR1_CHECK_OK:
    return verdict == TLSF_GR1_CHECK_CERT_FAILED ||
                   verdict == TLSF_GR1_CHECK_REFUTED
               ? FailureCause::applicability
               : FailureCause::error;
  default:
    return FailureCause::error;
  }
}
TlsfGr1SeedPolarity solve_shared_seed(Instance &seed, const Config &cfg,
                                      TlsfGr1BothResult &out, bool fold) {
  char artifact[65]{};
  if (phase_observer && phase_observer->phase)
    sha256_hex(seed.r.aag, seed.r.aag_size, artifact);
  BothPhase phase("native_seed_solve", artifact);
  cfg.check("seed_solve");
  char reason[256]{};
  if (!tlsf_gr1_validate_game(seed.r.game, reason, sizeof reason))
    decline(FailureCause::error, "seed_solve", reason);
  auto game = parse_aig(seed.r.aag, seed.r.aag_size);
  OxiddFailure failure{};
  char *cert = nullptr, *meta = nullptr, *policy = nullptr,
       *policy_meta = nullptr;
  size_t cert_size = 0, meta_size = 0, policy_size = 0, policy_meta_size = 0;
  Gr1CertificateOptions export_options{};
  export_options.semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
  export_options.aag_bytes = &cert;
  export_options.aag_size = &cert_size;
  export_options.json_bytes = &meta;
  export_options.json_size = &meta_size;
  export_options.policy_aag_bytes = &policy;
  export_options.policy_aag_size = &policy_size;
  export_options.policy_json_bytes = &policy_meta;
  export_options.policy_json_size = &policy_meta_size;
  export_options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  Gr1SolveOptions options{};
  options.oxidd = oxidd_solve_options_default();
  options.oxidd.node_cap = cfg.o.solver_nodes;
  options.oxidd.cache_cap = cfg.o.solver_cache;
  options.oxidd.deadline_mono_ns = cfg.o.deadline_mono_ns;
  options.oxidd.cancelled = cfg.o.cancelled;
  options.oxidd.cancel_ctx = cfg.o.cancel_ctx;
  options.oxidd.max_artifact_bytes = cfg.o.max_artifact_bytes;
  options.oxidd.failure = &failure;
  options.certificate = &export_options;
  FoldBudget budget{cfg, {}};
  if (fold) {
    options.oxidd.deadline_mono_ns = cfg.effective_deadline();
    options.oxidd.cancelled = FoldBudget::cancelled;
    options.oxidd.cancel_ctx = &budget;
  }
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd(game.release(), &unreal, &options);
  const bool real = strategy && !unreal;
  aig_free(strategy);
  out.seed_solves++;
  std::unique_ptr<char, decltype(&free)> cert_owner(cert, &free),
      meta_owner(meta, &free), policy_owner(policy, &free),
      policy_meta_owner(policy_meta, &free);
  if (fold)
    budget.finish();
  if (failure.kind == OXIDD_FAILURE_DEADLINE)
    throw Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline, "seed_solve",
                  "deadline exceeded");
  cfg.check("seed_solve");
  if (failure.kind != OXIDD_FAILURE_NONE || export_options.failed ||
      (!real && !unreal) || !cert || !meta ||
      (unreal && (!policy || !policy_meta)))
    throw Failure(TLSF_GR1_LIFT_DECLINED, solver_failure_cause(failure.kind),
                  "seed_solve", "exact seed certificate unavailable");
  for (size_t count : {cert_size, meta_size, policy_size, policy_meta_size})
    cfg.bytes(count, "seed_solve");
  seed.cert_aag.assign(cert, cert_size);
  seed.cert_json.assign(meta, meta_size);
  if (unreal) {
    seed.env_policy_aag.assign(policy, policy_size);
    seed.env_policy_json.assign(policy_meta, policy_meta_size);
  }
  seed.cert_meta = j::parse(seed.cert_json).as_object();
  if (s(seed.cert_meta, "reduction_semantics") != "exact" ||
      s(seed.cert_meta, "side") != (real ? "system" : "environment") ||
      s(seed.cert_meta, "status") != (real ? "realizable" : "unrealizable"))
    decline(FailureCause::error, "seed_metadata",
            "seed certificate metadata mismatch");
  phase.finish();
  BothPhase check_phase("native_seed_check", artifact);
  TlsfGr1CheckInput input{};
  input.game_aag = {(const uint8_t *)seed.r.aag, seed.r.aag_size};
  input.certificate_aag = {(const uint8_t *)cert, cert_size};
  input.certificate_json = {(const uint8_t *)meta, meta_size};
  if (unreal) {
    input.policy_aag = {(const uint8_t *)policy, policy_size};
    input.policy_json = {(const uint8_t *)policy_meta, policy_meta_size};
  }
  TlsfGr1CheckOptions check_options{};
  check_options.method =
      real ? TLSF_GR1_CHECK_REGION : TLSF_GR1_CHECK_CERTIFICATE;
  check_options.node_cap = cfg.o.checker_nodes;
  check_options.cache_cap = cfg.o.checker_cache;
  check_options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  check_options.deadline_mono_ns = cfg.o.deadline_mono_ns;
  check_options.cancelled = cfg.o.cancelled;
  check_options.cancel_ctx = cfg.o.cancel_ctx;
  if (fold) {
    check_options.deadline_mono_ns = cfg.effective_deadline();
    check_options.cancelled = FoldBudget::cancelled;
    check_options.cancel_ctx = &budget;
  }
  TlsfGr1CheckResult checked{};
  out.seed_checks++;
  auto status = tlsf_gr1_check(&input, &check_options, &checked);
  const auto verdict = checked.verdict;
  bool verified = status == TLSF_GR1_CHECK_OK &&
                  checked.verdict == (real ? TLSF_GR1_CHECK_REGION_VERIFIED
                                           : TLSF_GR1_CHECK_VERIFIED);
  tlsf_gr1_check_result_clear(&checked);
  if (fold)
    budget.finish();
  if (status == TLSF_GR1_CHECK_DEADLINE)
    throw Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline, "seed_check",
                  "deadline exceeded");
  cfg.check("seed_check");
  if (!verified)
    throw Failure(TLSF_GR1_LIFT_DECLINED, check_failure_cause(status, verdict),
                  "seed_check", "independent seed proof rejected");
  seed.cert = parse_aig(seed.cert_aag.data(), seed.cert_aag.size());
  return real ? TLSF_GR1_SEEDS_REAL : TLSF_GR1_SEEDS_UNREAL;
}
TlsfGr1SeedPolarity solve_shared_seed(Instance &seed, const Config &cfg,
                                      TlsfGr1BothResult &out) {
  return solve_shared_seed(seed, cfg, out, false);
}
struct Variable {
  int index;
  std::string kind, prefix;
  std::vector<int> indices;
  std::set<int> owners;
};
struct Goal {
  int number, owner;
  std::string key;
};
struct GameView {
  const Instance *inst;
  Modes modes;
  Roles roles;
  std::vector<int> members;
  std::vector<Variable> variables;
  std::vector<Goal> goals;
  std::vector<bool> controls;
  std::map<std::string, int> output_by_name;
  uint32_t states, inputs, fairness;
  bool fold;
  bool param = false;
  GameView(const Instance &i, const Modes &m, const Config &cfg,
           const std::vector<int> *target_members = nullptr,
           bool monitor_fold = false)
      : inst(&i), modes(m),
        roles(monitor_fold ? Roles{}
                           : role_signatures(i, m, cfg, target_members)),
        members(target_members ? *target_members : i.members),
        states(aig_num_latches(i.r.game)), inputs(aig_num_inputs(i.r.game)),
        fairness(aig_num_fairness(i.r.game)), fold(monitor_fold) {
    if (fold) {
      (void)fold_inventory(i);
      for (uint32_t p = 0; p < states + inputs; p++)
        variables.push_back(
            {int(p), p < states ? "state" : "letter", "", {}, {}});
      std::map<uint32_t, bool> signals;
      for (const char *kind : {"inputs", "outputs"})
        for (const J &v : i.data.at(kind).as_array())
          signals[uint32_t(n(v.as_object(), "game_literal"))] =
              s(v.as_object(), "direction") == "output";
      for (uint32_t p = 0; p < inputs; p++) {
        uint32_t lit;
        aig_input_name(i.r.game, p, &lit);
        controls.push_back(signals.at(lit));
      }
      std::map<int, std::string> justice;
      for (const J &v : i.data.at("monitors").as_array()) {
        const O &r = v.as_object();
        if (s(r, "role") == "justice")
          justice.emplace(int(n(r, "justice_index")), fold_key(r));
      }
      if (justice.size() != aig_num_justice(i.r.game))
        decline(FailureCause::applicability, "fold_detection",
                "fold_goal_inventory");
      for (size_t p = 0; p < justice.size(); p++) {
        uint32_t count;
        aig_justice_at(i.r.game, p, nullptr, &count);
        if (count != 1 || !justice.count(int(p)))
          decline(FailureCause::applicability, "fold_detection",
                  "fold_goal_inventory");
        goals.push_back({int(p), -1, justice.at(int(p))});
      }
      if (i.cert) {
        if (aig_num_inputs(i.cert.get()) != variables.size() ||
            n(i.cert_meta.at("counts").as_object(), "sampling_latches") != 0)
          decline(FailureCause::applicability, "fold_detection",
                  "fold_seed_interface");
        for (uint32_t p = 0; p < variables.size(); p++) {
          const char *actual = aig_input_name(i.cert.get(), p, nullptr);
          const char *expected =
              p < states ? aig_latch_name(i.r.game, p)
                         : aig_input_name(i.r.game, p - states, nullptr);
          if (!actual || !expected || strcmp(actual, expected))
            decline(FailureCause::error, "fold_detection",
                    "fold_seed_interface");
        }
        for (uint32_t p = 0; p < aig_num_outputs(i.cert.get()); p++)
          if (const char *name = aig_output_at(i.cert.get(), p, nullptr))
            output_by_name[name] = int(p);
      }
      return;
    }
    auto &data = i.data;
    std::map<uint32_t, std::pair<const O *, size_t>> latch_records;
    for (const J &v : data.at("monitors").as_array()) {
      const O &r = v.as_object();
      const A &lits = r.at("latch_literals").as_array();
      if (!lits.empty() && lits.size() != size_t(n(r, "state_count")))
        decline(FailureCause::error, "schema_abi", "monitor inventory");
      for (size_t state = 0; state < lits.size(); state++)
        if (!latch_records
                 .emplace(uint32_t(num(lits[state])), std::make_pair(&r, state))
                 .second)
          decline(FailureCause::error, "schema_abi",
                  "duplicate monitor latch literal");
    }
    uint32_t violated = UINT32_MAX;
    if (s(data, "semantics") == "strict" &&
        !data.at("violated_latch_literal").is_null())
      violated = uint32_t(num(data.at("violated_latch_literal")));
    for (uint32_t p = 0; p < states; p++) {
      uint32_t lit = 0;
      aig_latch_at(i.r.game, p, &lit, nullptr, nullptr);
      if (lit == violated) {
        variables.push_back({int(p), "state", "strict_release", {}, {}});
        continue;
      }
      auto found = latch_records.find(lit);
      if (found == latch_records.end())
        decline(FailureCause::error, "schema_abi", "unmatched latch literal");
      const O &r = *found->second.first;
      auto indices = monitor_indices(r);
      if (monitor_is_symmetric(r, i, m))
        indices.clear();
      std::set<int> owners;
      for (int x : indices)
        if (roles.count(x))
          owners.insert(x);
      variables.push_back(
          {int(p), "state",
           key({monitor_key(r, i, m, cfg), field(found->second.second)}),
           indices, std::move(owners)});
    }
    if (latch_records.size() + (violated != UINT32_MAX) != states)
      decline(FailureCause::error, "schema_abi", "latch inventory");
    std::map<uint32_t, const O *> signals;
    for (const char *kind : {"inputs", "outputs"})
      for (const J &v : data.at(kind).as_array()) {
        const O &r = v.as_object();
        if (!signals.emplace(uint32_t(n(r, "game_literal")), &r).second)
          decline(FailureCause::error, "schema_abi", "duplicate game literal");
      }
    if (signals.size() != inputs)
      decline(FailureCause::error, "schema_abi", "signal inventory");
    for (uint32_t p = 0; p < inputs; p++) {
      uint32_t lit = 0;
      aig_input_name(i.r.game, p, &lit);
      auto it = signals.find(lit);
      if (it == signals.end())
        decline(FailureCause::error, "schema_abi", "game signal unmatched");
      const O &r = *it->second;
      if (s(r, "direction") != "input" && s(r, "direction") != "output")
        decline(FailureCause::error, "schema_abi", "invalid signal direction");
      controls.push_back(s(r, "direction") == "output");
      auto indices = ints(r.at("index_tuple").as_array());
      std::set<int> owners;
      if (s(r, "index_role") == "element")
        for (int x : indices)
          if (roles.count(x))
            owners.insert(x);
      variables.push_back({int(states + p), "letter",
                           key({s(r, "direction"), s(r, "declaration_id")}),
                           indices, std::move(owners)});
    }
    if (i.cert) {
      if (aig_num_inputs(i.cert.get()) != variables.size() ||
          n(i.cert_meta.at("counts").as_object(), "sampling_latches") != 0 ||
          n(i.cert_meta.at("counts").as_object(), "original_game_latches") !=
              states)
        decline(FailureCause::error, "schema_abi",
                "certificate input mismatch");
      for (uint32_t p = 0; p < variables.size(); p++) {
        const char *actual = aig_input_name(i.cert.get(), p, nullptr);
        const char *expected =
            p < states ? aig_latch_name(i.r.game, p)
                       : aig_input_name(i.r.game, p - states, nullptr);
        if (!actual || !expected || strcmp(actual, expected))
          decline(FailureCause::error, "schema_abi",
                  "certificate input mismatch");
      }
      for (uint32_t p = 0; p < aig_num_outputs(i.cert.get()); p++) {
        const char *name = aig_output_at(i.cert.get(), p, nullptr);
        if (name)
          output_by_name[name] = int(p);
      }
    }
    std::map<int, const O *> justice;
    for (const J &v : data.at("monitors").as_array())
      if (s(v.as_object(), "role") == "justice") {
        const O &r = v.as_object();
        if (!r.contains("justice_index") ||
            !justice.emplace(int(n(r, "justice_index")), &r).second)
          decline(FailureCause::error, "schema_abi", "duplicate justice ID");
      }
    if (s(data, "semantics") == "strict" && justice.empty() &&
        aig_num_justice(i.r.game) == 1) {
      goals.push_back({0, -1, "implicit_true_justice"});
    } else {
      if (justice.size() != aig_num_justice(i.r.game))
        decline(FailureCause::error, "schema_abi", "justice inventory");
      for (size_t p = 0; p < justice.size(); p++) {
        auto found = justice.find(int(p));
        if (found == justice.end())
          decline(FailureCause::error, "schema_abi", "missing justice ID");
        const O &r = *found->second;
        auto indices = ints(
            r.at("source_origin").as_object().at("index_tuple").as_array());
        if (indices.size() > 1)
          decline(FailureCause::applicability, "schema_abi",
                  "multi-index goal");
        int owner =
            indices.size() == 1 && roles.count(indices[0]) ? indices[0] : -1;
        std::string role = owner < 0 ? "null" : roles.at(owner);
        goals.push_back(
            {int(p), owner, key({monitor_key(r, i, m, cfg), role})});
      }
    }
    for (uint32_t goal = 0; goal < aig_num_justice(i.r.game); goal++) {
      uint32_t count = 0;
      aig_justice_at(i.r.game, goal, nullptr, &count);
      if (count != 1)
        decline(FailureCause::applicability, "schema_abi",
                "multi-member justice");
    }
  }
  int levels(const Goal &goal) const {
    return int(num(inst->cert_meta.at("counts")
                       .as_object()
                       .at("levels_per_goal")
                       .as_array()
                       .at(goal.number)));
  }
  uint32_t output(const std::string &name) const {
    if (!inst->cert || !output_by_name.count(name))
      decline(FailureCause::error, "schema_abi", "missing seed predicate");
    uint32_t lit = aig_output_lit(inst->cert.get(), name.c_str());
    if (lit == UINT32_MAX)
      decline(FailureCause::error, "schema_abi", "missing seed predicate");
    return lit;
  }
};
struct B {
  oxidd_bdd_t v{};
  B() = default;
  explicit B(oxidd_bdd_t f) : v(f) {
    if (!v._p)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                    "schema_capacity", "OxiDD allocation failed");
  }
  B(const B &other) : v(oxidd_bdd_ref(other.v)) {}
  B(B &&other) noexcept : v(other.v) { other.v = {}; }
  B &operator=(const B &other) {
    if (this != &other) {
      oxidd_bdd_unref(v);
      v = oxidd_bdd_ref(other.v);
    }
    return *this;
  }
  B &operator=(B &&other) noexcept {
    if (this != &other) {
      oxidd_bdd_unref(v);
      v = other.v;
      other.v = {};
    }
    return *this;
  }
  ~B() { oxidd_bdd_unref(v); }
};
bool same(const B &a, const B &b) { return bdd_eq(a.v, b.v); }
using Handle = std::pair<const void *, size_t>;
Handle handle(const B &v) { return {v.v._p, v.v._i}; }
class Schema {
  oxidd_bdd_manager_t manager{};
  const Config *cfg;
  size_t calls = 0;
  std::map<std::string, int> normal;
  std::map<int, std::string> reverse_normal;

public:
  Schema(const Config &config, uint32_t initial) : cfg(&config) {
    manager = tlsf_oxidd_manager_new(cfg->o.schema_nodes, cfg->o.schema_cache);
    if (!manager._p)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                    "schema_capacity", "cannot create OxiDD manager");
    grow(initial);
  }
  ~Schema() { oxidd_bdd_manager_unref(manager); }
  Schema(const Schema &) = delete;
  void set_config(const Config &config) { cfg = &config; }
  void tick(const char *stage = "schema") {
    if (cfg->max_bdd_ops && calls >= cfg->max_bdd_ops)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, stage,
                    "fixed BDD operation budget exhausted");
    if ((++calls & 127u) == 0) {
      cfg->check(stage);
      if (oxidd_bdd_manager_approx_num_inner_nodes(manager) >
          cfg->o.schema_nodes)
        throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                      "schema_capacity", "node cap exceeded");
    }
  }
  void begin_phase(const Config &config) {
    cfg = &config;
    calls = 0;
  }
  const size_t *operation_counter() const { return &calls; }
  int width() const { return int(oxidd_bdd_manager_num_vars(manager)); }
  size_t node_count() const {
    return oxidd_bdd_manager_approx_num_inner_nodes(manager);
  }
  void grow(int count) {
    if (count <= width())
      return;
    auto range = oxidd_bdd_manager_add_vars(manager, count - width());
    if (int(range.end) != count)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                    "schema_capacity", "BDD variable limit");
  }
  B t() {
    tick();
    return B(oxidd_bdd_true(manager));
  }
  B f() {
    tick();
    return B(oxidd_bdd_false(manager));
  }
  B var(int i) {
    grow(i + 1);
    tick();
    return B(oxidd_bdd_var(manager, i));
  }
  B neg(const B &a) {
    tick();
    return B(oxidd_bdd_not(a.v));
  }
  B land(const B &a, const B &b) {
    tick();
    return B(oxidd_bdd_and(a.v, b.v));
  }
  B lor(const B &a, const B &b) {
    tick();
    return B(oxidd_bdd_or(a.v, b.v));
  }
  B ite(const B &c, const B &a, const B &b) {
    tick();
    return B(oxidd_bdd_ite(c.v, a.v, b.v));
  }
  B exists(const B &a, const B &cube) {
    tick();
    return B(oxidd_bdd_exists(a.v, cube.v));
  }
  B cube(const std::set<int> &vars) {
    B x = t();
    for (int v : vars)
      x = land(x, var(v));
    return x;
  }
  int normal_var(const std::string &k) {
    auto it = normal.find(k);
    if (it != normal.end())
      return it->second;
    int index = width();
    grow(index + 1);
    normal[k] = index;
    reverse_normal[index] = k;
    return index;
  }
  const std::string &normal_key(int index) const {
    return reverse_normal.at(index);
  }
  std::set<int> support(const B &root) {
    std::set<int> vars;
    std::set<Handle> visited;
    std::function<void(const B &)> visit = [&](const B &node) {
      tick();
      if (oxidd_bdd_node_level(node.v) == (oxidd_level_no_t)-1)
        return;
      if (!visited.insert(handle(node)).second)
        return;
      vars.insert(int(oxidd_bdd_node_var(node.v)));
      B hi(oxidd_bdd_cofactor_true(node.v));
      B lo(oxidd_bdd_cofactor_false(node.v));
      visit(hi);
      visit(lo);
    };
    visit(root);
    return vars;
  }
  B relabel(const B &root, const std::map<int, int> &mapping) {
    auto supp = support(root);
    for (int v : supp)
      if (!mapping.count(v))
        decline(FailureCause::error, "schema_abi", "unmapped BDD support");
    std::map<Handle, B> memo;
    std::function<B(const B &)> visit = [&](const B &node) -> B {
      tick();
      if (oxidd_bdd_node_level(node.v) == (oxidd_level_no_t)-1)
        return node;
      auto h = handle(node);
      auto it = memo.find(h);
      if (it != memo.end())
        return it->second;
      B hi(oxidd_bdd_cofactor_true(node.v));
      B lo(oxidd_bdd_cofactor_false(node.v));
      // Preserve GCC's right-first node/variable allocation order.
      B low = visit(lo);
      B high = visit(hi);
      B variable = var(mapping.at(int(oxidd_bdd_node_var(node.v))));
      B result = ite(variable, high, low);
      memo.emplace(h, result);
      return result;
    };
    return visit(root);
  }
  B from_aig(const Aig *aig, uint32_t root, bool game = false) {
    std::map<uint32_t, B> leaves, memo;
    std::map<uint32_t, std::pair<uint32_t, uint32_t>> gates;
    uint32_t nstate = game ? aig_num_latches(aig) : 0;
    if (game)
      for (uint32_t p = 0; p < nstate; p++) {
        uint32_t lit;
        aig_latch_at(aig, p, &lit, nullptr, nullptr);
        leaves.emplace(lit / 2, var(p));
      }
    for (uint32_t p = 0; p < aig_num_inputs(aig); p++) {
      uint32_t lit;
      aig_input_name(aig, p, &lit);
      leaves.emplace(lit / 2, var(nstate + p));
    }
    for (uint32_t p = 0; p < aig_num_ands(aig); p++) {
      uint32_t lhs, left, right;
      aig_and_at(aig, p, &lhs, &left, &right);
      gates.emplace(lhs / 2, std::pair{left, right});
    }
    std::function<B(uint32_t)> value = [&](uint32_t lit) -> B {
      tick();
      if (lit == 0)
        return f();
      if (lit == 1)
        return t();
      if (lit & 1)
        return neg(value(lit ^ 1));
      uint32_t variable = lit / 2;
      if (auto it = leaves.find(variable); it != leaves.end())
        return it->second;
      if (auto it = memo.find(variable); it != memo.end())
        return it->second;
      auto gate = gates.find(variable);
      if (gate == gates.end())
        decline(FailureCause::error, "schema_abi",
                "AIG root references missing gate");
      B right = value(gate->second.second);
      B left = value(gate->second.first);
      B result = land(left, right);
      memo.emplace(variable, result);
      return result;
    };
    return value(root);
  }
  uint32_t to_aig(Aig *aig, const B &root,
                  const std::map<int, uint32_t> &lits) {
    std::map<Handle, uint32_t> memo;
    std::function<uint32_t(const B &)> visit = [&](const B &node) -> uint32_t {
      tick("certificate_export");
      if (oxidd_bdd_node_level(node.v) == (oxidd_level_no_t)-1)
        return oxidd_bdd_satisfiable(node.v) ? AIG_TRUE : AIG_FALSE;
      auto h = handle(node);
      auto it = memo.find(h);
      if (it != memo.end())
        return it->second;
      int variable = int(oxidd_bdd_node_var(node.v));
      auto found = lits.find(variable);
      if (found == lits.end())
        decline(FailureCause::error, "candidate", "unmapped BDD variable");
      B hi(oxidd_bdd_cofactor_true(node.v));
      B lo(oxidd_bdd_cofactor_false(node.v));
      uint32_t x = found->second;
      // Export low first, including its guard, to keep historical gate IDs.
      uint32_t low = aig_and(aig, aig_not(x), visit(lo));
      uint32_t high = aig_and(aig, x, visit(hi));
      uint32_t result = aig_or(aig, high, low);
      memo.emplace(h, result);
      return result;
    };
    return visit(root);
  }
};
std::string normal_key(const Variable &v, const std::map<int, int> &slots) {
  std::vector<std::string> coords;
  for (int x : v.indices) {
    auto it = slots.find(x);
    coords.push_back(it == slots.end() ? key({"fixed", field(x)})
                                       : key({"slot", field(it->second)}));
  }
  return key({v.kind, v.prefix, join(coords)});
}
std::vector<int> ordered(const GameView &view, const std::vector<int> &subset,
                         const Goal *goal) {
  std::vector<int> out = subset;
  std::sort(out.begin(), out.end(), [&](int a, int b) {
    if (goal && a == goal->owner)
      return true;
    if (goal && b == goal->owner)
      return false;
    return std::tie(view.roles.at(a), a) < std::tie(view.roles.at(b), b);
  });
  return out;
}
std::string group_key(const GameView &view, const std::vector<int> &subset,
                      const Goal *goal) {
  std::vector<std::string> roles, relation;
  for (int x : subset) {
    roles.push_back(view.roles.at(x));
    relation.push_back(goal && goal->owner == x ? "goal" : "other");
  }
  return key({join(roles), join(relation)});
}
uint64_t choose_bounded(size_t n, size_t k, uint32_t cap) {
  if (k > n)
    return 0;
  uint64_t count = 1;
  for (size_t p = 1; p <= k; p++) {
    if (count > uint64_t(cap) * p / (n - k + p))
      return uint64_t(cap) + 1;
    count = count * (n - k + p) / p;
  }
  return count;
}
using Template = std::map<std::string, B>;
Template project(Schema &bdd, const GameView &view, const B &function,
                 int arity, const Goal *goal, const Config &cfg) {
  if (choose_bounded(view.members.size(), arity,
                     cfg.o.max_subsets_per_predicate) >
      cfg.o.max_subsets_per_predicate)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                  "schema_capacity", "subset count limit");
  Template result;
  B rebuilt = bdd.t();
  auto support = bdd.support(function);
  subsets(view.members, arity, [&](const std::vector<int> &selected) {
    cfg.check("schema");
    auto subset = ordered(view, selected, goal);
    std::set<int> set(subset.begin(), subset.end());
    std::map<int, int> slots;
    for (size_t p = 0; p < subset.size(); p++)
      slots[subset[p]] = int(p);
    std::set<int> keep, drop;
    std::map<int, int> mapping, back;
    for (const auto &v : view.variables) {
      if (std::includes(set.begin(), set.end(), v.owners.begin(),
                        v.owners.end())) {
        keep.insert(v.index);
        int normalized = bdd.normal_var(normal_key(v, slots));
        mapping[v.index] = normalized;
        if (!back.emplace(normalized, v.index).second)
          decline(FailureCause::applicability, "schema_abi",
                  "duplicate normalized variable");
      }
    }
    for (int v : support)
      if (!keep.count(v))
        drop.insert(v);
    B projected =
        drop.empty() ? function : bdd.exists(function, bdd.cube(drop));
    B normalized = bdd.relabel(projected, mapping);
    auto group = group_key(view, subset, goal);
    auto found = result.find(group);
    if (found != result.end() && !same(found->second, normalized))
      decline(FailureCause::applicability, "schema",
              "within-role projection disagreement");
    result.insert_or_assign(group, normalized);
    rebuilt = bdd.land(rebuilt, bdd.relabel(normalized, back));
  });
  if (!same(rebuilt, function))
    decline(FailureCause::applicability, "schema",
            "predicate not exactly reconstructed");
  return result;
}
struct Learned {
  Template templ;
  int arity;
};
Learned learn(Schema &bdd, const std::vector<GameView> &seeds,
              const std::vector<std::string> &names,
              const std::vector<const Goal *> &goals, const Config &cfg) {
  FailureCause cause = FailureCause::applicability;
  int limit = int(cfg.o.max_predicate_arity);
  for (const auto &seed : seeds)
    limit = std::min(limit, int(seed.members.size()));
  for (int arity = 0; arity <= limit; arity++) {
    cfg.check("schema");
    bool has_larger = false;
    for (const auto &seed : seeds)
      has_larger |= seed.members.size() > size_t(arity);
    if (!has_larger)
      continue;
    std::vector<Template> observed;
    try {
      for (size_t p = 0; p < seeds.size(); p++) {
        const auto &seed = seeds[p];
        B predicate =
            bdd.from_aig(seed.inst->cert.get(), seed.output(names[p]));
        observed.push_back(project(bdd, seed, predicate, arity, goals[p], cfg));
      }
    } catch (const Failure &e) {
      if (e.status != TLSF_GR1_LIFT_DECLINED)
        throw;
      if (!is_applicability(e.cause))
        cause = e.cause;
      continue;
    }
    bool equal = true;
    for (size_t p = 1; p < observed.size(); p++) {
      if (observed[p].size() != observed[0].size()) {
        equal = false;
        break;
      }
      for (const auto &[group, fun] : observed[0]) {
        auto it = observed[p].find(group);
        if (it == observed[p].end() || !same(fun, it->second)) {
          equal = false;
          break;
        }
      }
    }
    if (equal)
      return {std::move(observed[0]), arity};
  }
  decline(cause, "schema", "no bounded exact template");
}
B instantiate(Schema &bdd, const GameView &target, const Learned &learned,
              const Goal *goal, const Config &cfg) {
  if (choose_bounded(target.members.size(), learned.arity,
                     cfg.o.max_subsets_per_predicate) >
      cfg.o.max_subsets_per_predicate)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                  "schema_capacity", "target subset count limit");
  B result = bdd.t();
  subsets(target.members, learned.arity, [&](const std::vector<int> &selected) {
    cfg.check("instantiate");
    auto subset = ordered(target, selected, goal);
    auto it = learned.templ.find(group_key(target, subset, goal));
    if (it == learned.templ.end())
      decline(FailureCause::applicability, "instantiate",
              "missing role template");
    std::set<int> set(subset.begin(), subset.end());
    std::map<int, int> slots;
    for (size_t p = 0; p < subset.size(); p++)
      slots[subset[p]] = int(p);
    std::map<std::string, int> concrete;
    for (const auto &v : target.variables)
      if (std::includes(set.begin(), set.end(), v.owners.begin(),
                        v.owners.end()))
        concrete[normal_key(v, slots)] = v.index;
    std::map<int, int> mapping;
    for (int variable : bdd.support(it->second)) {
      auto found = concrete.find(bdd.normal_key(variable));
      if (found == concrete.end())
        decline(FailureCause::applicability, "instantiate",
                "missing target variable");
      mapping[variable] = found->second;
    }
    result = bdd.land(result, bdd.relabel(it->second, mapping));
  });
  return result;
}
struct LearnedCertificate {
  std::map<std::string, B> predicates;
  std::map<std::string, int> arities;
  std::vector<int> depths;
};

std::map<std::string, B> fold_atoms(Schema &bdd, const GameView &view) {
  const Aig *game = view.inst->r.game;
  std::map<int, std::tuple<int, uint32_t, uint32_t>> states;
  for (uint32_t p = 0; p < view.states; p++) {
    uint32_t lit, next, reset;
    aig_latch_at(game, p, &lit, &next, &reset);
    states[int(lit)] = {int(p), next, reset};
  }
  std::map<std::string, B> atoms;
  for (const auto &[schema, monitors] : fold_inventory(*view.inst)) {
    B live = bdd.t(), except = bdd.t();
    bool tagged = true;
    for (const O *monitor : monitors) {
      B any = bdd.f(), rest = bdd.f();
      unsigned transients = 0;
      for (int lit : ints(monitor->at("latch_literals").as_array())) {
        const auto &[pos, next, reset] = states.at(lit);
        B state = bdd.var(pos);
        any = bdd.lor(any, state);
        // A semantic tag, never a monitor-state ordinal or a one-hot premise.
        if (reset == 1 && next == 0)
          ++transients;
        else
          rest = bdd.lor(rest, state);
      }
      tagged &= transients == 1;
      live = bdd.land(live, any);
      except = bdd.land(except, rest);
    }
    atoms.emplace(key({schema, "Live"}), std::move(live));
    if (tagged)
      atoms.emplace(key({schema, "LiveExcept(transient)"}), std::move(except));
  }
  return atoms;
}
struct FoldRule {
  struct Term {
    bool zero = true;
    std::set<std::string> atoms;
  };
  std::map<std::string, Term> terms;
  std::map<std::string, int> depths;
};
std::string fold_rank(const Goal &g, int level, int fair) {
  return key({g.key, field(level), field(fair)});
}
FoldRule learn_fold(Schema &bdd, const std::vector<GameView> &seeds,
                    const GameView &target, const Config &cfg) {
  FoldRule rule;
  const auto target_atoms = fold_atoms(bdd, target);
  auto observe = [&](const std::string &name, const B &predicate,
                     const std::map<std::string, B> &atoms) {
    auto [it, inserted] = rule.terms.try_emplace(name);
    auto &term = it->second;
    term.zero &= same(predicate, bdd.f());
    std::set<std::string> implied;
    for (const auto &[atom, value] : atoms) {
      cfg.check("fold_learning");
      if (target_atoms.count(atom) &&
          same(bdd.land(predicate, value), predicate))
        implied.insert(atom);
    }
    if (inserted)
      term.atoms = std::move(implied);
    else {
      std::set<std::string> common;
      std::set_intersection(term.atoms.begin(), term.atoms.end(),
                            implied.begin(), implied.end(),
                            std::inserter(common, common.end()));
      term.atoms = std::move(common);
    }
  };
  for (const auto &seed : seeds) {
    if (seed.fairness != target.fairness)
      decline(FailureCause::applicability, "fold_learning",
              "fold_fairness_changed");
    const auto atoms = fold_atoms(bdd, seed);
    observe("inv", bdd.from_aig(seed.inst->cert.get(), seed.output("inv")),
            atoms);
    for (const auto &g : seed.goals) {
      int depth = seed.levels(g);
      auto [it, inserted] = rule.depths.emplace(g.key, depth);
      if (depth < 1 || (!inserted && it->second != depth))
        decline(FailureCause::applicability, "fold_learning",
                "fold_rank_depth_changed");
      for (int k = 0; k < depth; k++)
        for (uint32_t f = 0; f < std::max(1u, seed.fairness); f++) {
          auto name = "x_" + field(g.number) + "_" + field(k) + "_" + field(f);
          observe(fold_rank(g, k, f),
                  bdd.from_aig(seed.inst->cert.get(), seed.output(name)),
                  atoms);
        }
    }
  }
  for (const auto &g : target.goals)
    if (!rule.depths.count(g.key))
      decline(FailureCause::applicability, "fold_learning",
              "fold_no_candidate");
  return rule;
}
LearnedCertificate instantiate_fold(Schema &bdd, const GameView &view,
                                    const FoldRule &rule) {
  const auto atoms = fold_atoms(bdd, view);
  auto predicate = [&](const std::string &name) {
    const auto &term = rule.terms.at(name);
    B out = term.zero ? bdd.f() : bdd.t();
    for (const auto &atom : term.atoms) {
      if (!atoms.count(atom))
        decline(FailureCause::applicability, "fold_instantiation",
                "fold_missing_tag");
      out = bdd.land(out, atoms.at(atom));
    }
    return out;
  };
  LearnedCertificate out;
  out.predicates.emplace("inv", predicate("inv"));
  for (const auto &g : view.goals) {
    int depth = rule.depths.at(g.key);
    out.depths.push_back(depth);
    const uint32_t *members;
    uint32_t count;
    aig_justice_at(view.inst->r.game, g.number, &members, &count);
    out.predicates.emplace("goal_" + field(g.number),
                           bdd.from_aig(view.inst->r.game, members[0], true));
    for (int k = 0; k < depth; k++) {
      B y = bdd.f();
      for (uint32_t f = 0; f < std::max(1u, view.fairness); f++) {
        B x = predicate(fold_rank(g, k, f));
        y = bdd.lor(y, x);
        out.predicates.emplace("x_" + field(g.number) + "_" + field(k) + "_" +
                                   field(f),
                               std::move(x));
      }
      out.predicates.emplace("y_" + field(g.number) + "_" + field(k),
                             std::move(y));
    }
  }
  return out;
}
LearnedCertificate learn_certificate(Schema &bdd,
                                     const std::vector<GameView> &seeds,
                                     const GameView &target,
                                     const Config &cfg) {
  if (seeds.empty())
    decline(FailureCause::error, "schema", "no seeds");
  for (const auto &seed : seeds) {
    if (seed.fairness != target.fairness)
      decline(FailureCause::applicability, "schema_abi", "fairness changed");
    std::set<std::string> left, right;
    for (const auto &[coord, role] : seed.roles)
      left.insert(role);
    for (const auto &[coord, role] : target.roles)
      right.insert(role);
    if (left != right)
      decline(FailureCause::applicability, "schema_abi",
              "role classes changed");
  }
  LearnedCertificate out;
  // Rank depth is a property of the selected solved seeds. Check it before
  // predicate learning so an unstable family has a precise decline stage.
  for (const Goal &goal : target.goals) {
    int depth = -1;
    for (const auto &seed : seeds) {
      const Goal *found = nullptr;
      for (const Goal &g : seed.goals)
        if (g.key == goal.key) {
          found = &g;
          break;
        }
      if (!found)
        decline(FailureCause::applicability, "schema_abi", "goal class absent");
      int current = seed.levels(*found);
      if (current < 1)
        decline(FailureCause::error, "schema", "empty rank depth");
      if (depth >= 0 && current != depth)
        throw Failure(TLSF_GR1_LIFT_DECLINED, FailureCause::applicability,
                      "schema",
                      "rank depth changed from " + field(depth) + " to " +
                          field(current));
      depth = current;
    }
    out.depths.push_back(depth);
  }
  auto inv = learn(bdd, seeds, std::vector<std::string>(seeds.size(), "inv"),
                   std::vector<const Goal *>(seeds.size(), nullptr), cfg);
  out.predicates.emplace("inv", instantiate(bdd, target, inv, nullptr, cfg));
  out.arities["inv"] = inv.arity;
  for (size_t goal_pos = 0; goal_pos < target.goals.size(); goal_pos++) {
    const Goal &goal = target.goals[goal_pos];
    std::vector<const Goal *> aligned;
    for (const auto &seed : seeds) {
      const Goal *found = nullptr;
      for (const Goal &g : seed.goals)
        if (g.key == goal.key) {
          found = &g;
          break;
        }
      if (!found)
        decline(FailureCause::applicability, "schema_abi", "goal class absent");
      aligned.push_back(found);
    }
    int depth = out.depths[goal_pos];
    const uint32_t *members = nullptr;
    uint32_t count = 0;
    aig_justice_at(target.inst->r.game, goal.number, &members, &count);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 6)
      count = 2;
#endif
    if (count != 1)
      decline(FailureCause::error, "schema_abi", "multi-member justice");
    out.predicates.emplace("goal_" + field(goal.number),
                           bdd.from_aig(target.inst->r.game, members[0], true));
    for (int level = 0; level < depth; level++) {
      B y = bdd.f();
      for (int fair = 0; fair < int(std::max(1u, target.fairness)); fair++) {
        std::vector<std::string> names;
        for (const Goal *g : aligned)
          names.push_back("x_" + field(g->number) + "_" + field(level) + "_" +
                          field(fair));
        auto learned = learn(bdd, seeds, names, aligned, cfg);
        std::string name =
            "x_" + field(goal.number) + "_" + field(level) + "_" + field(fair);
        B x = instantiate(bdd, target, learned, &goal, cfg);
        y = bdd.lor(y, x);
        out.predicates.emplace(name, std::move(x));
        out.arities[name] = learned.arity;
      }
      out.predicates.emplace("y_" + field(goal.number) + "_" + field(level),
                             std::move(y));
    }
  }
  return out;
}
struct ParamSignature {
  std::vector<int> states;
  std::vector<uint32_t> reset;
  std::vector<B> next;
  B acceptance;
};
std::map<std::string, int> param_fairness(const Instance &i) {
  std::map<std::string, int> out;
  int lane = 0;
  for (const J &v : i.data.at("monitors").as_array()) {
    const O &m = v.as_object();
    if (s(m, "role") == "fairness") {
      if (!m.at("source_origin")
               .as_object()
               .at("bindings")
               .as_array()
               .empty() ||
          !out.emplace(param_key(m), lane++).second)
        param_decline("param_fairness_changed");
    }
  }
  if (out.size() != aig_num_fairness(i.r.game))
    param_decline("param_fairness_changed");
  if (out.empty())
    out.emplace("implicit_true_fairness", 0);
  return out;
}
std::map<std::string, B> param_features(Schema &bdd, const GameView &view,
                                        const O &m) {
  const O &o = m.at("source_origin").as_object();
  auto bound = ints(o.at("index_tuple").as_array());
  auto decls = declarations(*view.inst);
  std::map<uint32_t, int> letters;
  for (uint32_t p = 0; p < view.inputs; p++) {
    uint32_t lit;
    aig_input_name(view.inst->r.game, p, &lit);
    letters[lit] = int(view.states + p);
  }
  auto atom = [&](const O &r) {
    return bdd.var(letters.at(uint32_t(n(r, "game_literal"))));
  };
  std::map<std::string, std::set<int>> refs;
  std::map<std::string, B> out;
  for (const J &v : o.at("signal_refs").as_array()) {
    const O &r = v.as_object();
    const auto id = s(r, "declaration_id");
    auto coords = ints(r.at("index_tuple").as_array());
    if (coords.empty())
      out.emplace(key({id, "scalar"}), atom(*decls.at(id).front()));
    else
      refs[id].insert(coords.at(0));
  }
  for (const auto &[id, coords] : refs) {
    const auto &rows = decls.at(id);
    if (bound.empty() && coords.size() == rows.size() && rows.size() > 1) {
      B none = bdd.t(), amo = bdd.t();
      for (const O *r : rows) {
        B x = atom(*r);
        amo = bdd.lor(bdd.land(amo, bdd.neg(x)), bdd.land(none, x));
        none = bdd.land(none, bdd.neg(x));
      }
      out.emplace(key({id, "count0"}), std::move(none));
      out.emplace(key({id, "count01"}), std::move(amo));
    } else
      for (int c : coords)
        for (const O *r : rows)
          if (ints(r->at("index_tuple").as_array()).at(0) == c)
            out.emplace(!bound.empty() && c == bound[0]
                            ? key({id, "owner"})
                            : key({id, "constant", field(c)}),
                        atom(*r));
  }
  return out;
}
ParamSignature param_signature(Schema &bdd, const GameView &view, const O &m) {
  const Aig *game = view.inst->r.game;
  const auto lits = ints(m.at("latch_literals").as_array());
  // shortcut: finite transport search up to six state bits; grow only with
  // evidence.
  if (lits.empty() || lits.size() > 6 ||
      lits.size() != size_t(n(m, "state_count")))
    param_decline("param_tag_transport");
  auto features = param_features(bdd, view, m);
  if (features.size() > 8)
    param_decline("param_feature_alphabet");
  ParamSignature out;
  std::map<int, int> mapping;
  std::vector<uint32_t> next;
  for (int lit : lits) {
    bool found = false;
    for (uint32_t p = 0; p < view.states; p++) {
      uint32_t cur, nxt, reset;
      aig_latch_at(game, p, &cur, &nxt, &reset);
      if (int(cur) == lit) {
        found = true;
        out.states.push_back(int(p));
        out.reset.push_back(reset);
        next.push_back(nxt);
        mapping[int(p)] =
            bdd.normal_var(key({"param-tag-state", field(mapping.size())}));
      }
    }
    if (!found)
      param_decline("param_monitor_inventory");
  }
  std::vector<std::pair<B, B>> alphabet;
  for (unsigned mask = 0; mask < (1u << features.size()); mask++) {
    B concrete = bdd.t(), abstract = bdd.t();
    unsigned bit = 0;
    for (const auto &[name, f] : features) {
      bool value = mask & (1u << bit++);
      concrete = bdd.land(concrete, value ? f : bdd.neg(f));
      B v = bdd.var(bdd.normal_var(key({"param-tag-letter", name})));
      abstract = bdd.land(abstract, value ? v : bdd.neg(v));
    }
    if (!same(concrete, bdd.f()))
      alphabet.emplace_back(std::move(concrete), std::move(abstract));
  }
  std::set<int> letters;
  for (uint32_t p = 0; p < view.inputs; p++)
    letters.insert(int(view.states + p));
  B cube = bdd.cube(letters);
  for (uint32_t lit : next) {
    B actual = bdd.from_aig(game, lit, true), normal = bdd.f();
    for (const auto &[condition, abstract] : alphabet) {
      B selected = bdd.land(actual, condition);
      B coefficient = bdd.exists(selected, cube);
      if (!same(selected, bdd.land(coefficient, condition)))
        param_decline("param_tag_transport");
      for (int v : bdd.support(coefficient))
        if (!mapping.count(v))
          param_decline("param_tag_transport");
      normal = bdd.lor(normal,
                       bdd.land(bdd.relabel(coefficient, mapping), abstract));
    }
    out.next.push_back(std::move(normal));
  }
  uint32_t acceptance;
  if (s(m, "role") == "justice") {
    const uint32_t *members;
    uint32_t count;
    aig_justice_at(game, uint32_t(n(m, "justice_index")), &members, &count);
    if (count != 1)
      param_decline("param_goal_inventory");
    acceptance = members[0];
  } else
    acceptance =
        aig_fairness_at(game, param_fairness(*view.inst).at(param_key(m)));
  B acc = bdd.from_aig(game, acceptance, true);
  for (int v : bdd.support(acc))
    if (!mapping.count(v))
      param_decline("param_tag_transport");
  out.acceptance = bdd.relabel(acc, mapping);
  return out;
}
std::vector<int> param_transport(Schema &bdd, const ParamSignature &reference,
                                 const ParamSignature &actual) {
  if (reference.states.size() != actual.states.size())
    param_decline("param_state_growth");
  std::vector<int> perm(actual.states.size());
  std::iota(perm.begin(), perm.end(), 0);
  std::vector<int> result;
  unsigned matches = 0;
  do {
    bdd.tick("param_tag_transport");
    bool equal = true;
    std::map<int, int> mapping;
    for (size_t p = 0; p < perm.size(); p++) {
      equal &= reference.reset[p] == actual.reset[perm[p]];
      mapping[bdd.normal_var(key({"param-tag-state", field(p)}))] =
          bdd.normal_var(key({"param-tag-state", field(perm[p])}));
    }
    if (!equal)
      continue;
    auto extend = [&](const B &b) {
      for (int v : bdd.support(b))
        if (!mapping.count(v))
          mapping[v] = v;
    };
    extend(reference.acceptance);
    for (const B &b : reference.next)
      extend(b);
    if (!same(bdd.relabel(reference.acceptance, mapping), actual.acceptance))
      continue;
    for (size_t p = 0; p < perm.size() && equal; p++)
      equal &=
          same(bdd.relabel(reference.next[p], mapping), actual.next[perm[p]]);
    if (equal) {
      matches++;
      result = perm;
    }
  } while (std::next_permutation(perm.begin(), perm.end()));
  if (matches != 1)
    param_decline("param_tag_transport");
  return result;
}
O bind_param(Schema &bdd, std::vector<GameView> &seeds, GameView &target,
             const Config &cfg) {
  std::map<std::string, ParamSignature> tags;
  const auto domain = param_domain(
      *target.inst, param_inventory(*target.inst, cfg), target.members, cfg);
  const auto fairness = param_fairness(*target.inst);
  A evidence;
  std::vector<GameView *> views;
  for (auto &v : seeds)
    views.push_back(&v);
  views.push_back(&target);
  for (GameView *view : views) {
    view->param = true;
    const auto actual_fairness = param_fairness(*view->inst);
    if (actual_fairness.size() != fairness.size() ||
        !std::equal(
            actual_fairness.begin(), actual_fairness.end(), fairness.begin(),
            [](const auto &a, const auto &b) { return a.first == b.first; }))
      param_decline("param_fairness_changed");
    for (int c : view->members)
      view->roles[c] =
          domain.constants.count(c) ? key({"constant", field(c)}) : "element";
    A bindings;
    for (const auto &[family, monitors] : param_inventory(*view->inst, cfg))
      for (const O *m : monitors) {
        auto sig = param_signature(bdd, *view, *m);
        if (!tags.count(family))
          tags.emplace(family, sig);
        auto transport = param_transport(bdd, tags.at(family), sig);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
        if (lift_test_fault == 16)
          param_decline("param_tag_transport");
#endif
        auto bound = ints(
            m->at("source_origin").as_object().at("index_tuple").as_array());
        for (size_t k = 0; k < transport.size(); k++) {
          auto &v = view->variables.at(sig.states.at(transport[k]));
          v.prefix = key({family, "tag", field(k)});
          v.indices.clear();
          v.owners.clear();
          if (!bound.empty()) {
            if (domain.constants.count(bound[0]))
              v.prefix = key({v.prefix, "constant", field(bound[0])});
            else {
              v.indices = bound;
              v.owners.insert(bound[0]);
            }
          }
        }
        if (s(*m, "role") == "justice") {
          auto &g = view->goals.at(size_t(n(*m, "justice_index")));
          g.owner = bound.empty() ? -1 : bound[0];
          g.key = key({family, bound.empty() ? "scalar"
                               : domain.constants.count(bound[0])
                                   ? key({"constant", field(bound[0])})
                                   : "element"});
        }
        A permutation;
        for (int p : transport)
          permutation.emplace_back(p);
        bindings.emplace_back(O{{"monitor", m->at("monitor")},
                                {"origin", m->at("source_origin")},
                                {"tag_transport", permutation}});
      }
    O values;
    for (const auto &[name, value] : view->inst->overrides)
      values[name] = value;
    char hash[65]{};
    sha256_hex(view->inst->r.aag, view->inst->r.aag_size, hash);
    evidence.emplace_back(O{
        {"parameters", values}, {"game_sha256", hash}, {"monitors", bindings}});
  }
  return O{{"generator", "parametric-support-fold-v1"},
           {"tag_validation", "unique reset/next/acceptance BDD equality"},
           {"bindings", evidence}};
}
// Existential projections produce a candidate G over fixed states, the goal's
// owner and one remaining element. Their conjunction must reconstruct P exactly
// on ALL Boolean states, including zero/multi-hot monitor encodings.
Learned param_project(Schema &bdd, const GameView &view, const B &predicate,
                      const Goal *goal, const Config &cfg) {
  Template templ;
  B rebuilt = bdd.t();
  auto support = bdd.support(predicate);
  std::vector<int> remaining;
  for (const auto &[c, role] : view.roles)
    if (role == "element" && (!goal || goal->owner != c))
      remaining.push_back(c);
  if (remaining.empty())
    param_decline("param_no_candidate");
  if (remaining.size() > cfg.o.max_subsets_per_predicate)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "param_schema",
                  "param_subset_budget");
  for (int element : remaining) {
    std::set<int> drop;
    std::map<int, int> mapping, back;
    for (const auto &v : view.variables) {
      if (v.kind != "state")
        continue;
      bool keep = v.owners.empty() || v.owners.count(element) ||
                  (goal && v.owners.count(goal->owner));
      if (!keep)
        continue;
      std::string slot = v.owners.empty()                      ? "fixed"
                         : goal && v.owners.count(goal->owner) ? "owner"
                                                               : "fold";
      int normal = bdd.normal_var(key({"param-predicate", v.prefix, slot}));
      mapping[v.index] = normal;
      if (!back.emplace(normal, v.index).second)
        param_decline("param_monitor_inventory");
    }
    for (int v : support)
      if (!mapping.count(v))
        drop.insert(v);
    B projected = bdd.exists(predicate, bdd.cube(drop));
    B normalized = bdd.relabel(projected, mapping);
    if (!templ.empty() && !same(templ.begin()->second, normalized))
      param_decline("param_no_candidate");
    templ.insert_or_assign("fold", normalized);
    rebuilt = bdd.land(rebuilt, bdd.relabel(normalized, back));
  }
  if (!same(rebuilt, predicate))
    param_decline("param_no_candidate");
  return {std::move(templ), 1};
}
B param_instantiate(Schema &bdd, const GameView &view, const Learned &rule,
                    const Goal *goal, const Config &cfg) {
  size_t count = 0;
  for (const auto &[c, role] : view.roles)
    count += role == "element" && (!goal || goal->owner != c);
  if (count > cfg.o.max_subsets_per_predicate)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "param_schema",
                  "param_subset_budget");
  B result = bdd.t();
  for (const auto &[c, role] : view.roles) {
    if (role != "element" || (goal && goal->owner == c))
      continue;
    std::map<int, int> mapping;
    for (const auto &v : view.variables) {
      if (v.kind != "state")
        continue;
      if (!v.owners.empty() && !v.owners.count(c) &&
          (!goal || !v.owners.count(goal->owner)))
        continue;
      const auto slot = v.owners.empty()                      ? "fixed"
                        : goal && v.owners.count(goal->owner) ? "owner"
                                                              : "fold";
      mapping[bdd.normal_var(key({"param-predicate", v.prefix, slot}))] =
          v.index;
    }
    for (int v : bdd.support(rule.templ.at("fold")))
      if (!mapping.count(v))
        param_decline("param_seed_mismatch");
    result = bdd.land(result, bdd.relabel(rule.templ.at("fold"), mapping));
  }
  return result;
}
LearnedCertificate learn_param(Schema &bdd, const std::vector<GameView> &seeds,
                               const GameView &target, const Config &cfg,
                               O &evidence) {
  std::map<std::string, Learned> rules;
  std::map<std::string, int> depths;
  const auto fairness = param_fairness(*target.inst);
  A checks;
  for (const auto &seed : seeds) {
    const auto seed_fairness = param_fairness(*seed.inst);
    unsigned exact = 0;
    auto observe = [&](const std::string &key, const std::string &name,
                       const Goal *g) {
      B actual = bdd.from_aig(seed.inst->cert.get(), seed.output(name));
      for (int v : bdd.support(actual))
        if (v >= int(seed.states))
          param_decline("param_no_candidate");
      if (!rules.count(key))
        rules.emplace(key, param_project(bdd, seed, actual, g, cfg));
      B rebuilt = param_instantiate(bdd, seed, rules.at(key), g, cfg);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      if (lift_test_fault == 18)
        rebuilt = bdd.neg(rebuilt);
#endif
      if (!same(actual, rebuilt))
        param_decline("param_seed_mismatch");
      exact++;
      return rebuilt;
    };
    observe("inv", "inv", nullptr);
    for (const auto &g : seed.goals) {
      const int depth = seed.levels(g);
      // Depth belongs to the source generator, including every binding class.
      const O *monitor = nullptr;
      for (const J &v : seed.inst->data.at("monitors").as_array())
        if (s(v.as_object(), "role") == "justice" &&
            n(v.as_object(), "justice_index") == g.number)
          monitor = &v.as_object();
      auto family = param_key(*monitor);
      if (depth < 1 || (depths.count(family) && depths.at(family) != depth))
        param_decline("param_rank_depth_changed");
      depths[family] = depth;
      const uint32_t *members;
      uint32_t count;
      aig_justice_at(seed.inst->r.game, g.number, &members, &count);
      if (count != 1 ||
          !same(bdd.from_aig(seed.inst->r.game, members[0], true),
                bdd.from_aig(seed.inst->cert.get(),
                             seed.output("goal_" + field(g.number)))))
        param_decline("param_seed_mismatch");
      exact++;
      for (int k = 0; k < depth; k++) {
        B y = bdd.f();
        for (const auto &[owner, f] : seed_fairness) {
          auto lane = key({g.key, field(k), owner});
          B x = observe(
              lane, "x_" + field(g.number) + "_" + field(k) + "_" + field(f),
              &g);
          y = bdd.lor(y, x);
        }
        if (!same(y, bdd.from_aig(
                         seed.inst->cert.get(),
                         seed.output("y_" + field(g.number) + "_" + field(k)))))
          param_decline("param_seed_mismatch");
        exact++;
      }
    }
    O values;
    for (const auto &[name, value] : seed.inst->overrides)
      values[name] = value;
    checks.emplace_back(O{{"parameters", values},
                          {"widths", A{}},
                          {"exact_predicates", true},
                          {"predicate_count", exact}});
  }
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (lift_test_fault == 17)
    param_decline("param_no_candidate");
  if (lift_test_fault == 20)
    param_decline("param_rank_depth_changed");
  if (lift_test_fault == 21)
    param_decline("param_fairness_changed");
#endif
  LearnedCertificate out;
  out.predicates.emplace(
      "inv", param_instantiate(bdd, target, rules.at("inv"), nullptr, cfg));
  for (const auto &g : target.goals) {
    const O *monitor = nullptr;
    for (const J &v : target.inst->data.at("monitors").as_array())
      if (s(v.as_object(), "role") == "justice" &&
          n(v.as_object(), "justice_index") == g.number)
        monitor = &v.as_object();
    int depth = depths.at(param_key(*monitor));
    out.depths.push_back(depth);
    const uint32_t *members;
    uint32_t count;
    aig_justice_at(target.inst->r.game, g.number, &members, &count);
    out.predicates.emplace("goal_" + field(g.number),
                           bdd.from_aig(target.inst->r.game, members[0], true));
    for (int k = 0; k < depth; k++) {
      B y = bdd.f();
      for (const auto &[owner, f] : fairness) {
        const auto lane = key({g.key, field(k), owner});
        if (!rules.count(lane))
          param_decline("param_no_candidate");
        B x = param_instantiate(bdd, target, rules.at(lane), &g, cfg);
        y = bdd.lor(y, x);
        out.predicates.emplace("x_" + field(g.number) + "_" + field(k) + "_" +
                                   field(f),
                               std::move(x));
      }
      out.predicates.emplace("y_" + field(g.number) + "_" + field(k),
                             std::move(y));
    }
  }
  evidence["seed_validation"] = "full Boolean BDD equality of W/X/Y/goals";
  evidence["seeds"] = checks;
  return out;
}

struct Candidate {
  std::string game, certificate, certificate_json, policy, policy_json,
      check_json, evidence;
  TlsfGr1CheckMethod method = TLSF_GR1_CHECK_CERTIFICATE;
  TlsfGr1CheckVerdict verdict = TLSF_GR1_CHECK_UNKNOWN;
  bool fold = false;
  bool param = false;
  std::string checker_order;
  O fold_evidence;
};
J certificate_sidecar(const GameView &target, const LearnedCertificate &learned,
                      const Aig *certificate,
                      TlsfGr1ReductionSemantics semantics) {
  const Aig *game = target.inst->r.game;
  uint32_t nstate = target.states, nin = target.inputs,
           ngoals = uint32_t(target.goals.size());
  uint32_t nu = 0, nc = 0;
  A state, unc, con, outputs, goals, counters, depths;
  for (uint32_t p = 0; p < nstate; p++) {
    uint32_t cur, next, reset;
    aig_latch_at(game, p, &cur, &next, &reset);
    state.emplace_back(O{{"certificate_input", p},
                         {"name", aig_latch_name(game, p)},
                         {"game_latch", p},
                         {"game_literal", cur},
                         {"next_game_literal", next},
                         {"reset", reset},
                         {"solver_added", false}});
  }
  for (uint32_t p = 0; p < nin; p++) {
    uint32_t lit;
    const char *name = aig_input_name(game, p, &lit);
    O row{{"certificate_input", nstate + p},
          {"game_input", p},
          {"game_literal", lit},
          {"name", name}};
    if (target.controls[p]) {
      con.emplace_back(std::move(row));
      nc++;
    } else {
      unc.emplace_back(std::move(row));
      nu++;
    }
  }
  outputs.emplace_back(O{{"name", "inv"}, {"kind", "winning_region"}});
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    std::string name = "goal_" + field(goal);
    outputs.emplace_back(O{{"name", name}, {"kind", "goal"}, {"goal", goal}});
  }
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    depths.emplace_back(learned.depths[goal]);
    for (int level = 0; level < learned.depths[goal]; level++) {
      std::string name = "y_" + field(goal) + "_" + field(level);
      outputs.emplace_back(O{{"name", name},
                             {"kind", "mu_level"},
                             {"goal", goal},
                             {"level", level}});
    }
  }
  for (uint32_t goal = 0; goal < ngoals; goal++)
    for (int level = 0; level < learned.depths[goal]; level++)
      for (uint32_t fair = 0; fair < std::max(1u, target.fairness); fair++) {
        std::string name =
            "x_" + field(goal) + "_" + field(level) + "_" + field(fair);
        outputs.emplace_back(O{{"name", name},
                               {"kind", "nu_level"},
                               {"goal", goal},
                               {"level", level},
                               {"fairness", fair}});
      }
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    std::string name = "move_" + field(goal);
    outputs.emplace_back(
        O{{"name", name}, {"kind", "move_relation"}, {"goal", goal}});
    goals.emplace_back(
        O{{"goal", goal}, {"justice_record", goal}, {"record_member", 0}});
    counters.emplace_back(O{{"strategy_latch", nstate + goal},
                            {"name", "__tlsf_gr1_goal_counter_" + field(goal)},
                            {"goal", goal},
                            {"reset", 0},
                            {"effective_initial", goal == 0},
                            {"advance_to_goal", (goal + 1) % ngoals}});
  }
  return O{
      {"format", "tlsf-gr1-certificate-v1"},
      {"status", "realizable"},
      {"side", "system"},
      {"reduction_semantics", semantics == TLSF_GR1_EXACT ? "exact" : "strict"},
      {"circuit", O{{"path", "memory"}, {"kind", "ASCII AIGER combinational"}}},
      {"fixpoint", target.fold ? "monitor-fold candidate"
                               : "generalized fixed-arity monitor certificate"},
      {"counts", O{{"goals", ngoals},
                   {"justice_records", aig_num_justice(game)},
                   {"fairness_assumptions", target.fairness},
                   {"state_variables", nstate},
                   {"original_game_latches", nstate},
                   {"sampling_latches", 0},
                   {"uncontrollable_inputs", nu},
                   {"controllable_inputs", nc},
                   {"predicates", aig_num_outputs(certificate)},
                   {"aig_inputs", aig_num_inputs(certificate)},
                   {"aig_latches", 0},
                   {"aig_ands", aig_num_ands(certificate)},
                   {"levels_per_goal", depths}}},
      {"outputs", outputs},
      {"goals", goals},
      {"variables",
       O{{"state", state}, {"uncontrollable", unc}, {"controllable", con}}},
      {"sampling_semantics",
       "No input-dependent acceptance sampling latches were required."},
      {"goal_counter_latches", counters},
      {"goal_counter_semantics",
       "All-zero denotes goal 0; goals advance cyclically."},
      {"rank_semantics", "y_j_k is definitionally the union of x_j_k_i."},
      {"move_semantics",
       target.fold ? "Placeholders unused by the region method."
                   : "Target transition relation and lifted invariant/ranks."},
      {"move_source", "target_game"}};
}
std::unique_ptr<Aig, decltype(&aig_free)>
emit_certificate(Schema &bdd, const GameView &target,
                 const LearnedCertificate &learned, const Config &cfg) {
  const Aig *game = target.inst->r.game;
  auto out = std::unique_ptr<Aig, decltype(&aig_free)>(aig_new(), &aig_free);
  if (!out)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                  "certificate_export", "cannot allocate AIG");
  std::map<int, uint32_t> current, following;
  for (uint32_t p = 0; p < target.states; p++)
    current[int(p)] = aig_input(out.get(), aig_latch_name(game, p));
  for (uint32_t p = 0; p < target.inputs; p++)
    current[int(target.states + p)] =
        aig_input(out.get(), aig_input_name(game, p, nullptr));
  if (target.fold) {
    for (const auto &[name, predicate] : learned.predicates)
      aig_set_output(out.get(), name.c_str(),
                     bdd.to_aig(out.get(), predicate, current));
    for (const auto &g : target.goals)
      aig_set_output(out.get(), ("move_" + field(g.number)).c_str(), 0);
    return out;
  }
  std::map<uint32_t, uint32_t> translated;
  for (uint32_t p = 0; p < target.states; p++) {
    uint32_t cur;
    aig_latch_at(game, p, &cur, nullptr, nullptr);
    translated[cur / 2] = current[int(p)];
  }
  for (uint32_t p = 0; p < target.inputs; p++) {
    uint32_t lit;
    aig_input_name(game, p, &lit);
    translated[lit / 2] = current[int(target.states + p)];
  }
  std::map<uint32_t, std::pair<uint32_t, uint32_t>> gates;
  for (uint32_t p = 0; p < aig_num_ands(game); p++) {
    uint32_t lhs, left, right;
    aig_and_at(game, p, &lhs, &left, &right);
    gates[lhs / 2] = {left, right};
  }
  std::function<uint32_t(uint32_t)> translate = [&](uint32_t lit) -> uint32_t {
    cfg.check("certificate_export");
    if (lit < 2)
      return lit;
    if (lit & 1)
      return aig_not(translate(lit ^ 1));
    auto it = translated.find(lit / 2);
    if (it != translated.end())
      return it->second;
    auto gate = gates.find(lit / 2);
    if (gate == gates.end())
      decline(FailureCause::error, "candidate", "unmapped target game gate");
    uint32_t right = translate(gate->second.second);
    uint32_t left = translate(gate->second.first);
    uint32_t value = aig_and(out.get(), left, right);
    translated.emplace(lit / 2, value);
    return value;
  };
  for (uint32_t p = 0; p < target.states; p++) {
    uint32_t next;
    aig_latch_at(game, p, nullptr, &next, nullptr);
    following[int(p)] = translate(next);
  }
  for (uint32_t p = 0; p < target.inputs; p++)
    following[int(target.states + p)] = current[int(target.states + p)];
  uint32_t bad = 0;
  for (uint32_t p = 0; p < aig_num_bad(game); p++) {
    uint32_t lit;
    aig_bad_at(game, p, &lit);
    bad = aig_or(out.get(), bad, translate(lit));
  }
  auto predicate = [&](const std::string &name) -> const B & {
    return learned.predicates.at(name);
  };
  auto now = [&](const B &b) { return bdd.to_aig(out.get(), b, current); };
  auto later = [&](const B &b) { return bdd.to_aig(out.get(), b, following); };
  auto inv = predicate("inv");
  aig_set_output(out.get(), "inv", now(inv));
  for (const Goal &g : target.goals) {
    std::string name = "goal_" + field(g.number);
    aig_set_output(out.get(), name.c_str(), now(predicate(name)));
  }
  for (const Goal &g : target.goals)
    for (int level = 0; level < learned.depths[g.number]; level++) {
      std::string name = "y_" + field(g.number) + "_" + field(level);
      aig_set_output(out.get(), name.c_str(), now(predicate(name)));
    }
  for (const Goal &g : target.goals)
    for (int level = 0; level < learned.depths[g.number]; level++)
      for (uint32_t fair = 0; fair < std::max(1u, target.fairness); fair++) {
        std::string name =
            "x_" + field(g.number) + "_" + field(level) + "_" + field(fair);
        aig_set_output(out.get(), name.c_str(), now(predicate(name)));
      }
  std::vector<B> fairness;
  for (uint32_t fair = 0; fair < target.fairness; fair++)
    fairness.push_back(bdd.from_aig(game, aig_fairness_at(game, fair), true));
  for (const Goal &g : target.goals) {
    B at_goal = bdd.land(inv, predicate("goal_" + field(g.number)));
    uint32_t safe_next = aig_and(out.get(), aig_not(bad), later(inv));
    uint32_t at_goal_now = now(at_goal);
    uint32_t move = aig_and(out.get(), at_goal_now, safe_next);
    B covered = at_goal;
    for (int level = 0; level < learned.depths[g.number]; level++) {
      B strict = level == 0
                     ? at_goal
                     : bdd.lor(at_goal, predicate("y_" + field(g.number) + "_" +
                                                  field(level - 1)));
      for (uint32_t fair = 0; fair < std::max(1u, target.fairness); fair++) {
        const B &x = predicate("x_" + field(g.number) + "_" + field(level) +
                               "_" + field(fair));
        B fair_pred = fairness.empty() ? bdd.t() : fairness[fair];
        B rank_target = bdd.lor(strict, bdd.land(bdd.neg(fair_pred), x));
        B layer = bdd.land(x, bdd.neg(covered));
        uint32_t safe_target =
            aig_and(out.get(), aig_not(bad), later(rank_target));
        uint32_t layer_now = now(layer);
        move =
            aig_or(out.get(), move, aig_and(out.get(), layer_now, safe_target));
        covered = bdd.lor(covered, x);
      }
    }
    std::string name = "move_" + field(g.number);
    aig_set_output(out.get(), name.c_str(), move);
  }
  return out;
}
J policy_sidecar(const GameView &target, const Aig *policy,
                 TlsfGr1ReductionSemantics semantics) {
  const Aig *game = target.inst->r.game;
  uint32_t nstate = target.states, ngoals = uint32_t(target.goals.size());
  A state, counter, unc, con, advance;
  uint32_t uindex = 0, cindex = 0;
  for (uint32_t p = 0; p < nstate; p++)
    state.emplace_back(O{{"policy_input", p},
                         {"game_latch", p},
                         {"name", aig_latch_name(game, p)}});
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    counter.emplace_back(O{{"policy_input", nstate + goal},
                           {"goal", goal},
                           {"name", "curr_" + field(goal)},
                           {"reset", 0},
                           {"effective_initial", goal == 0}});
    advance.emplace_back(O{{"policy_output", 0},
                           {"goal", goal},
                           {"name", "curr_next_" + field(goal)}});
  }
  for (uint32_t p = 0; p < target.inputs; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (target.controls[p])
      con.emplace_back(
          O{{"policy_output", cindex++}, {"game_input", p}, {"name", name}});
    else
      unc.emplace_back(O{{"policy_input", nstate + ngoals + uindex++},
                         {"game_input", p},
                         {"name", name}});
  }
  for (uint32_t p = 0; p < ngoals; p++)
    advance[p].as_object()["policy_output"] = cindex + p;
  return O{
      {"format", "tlsf-gr1-policy-v1"},
      {"side", "system"},
      {"reduction_semantics", semantics == TLSF_GR1_EXACT ? "exact" : "strict"},
      {"circuit", O{{"path", "memory"}, {"kind", "ASCII AIGER combinational"}}},
      {"counts", O{{"game_state_variables", nstate},
                   {"original_game_latches", nstate},
                   {"sampling_latches", 0},
                   {"goals", ngoals},
                   {"uncontrollable_inputs", uindex},
                   {"controllable_outputs", cindex},
                   {"aig_inputs", aig_num_inputs(policy)},
                   {"aig_outputs", aig_num_outputs(policy)},
                   {"aig_ands", aig_num_ands(policy)}}},
      {"inputs",
       O{{"state", state}, {"counter", counter}, {"uncontrollable", unc}}},
      {"outputs", O{{"controllable", con}, {"counter_next", advance}}},
      {"counter_semantics",
       "All-zero denotes curr_0; advance on the current goal."},
      {"skolem_rule",
       "controllable inputs in game order, true/lowest index first"}};
}
std::unique_ptr<Aig, decltype(&aig_free)> emit_policy(Schema &bdd,
                                                      const GameView &target,
                                                      const Aig *certificate,
                                                      const Config &cfg) {
  const Aig *game = target.inst->r.game;
  uint32_t nstate = target.states, ngoals = uint32_t(target.goals.size());
  uint32_t public_width = nstate + target.inputs;
  int start = bdd.width();
  bdd.grow(start + int(ngoals) + int(public_width));
  std::map<int, int> public_to_policy;
  for (uint32_t p = 0; p < public_width; p++)
    public_to_policy[int(p)] = start + int(ngoals + p);
  std::vector<B> moves, goals, curr, effective;
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    std::string move = "move_" + field(goal), g = "goal_" + field(goal);
    moves.push_back(bdd.relabel(
        bdd.from_aig(certificate, aig_output_lit(certificate, move.c_str())),
        public_to_policy));
    goals.push_back(bdd.relabel(
        bdd.from_aig(certificate, aig_output_lit(certificate, g.c_str())),
        public_to_policy));
    curr.push_back(bdd.var(start + int(goal)));
  }
  B any = bdd.f();
  for (const B &b : curr)
    any = bdd.lor(any, b);
  for (uint32_t goal = 0; goal < ngoals; goal++)
    effective.push_back(goal == 0 ? bdd.lor(curr[0], bdd.neg(any))
                                  : curr[goal]);
  B relation = bdd.f();
  for (uint32_t goal = 0; goal < ngoals; goal++)
    relation = bdd.lor(relation, bdd.land(effective[goal], moves[goal]));
  std::vector<int> controls;
  std::vector<std::string> control_names;
  for (uint32_t p = 0; p < target.inputs; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (target.controls[p]) {
      controls.push_back(public_to_policy.at(int(nstate + p)));
      control_names.emplace_back(name);
    }
  }
  B control_cube = bdd.cube({controls.begin(), controls.end()});
  B chosen = bdd.t();
  std::vector<B> functions;
  for (int control : controls) {
    cfg.check("policy");
    B bit = bdd.var(control);
    B function =
        bdd.exists(bdd.land(bdd.land(relation, chosen), bit), control_cube);
    functions.push_back(function);
    B not_function = bdd.neg(function);
    B not_bit = bdd.neg(bit);
    B low = bdd.land(not_bit, not_function);
    B high = bdd.land(bit, function);
    chosen = bdd.land(chosen, bdd.lor(high, low));
  }
  std::vector<B> next_curr;
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    B advance = bdd.land(effective[goal], goals[goal]);
    uint32_t previous = (goal + ngoals - 1) % ngoals;
    B entered = bdd.land(effective[previous], goals[previous]);
    B stayed = bdd.land(effective[goal], bdd.neg(advance));
    next_curr.push_back(bdd.lor(stayed, entered));
  }
  auto policy = std::unique_ptr<Aig, decltype(&aig_free)>(aig_new(), &aig_free);
  if (!policy)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "policy",
                  "cannot allocate AIG");
  std::map<int, uint32_t> mapping;
  for (uint32_t p = 0; p < nstate; p++)
    mapping[public_to_policy.at(int(p))] =
        aig_input(policy.get(), aig_latch_name(game, p));
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    std::string name = "curr_" + field(goal);
    mapping[start + int(goal)] = aig_input(policy.get(), name.c_str());
  }
  for (uint32_t p = 0; p < target.inputs; p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (!target.controls[p])
      mapping[public_to_policy.at(int(nstate + p))] =
          aig_input(policy.get(), name);
  }
  for (size_t p = 0; p < controls.size(); p++)
    aig_set_output(policy.get(), control_names[p].c_str(),
                   bdd.to_aig(policy.get(), functions[p], mapping));
  for (uint32_t goal = 0; goal < ngoals; goal++) {
    std::string name = "curr_next_" + field(goal);
    aig_set_output(policy.get(), name.c_str(),
                   bdd.to_aig(policy.get(), next_curr[goal], mapping));
  }
  return policy;
}
TlsfGr1CheckResult
check(const TrustedTarget &trusted, const Candidate &candidate,
      const Config &cfg, TlsfGr1CheckMethod method, uint64_t deadline,
      TlsfGr1CheckVarOrder order = TLSF_GR1_CHECK_VAR_ORDER_AUTO,
      uint64_t *checks = nullptr) {
  char game_hash[65]{};
  sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), game_hash);
  if (trusted.game_hash != game_hash ||
      trusted.game_aag !=
          std::string(trusted.instance->r.aag, trusted.instance->r.aag_size))
    throw Failure(TLSF_GR1_LIFT_DECLINED, FailureCause::error, "target_check",
                  "prepared game changed before verification");
  StatsScope check_stats(cfg, TLSF_GR1_LIFT_STATS_INTERNAL_CHECK);
  if (cfg.stats)
    cfg.stats->internal_checks++;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (method == TLSF_GR1_CHECK_REGION &&
      (lift_test_fault == 2 || lift_test_fault == 3 || lift_test_fault == 4)) {
    if (checks)
      ++*checks;
    TlsfGr1CheckResult injected{};
    const bool capacity = lift_test_fault == 2 || lift_test_fault == 4;
    injected.status = capacity ? TLSF_GR1_CHECK_LIMIT : TLSF_GR1_CHECK_OK;
    injected.verdict =
        capacity ? TLSF_GR1_CHECK_UNKNOWN : TLSF_GR1_CHECK_CERT_FAILED;
    return injected;
  }
#endif
  TlsfGr1CheckInput input{};
  input.game_aag = {(const uint8_t *)trusted.game_aag.data(),
                    trusted.game_aag.size()};
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (lift_test_fault == 5)
    lift_test_checked_game_aag.assign(
        reinterpret_cast<const char *>(input.game_aag.data),
        input.game_aag.size);
#endif
  input.certificate_aag = {(const uint8_t *)candidate.certificate.data(),
                           candidate.certificate.size()};
  input.certificate_json = {(const uint8_t *)candidate.certificate_json.data(),
                            candidate.certificate_json.size()};
  if (method == TLSF_GR1_CHECK_CERTIFICATE) {
    input.policy_aag = {(const uint8_t *)candidate.policy.data(),
                        candidate.policy.size()};
    input.policy_json = {(const uint8_t *)candidate.policy_json.data(),
                         candidate.policy_json.size()};
  }
  TlsfGr1CheckOptions options{};
  options.method = method;
  options.node_cap = cfg.o.checker_nodes;
  options.cache_cap = cfg.o.checker_cache;
  options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  options.deadline_mono_ns = deadline;
  options.cancelled = cfg.o.cancelled;
  options.cancel_ctx = cfg.o.cancel_ctx;
  FoldBudget budget{cfg, {}};
  if (candidate.fold) {
    options.cancelled = FoldBudget::cancelled;
    options.cancel_ctx = &budget;
    options.deadline_mono_ns = cfg.effective_deadline();
    options.var_order = order;
  }
  TlsfGr1CheckResult result{};
  if (checks)
    ++*checks;
  tlsf_gr1_check(&input, &options, &result);
  if (candidate.fold) {
    try {
      budget.finish();
    } catch (...) {
      tlsf_gr1_check_result_clear(&result);
      throw;
    }
  }
  if (cfg.stats)
    cfg.stats->internal_check_peak_nodes = std::max<uint64_t>(
        cfg.stats->internal_check_peak_nodes, result.peak_nodes);
  return result;
}

// Candidate generation has no soundness claim. Only REGION_VERIFIED against
// the unchanged, source-bound target may publish REALIZABLE; the method's
// sufficiency is proved by Tlsf.Gr1.region_conditions_sound (PR #142).
void verify_fold(const TrustedTarget &trusted, Candidate &candidate,
                 const Config &cfg, SeedDeclines log,
                 uint64_t *checks = nullptr) try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (lift_test_fault == 12 || (candidate.param && lift_test_fault == 24))
    throw std::bad_alloc();
#endif
  // Aggregate temporal monitors made state-first construction exhaust the B2
  // deadline at n=10/11; input-first verifies the same unchanged obligations.
  const auto first = candidate.param ? TLSF_GR1_CHECK_VAR_ORDER_INPUT_FIRST
                                     : TLSF_GR1_CHECK_VAR_ORDER_AUTO;
  const auto second = candidate.param ? TLSF_GR1_CHECK_VAR_ORDER_AUTO
                                      : TLSF_GR1_CHECK_VAR_ORDER_INPUT_FIRST;
  const std::string prefix = candidate.param ? "param" : "fold";
  for (auto order : {first, second}) {
    const char *name =
        order == TLSF_GR1_CHECK_VAR_ORDER_AUTO ? "default" : "input-first";
    cfg.check("fold_region_check");
    auto result = check(trusted, candidate, cfg, TLSF_GR1_CHECK_REGION,
                        cfg.effective_deadline(), order, checks);
    auto clear = [](TlsfGr1CheckResult *r) {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      if ((lift_test_fault == 13 || lift_test_fault == 25) && r->json &&
          r->verdict == TLSF_GR1_CHECK_REGION_VERIFIED)
        ++lift_test_check_json_clears;
#endif
      tlsf_gr1_check_result_clear(r);
    };
    std::unique_ptr<TlsfGr1CheckResult, decltype(clear)> owned(&result, clear);
    const auto status = result.status;
    const auto verdict = result.verdict;
    const bool capacity =
        status == TLSF_GR1_CHECK_LIMIT &&
        !strcmp(result.message, "checker allocation or node cap exhausted");
    if (status == TLSF_GR1_CHECK_OK &&
        verdict == TLSF_GR1_CHECK_REGION_VERIFIED) {
      candidate.method = TLSF_GR1_CHECK_REGION;
      candidate.verdict = verdict;
      candidate.checker_order = name;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      if ((lift_test_fault == 13 ||
           (candidate.param && lift_test_fault == 25)) &&
          result.json)
        throw std::bad_alloc();
#endif
      if (result.json)
        candidate.check_json.assign(result.json, result.json_size);
      return;
    }
    owned.reset();
    log.note((prefix + "_region_failed(" + name + ")").c_str());
    if (capacity && order == first)
      continue;
    if (status == TLSF_GR1_CHECK_DEADLINE)
      throw cfg.deadline_failure("fold_region_check");
    if (status == TLSF_GR1_CHECK_CANCELLED)
      throw Failure(TLSF_GR1_LIFT_CANCELLED, FailureCause::cancelled,
                    "fold_region_check", "fold_cancelled");
    throw Failure(status == TLSF_GR1_CHECK_LIMIT ? TLSF_GR1_LIFT_LIMIT
                                                 : TLSF_GR1_LIFT_DECLINED,
                  check_failure_cause(status, verdict),
                  candidate.param ? "param_region_check" : "fold_region_check",
                  candidate.param ? "param_region_failed"
                                  : "fold_region_failed");
  }
} catch (const Failure &e) {
  log.note("fold_region_stopped");
  log.failure(e);
  throw;
} catch (const std::bad_alloc &) {
  log.note("fold_region_stopped");
  log.exception("fold_region_check", "resource", "host allocation failed");
  throw;
} catch (const std::exception &e) {
  log.note("fold_region_stopped");
  log.exception("fold_region_check", "error", e.what());
  throw;
}

O validate_fold_seeds(Schema &bdd, const std::vector<GameView> &seeds,
                      const FoldRule &rule, const std::string &axis,
                      const Config &cfg, uint64_t *checks) {
  A evidence;
  for (const auto &seed : seeds) {
    auto learned = instantiate_fold(bdd, seed, rule);
    bool exact = true;
    for (const auto &[name, predicate] : learned.predicates)
      exact &= same(predicate,
                    bdd.from_aig(seed.inst->cert.get(), seed.output(name)));
    auto cert = emit_certificate(bdd, seed, learned, cfg);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 9 && &seed == &seeds[1]) {
      aig_remove_output(cert.get(), "inv");
      aig_set_output(cert.get(), "inv", 0);
    }
#endif
    auto aag = render_aig(cert.get(), cfg);
    auto json =
        dump(certificate_sidecar(seed, learned, cert.get(), TLSF_GR1_EXACT));
    TlsfGr1CheckInput input{};
    input.game_aag = {(const uint8_t *)seed.inst->r.aag, seed.inst->r.aag_size};
    input.certificate_aag = {(const uint8_t *)aag.data(), aag.size()};
    input.certificate_json = {(const uint8_t *)json.data(), json.size()};
    TlsfGr1CheckOptions options{};
    options.method = TLSF_GR1_CHECK_REGION;
    options.node_cap = cfg.o.checker_nodes;
    options.cache_cap = cfg.o.checker_cache;
    options.max_artifact_bytes = cfg.o.max_artifact_bytes;
    options.deadline_mono_ns = cfg.effective_deadline();
    FoldBudget budget{cfg, {}};
    options.cancelled = FoldBudget::cancelled;
    options.cancel_ctx = &budget;
    TlsfGr1CheckResult checked{};
    BothPhase phase("native_fold_seed_check");
    if (checks)
      ++*checks;
    auto status = tlsf_gr1_check(&input, &options, &checked);
    const auto verdict = checked.verdict;
    tlsf_gr1_check_result_clear(&checked);
    budget.finish();
    if (status != TLSF_GR1_CHECK_OK ||
        verdict != TLSF_GR1_CHECK_REGION_VERIFIED)
      throw Failure(status == TLSF_GR1_CHECK_DEADLINE ? TLSF_GR1_LIFT_DEADLINE
                    : status == TLSF_GR1_CHECK_LIMIT  ? TLSF_GR1_LIFT_LIMIT
                                                      : TLSF_GR1_LIFT_DECLINED,
                    check_failure_cause(status, verdict), "fold_seed_check",
                    "fold_seed_mismatch");
    char hash[65]{};
    sha256_hex(seed.inst->r.aag, seed.inst->r.aag_size, hash);
    A mappings;
    for (const auto &[schema, monitors] : fold_inventory(*seed.inst)) {
      A instances;
      for (const O *m : monitors)
        instances.emplace_back(O{{"monitor", m->at("monitor")},
                                 {"origin", m->at("source_origin")},
                                 {"latch_literals", m->at("latch_literals")}});
      mappings.emplace_back(O{{"schema", schema}, {"instances", instances}});
    }
    O values;
    for (const auto &[name, value] : seed.inst->overrides)
      values[name] = value;
    A widths, profile;
    for (int width : fold_widths(*seed.inst, axis))
      widths.emplace_back(width);
    for (int width : fold_profile(fold_widths(*seed.inst, axis)))
      profile.emplace_back(width);
    evidence.emplace_back(O{{"parameters", values},
                            {"game_sha256", hash},
                            {"widths", widths},
                            {"relative_width_profile", profile},
                            {"exact_predicates", exact},
                            {"verdict", "REGION_VERIFIED"},
                            {"schemas", mappings}});
  }
  O terms;
  for (const auto &[name, term] : rule.terms) {
    A atoms;
    for (const auto &atom : term.atoms)
      atoms.emplace_back(atom);
    terms[name] = O{{"false", term.zero}, {"conjunction", atoms}};
  }
  return O{{"generator", "monitor-fold-v1"},
           {"seed_validation", "region"},
           {"seeds", evidence},
           {"predicates", terms}};
}
Candidate prove(Schema &bdd, const GameView &target,
                const LearnedCertificate &learned, const TrustedTarget &trusted,
                const Config &cfg, bool candidate_only = false,
                char *fold_detail = nullptr) {
  Candidate candidate;
  candidate.fold = target.fold;
  candidate.param = target.param;
  candidate.game = trusted.game_aag;
  const auto semantics = trusted.semantics;
  StatsScope candidate_stats(cfg, TLSF_GR1_LIFT_STATS_CANDIDATE_INSTANTIATION);
  candidate_stats.count_bdd_ops(bdd.operation_counter());
  auto cert = emit_certificate(bdd, target, learned, cfg);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if ((target.fold && lift_test_fault == 8) ||
      (target.param && lift_test_fault == 19)) {
    aig_remove_output(cert.get(), "inv");
    aig_set_output(cert.get(), "inv", 0);
  }
#endif
  candidate.certificate = render_aig(cert.get(), cfg);
  candidate.certificate_json =
      dump(certificate_sidecar(target, learned, cert.get(), semantics));
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (lift_test_fault == 5)
    lift_test_generated_certificate_json = candidate.certificate_json;
#endif
  cfg.bytes(candidate.certificate_json.size(), "certificate_export");
  if (cfg.stats)
    cfg.stats->candidate_bytes =
        candidate.certificate.size() + candidate.certificate_json.size();
  if (cfg.stats)
    cfg.stats->schema_nodes_after_candidate = bdd.node_count();
  // The candidate scope ends before policy generation and verification.
  candidate_stats.finish();
  if (candidate_only) {
    candidate.method = TLSF_GR1_CHECK_REGION;
    return candidate;
  }
  if (target.fold) {
    char unused[TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE]{};
    verify_fold(trusted, candidate, cfg,
                SeedDeclines{fold_detail ? fold_detail : unused});
    return candidate;
  }
  TlsfGr1CheckStatus region_capacity_status = TLSF_GR1_CHECK_OK;
  TlsfGr1LiftStatus policy_capacity_status = TLSF_GR1_LIFT_LIMIT;
  auto try_region = [&]() {
    cfg.check("region_check");
    auto result = check(trusted, candidate, cfg, TLSF_GR1_CHECK_REGION,
                        cfg.o.deadline_mono_ns);
    const auto status = result.status;
    const auto verdict = result.verdict;
    if (status == TLSF_GR1_CHECK_OK &&
        verdict == TLSF_GR1_CHECK_REGION_VERIFIED) {
      candidate.method = TLSF_GR1_CHECK_REGION;
      candidate.verdict = verdict;
      if (result.json)
        candidate.check_json.assign(result.json, result.json_size);
      candidate.policy.clear();
      candidate.policy_json.clear();
    }
    tlsf_gr1_check_result_clear(&result);
    if (candidate.verdict == TLSF_GR1_CHECK_REGION_VERIFIED)
      return true;
    if (status == TLSF_GR1_CHECK_CANCELLED)
      throw Failure(TLSF_GR1_LIFT_CANCELLED, FailureCause::cancelled,
                    "region_check", "checker cancelled");
    if (status == TLSF_GR1_CHECK_LIMIT || status == TLSF_GR1_CHECK_DEADLINE) {
      region_capacity_status = status;
      return false;
    }
    // REGION_FAILED means the proposed certificate failed this proof method.
    // Do not turn it into an UNREAL result or spend policy work on it.
    decline(check_failure_cause(status, verdict),
            status == TLSF_GR1_CHECK_OK ? "target_check" : "checker_error",
            "region not verified");
  };
  auto try_policy = [&]() {
    cfg.check("policy");
    uint64_t now = now_ns();
    Config policy_cfg = cfg;
    policy_cfg.phase_deadline_ns = cfg.policy_proof_ns > UINT64_MAX - now
                                       ? UINT64_MAX
                                       : now + cfg.policy_proof_ns;
    policy_cfg.max_bdd_ops = cfg.max_policy_bdd_ops;
    try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
      if (lift_test_fault == 4 && cfg.o.deadline_mono_ns) {
        lift_test_fallback_started_before_deadline =
            now_ns() < cfg.o.deadline_mono_ns;
        while (now_ns() < cfg.o.deadline_mono_ns)
          std::this_thread::sleep_for(std::chrono::milliseconds(1));
        policy_cfg.check("policy");
      }
#endif
      StatsScope policy_stats(cfg, TLSF_GR1_LIFT_STATS_POLICY_EXPORT);
      bdd.begin_phase(policy_cfg);
      policy_stats.count_bdd_ops(bdd.operation_counter());
      auto policy = emit_policy(bdd, target, cert.get(), policy_cfg);
      candidate.policy = render_aig(policy.get(), policy_cfg);
      candidate.policy_json =
          dump(policy_sidecar(target, policy.get(), semantics));
      policy_cfg.bytes(candidate.policy_json.size(), "policy");
      if (cfg.stats)
        cfg.stats->policy_bytes =
            candidate.policy.size() + candidate.policy_json.size();
      policy_stats.finish();
      auto result =
          check(trusted, candidate, policy_cfg, TLSF_GR1_CHECK_CERTIFICATE,
                policy_cfg.effective_deadline());
      const auto status = result.status;
      const auto verdict = result.verdict;
      if (status == TLSF_GR1_CHECK_OK && verdict == TLSF_GR1_CHECK_VERIFIED) {
        candidate.method = TLSF_GR1_CHECK_CERTIFICATE;
        candidate.verdict = verdict;
        if (result.json)
          candidate.check_json.assign(result.json, result.json_size);
      }
      tlsf_gr1_check_result_clear(&result);
      if (candidate.verdict == TLSF_GR1_CHECK_VERIFIED) {
        bdd.set_config(cfg);
        return true;
      }
      if (status == TLSF_GR1_CHECK_CANCELLED)
        throw Failure(TLSF_GR1_LIFT_CANCELLED, FailureCause::cancelled,
                      "target_check", "checker cancelled");
      if (status != TLSF_GR1_CHECK_LIMIT && status != TLSF_GR1_CHECK_DEADLINE)
        decline(check_failure_cause(status, verdict),
                status == TLSF_GR1_CHECK_OK ? "target_check" : "checker_error",
                "certificate not verified");
      if (status == TLSF_GR1_CHECK_DEADLINE && cfg.o.deadline_mono_ns &&
          now_ns() >= cfg.o.deadline_mono_ns)
        policy_capacity_status = TLSF_GR1_LIFT_DEADLINE;
    } catch (const Failure &e) {
      bdd.set_config(cfg);
      if (e.status == TLSF_GR1_LIFT_LIMIT ||
          e.status == TLSF_GR1_LIFT_DEADLINE) {
        policy_capacity_status = e.status;
        return false;
      }
      throw;
    }
    bdd.set_config(cfg);
    return false;
  };
  if (cfg.o.proof_order == TLSF_GR1_LIFT_REGION_FIRST) {
    if (try_region() || try_policy())
      return candidate;
    cfg.check("target_check");
    throw Failure(policy_capacity_status, failure_cause(policy_capacity_status),
                  "target_check", "region and policy proof budgets exhausted");
  }
  if (try_policy() || try_region())
    return candidate;
  throw Failure(region_capacity_status == TLSF_GR1_CHECK_DEADLINE
                    ? TLSF_GR1_LIFT_DEADLINE
                    : TLSF_GR1_LIFT_LIMIT,
                failure_cause(region_capacity_status == TLSF_GR1_CHECK_DEADLINE
                                  ? TLSF_GR1_LIFT_DEADLINE
                                  : TLSF_GR1_LIFT_LIMIT),
                "region_check", "checker capacity or deadline");
}
char *copy_bytes(const std::string &value) {
  if (value.size() == SIZE_MAX)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "publish-size",
                  "artifact size overflow");
  char *p = (char *)malloc(value.size() + 1);
  if (!p)
    throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, "publish",
                  "cannot allocate result");
  memcpy(p, value.data(), value.size());
  p[value.size()] = '\0';
  return p;
}
TlsfGr1LiftOptions defaults(const TlsfGr1LiftOptions *provided) {
  TlsfGr1LiftOptions out{};
  if (provided)
    out = *provided;
  if (!out.solver_nodes)
    out.solver_nodes = TLSF_GR1_LIFT_DEFAULT_SOLVER_NODES;
  if (!out.solver_cache)
    out.solver_cache = TLSF_GR1_LIFT_DEFAULT_SOLVER_CACHE;
  if (!out.checker_nodes)
    out.checker_nodes = TLSF_GR1_LIFT_DEFAULT_CHECKER_NODES;
  if (!out.checker_cache)
    out.checker_cache = TLSF_GR1_LIFT_DEFAULT_CHECKER_CACHE;
  if (!out.schema_nodes)
    out.schema_nodes = TLSF_GR1_LIFT_DEFAULT_SCHEMA_NODES;
  if (!out.schema_cache)
    out.schema_cache = TLSF_GR1_LIFT_DEFAULT_SCHEMA_CACHE;
  if (!out.max_artifact_bytes)
    out.max_artifact_bytes = TLSF_GR1_LIFT_DEFAULT_MAX_ARTIFACT_BYTES;
  if (!out.max_monitor_states)
    out.max_monitor_states = TLSF_GR1_LIFT_DEFAULT_MAX_MONITOR_STATES;
  if (!out.max_sizes_per_axis)
    out.max_sizes_per_axis = TLSF_GR1_LIFT_DEFAULT_MAX_SIZES_PER_AXIS;
  if (!out.max_predicate_arity)
    out.max_predicate_arity = TLSF_GR1_LIFT_DEFAULT_MAX_PREDICATE_ARITY;
  if (!out.max_subsets_per_predicate)
    out.max_subsets_per_predicate =
        TLSF_GR1_LIFT_DEFAULT_MAX_SUBSETS_PER_PREDICATE;
  return out;
}
TrustedTarget prepare(const uint8_t *source, size_t size,
                      const std::map<std::string, int64_t> &overrides,
                      const Config &cfg, bool exact_only = false,
                      bool allow_no_parameters = false) {
  TrustedTarget trusted;
  trusted.snapshot.assign(reinterpret_cast<const char *>(source), size);
  source = reinterpret_cast<const uint8_t *>(trusted.snapshot.data());
  StatsScope source_stats(cfg, TLSF_GR1_LIFT_STATS_SOURCE);
  cfg.check("source");
  char source_hash[65]{};
  if (!tlsf_pipeline_source_sha256(source, size, source_hash))
    throw Failure(TLSF_GR1_LIFT_INVALID, FailureCause::invalid, "source",
                  "invalid byte snapshot or embedded NUL");
  int declared_parameters = tlsf_source_parameter_count(source, size);
  if (declared_parameters < 0)
    decline(FailureCause::error, "parse", "source parse failed");
  if (declared_parameters == 0 && !allow_no_parameters)
    decline(FailureCause::applicability, "parameters", "absent");
  trusted.source_hash = source_hash;
  source_stats.finish();
  StatsScope target_stats(cfg, TLSF_GR1_LIFT_STATS_TARGET_REDUCE);
  try {
    trusted.instance = lower(source, size, overrides, trusted.semantics, cfg);
  } catch (const Failure &e) {
    if (exact_only || (e.status != TLSF_GR1_LIFT_DECLINED &&
                       e.status != TLSF_GR1_LIFT_UNSUPPORTED))
      throw;
    trusted.semantics = TLSF_GR1_STRICT;
    try {
      trusted.instance = lower(source, size, overrides, trusted.semantics, cfg);
    } catch (const Failure &retry) {
      if (!is_applicability(e.cause) && is_applicability(retry.cause))
        throw Failure(retry.status, e.cause, retry.stage, retry.what());
      throw;
    }
  }
  target_stats.finish();
  if (cfg.stats) {
    cfg.stats->target_latches = aig_num_latches(trusted.instance->r.game);
    cfg.stats->target_ands = aig_num_ands(trusted.instance->r.game);
  }
  trusted.game_aag.assign(trusted.instance->r.aag,
                          trusted.instance->r.aag_size);
  char game_hash[65]{};
  sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), game_hash);
  trusted.game_hash = game_hash;
  return trusted;
}
void run(const TrustedTarget &trusted, const Config &cfg,
         TlsfGr1LiftResult &result, Window *shared_window = nullptr,
         bool candidate_only = false, uint64_t *seed_checks = nullptr) {
  bool folding = false, parametric = false;
  try {
    BothPhase phase("native_r_candidate", trusted.game_hash.c_str());
    const auto *source =
        reinterpret_cast<const uint8_t *>(trusted.snapshot.data());
    const size_t size = trusted.snapshot.size();
    const auto &source_hash = trusted.source_hash;
    const auto semantics = trusted.semantics;
    const auto &target = trusted.instance;
    auto axes = parameters(*target);
    if (axes.empty())
      decline(FailureCause::applicability, "parameters", "absent");
    Config discovery_cfg = cfg;
    StatsScope window_stats(cfg, TLSF_GR1_LIFT_STATS_SEED_WINDOW);
    auto window = shared_window ? std::move(*shared_window)
                                : discover(source, size, *target, semantics,
                                           discovery_cfg,
                                           SeedDeclines{result.decline_detail});
    folding = window.fold;
    parametric = window.param;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if ((folding && lift_test_fault == 11) ||
        (parametric && lift_test_fault == 23))
      throw std::bad_alloc();
    if (lift_test_fault == 1 && !window.sizes.empty())
      window.sizes[0]++;
#endif
    if (!window.fold)
      validate_window(window, *target);
    else if (window.seeds.size() < 2 || trusted.semantics != TLSF_GR1_EXACT)
      decline(FailureCause::applicability, "fold_discovery",
              "fold_no_candidate");
    window_stats.finish();
    if (cfg.stats) {
      cfg.stats->seeds_selected = window.seeds.size();
      for (const auto &seed : window.seeds) {
        cfg.stats->seed_latches += aig_num_latches(seed->r.game);
        cfg.stats->seed_ands += aig_num_ands(seed->r.game);
      }
    }
    if (!shared_window)
      for (auto &seed : window.seeds) {
        StatsScope solve_stats(cfg, TLSF_GR1_LIFT_STATS_SEED_SOLVE);
        if (cfg.stats)
          cfg.stats->seed_solves++;
        solve_seed(*seed, discovery_cfg, window.fold);
      }
    std::vector<GameView> seeds;
    seeds.reserve(window.seeds.size());
    for (auto &seed : window.seeds)
      seeds.emplace_back(*seed, window.modes, discovery_cfg, nullptr,
                         window.fold);
    GameView target_view(*target, window.modes, discovery_cfg,
                         &window.target_members, window.fold);
    uint32_t width = uint32_t(target_view.variables.size());
    for (const auto &seed : seeds)
      width = std::max(width, uint32_t(seed.variables.size()));
    Schema bdd(discovery_cfg, width);
    StatsScope schema_stats(cfg, TLSF_GR1_LIFT_STATS_SCHEMA_LEARNING);
    schema_stats.count_bdd_ops(bdd.operation_counter());
    LearnedCertificate learned;
    O fold_evidence;
    if (window.param) {
      fold_evidence = bind_param(bdd, seeds, target_view, cfg);
      learned =
          learn_param(bdd, seeds, target_view, discovery_cfg, fold_evidence);
    } else if (window.fold) {
      auto rule = learn_fold(bdd, seeds, target_view, discovery_cfg);
      fold_evidence = validate_fold_seeds(bdd, seeds, rule, window.axis,
                                          discovery_cfg, seed_checks);
      learned = instantiate_fold(bdd, target_view, rule);
    } else
      learned = learn_certificate(bdd, seeds, target_view, discovery_cfg);
    if (cfg.stats)
      cfg.stats->schema_nodes_after_learning = bdd.node_count();
    schema_stats.finish();
    bdd.set_config(cfg);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 5 && aig_num_latches(target->r.game)) {
      uint32_t current, next;
      aig_latch_at(target->r.game, 0, &current, &next, nullptr);
      if (!aig_set_latch_next(target->r.game, current, aig_not(next)))
        throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "candidate",
                      "fault hook could not mutate the game");
    }
#endif
    Candidate candidate = prove(bdd, target_view, learned, trusted, cfg,
                                candidate_only, result.decline_detail);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (lift_test_fault == 7 && !candidate_only)
      candidate.verdict = TLSF_GR1_CHECK_UNKNOWN;
#endif
    if (!candidate_only && candidate.verdict != TLSF_GR1_CHECK_VERIFIED &&
        candidate.verdict != TLSF_GR1_CHECK_REGION_VERIFIED)
      decline(FailureCause::error, "target_check", "unverified candidate");
    StatsScope publish_stats(cfg, TLSF_GR1_LIFT_STATS_PUBLISH);
    cfg.check("publish");
    cfg.bytes(candidate.game.size(), "publish");
    cfg.bytes(candidate.certificate.size(), "publish");
    cfg.bytes(candidate.certificate_json.size(), "publish");
    cfg.bytes(candidate.policy.size(), "publish");
    cfg.bytes(candidate.policy_json.size(), "publish");
    cfg.bytes(candidate.check_json.size(), "publish");
    char game_hash[65]{}, cert_hash[65]{}, policy_hash[65]{};
    if (!tlsf_pipeline_source_sha256(candidate.game.data(),
                                     candidate.game.size(), game_hash) ||
        !tlsf_pipeline_source_sha256(candidate.certificate.data(),
                                     candidate.certificate.size(), cert_hash))
      throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "publish",
                    "artifact hash failed");
    if (candidate.method == TLSF_GR1_CHECK_CERTIFICATE &&
        (candidate.policy.empty() ||
         !tlsf_pipeline_source_sha256(candidate.policy.data(),
                                      candidate.policy.size(), policy_hash)))
      throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "publish",
                    "policy artifact hash failed");
    A values, roles;
    for (int v : window.sizes)
      values.emplace_back(v);
    for (const auto &[index, role] : target_view.roles)
      roles.emplace_back(O{{"index", index}, {"signature", role}});
    O arities;
    for (const auto &[name, arity] : learned.arities)
      arities[name] = arity;
    J evidence =
        O{{"format", TLSF_GR1_LIFT_EVIDENCE_FORMAT},
          {"source_sha256", source_hash},
          {"game_sha256", game_hash},
          {"certificate_sha256", cert_hash},
          {"axis", window.axis},
          {"seed_values", values},
          {"roles", roles},
          {"predicate_arities", arities},
          {"move_source", "target_transition"},
          {"reduction_semantics",
           semantics == TLSF_GR1_EXACT ? "exact" : "strict"},
          {"method", candidate.method == TLSF_GR1_CHECK_REGION ? "gr1-region-v1"
                                                               : "certificate"},
          {"verdict", candidate_only ? "UNKNOWN"
                      : candidate.method == TLSF_GR1_CHECK_REGION
                          ? "REGION_VERIFIED"
                          : "VERIFIED"},
          {"global_knobs",
           O{{"max_sizes_per_axis", cfg.o.max_sizes_per_axis},
             {"max_predicate_arity", cfg.o.max_predicate_arity},
             {"max_subsets_per_predicate", cfg.o.max_subsets_per_predicate},
             {"seed_confirmation", cfg.o.seed_confirmation != 2},
             {"max_seed_probes", cfg.max_seed_probes},
             {"max_discovery_bdd_ops", cfg.max_bdd_ops},
             {"max_policy_bdd_ops", cfg.max_policy_bdd_ops},
             {"policy_proof_ns", cfg.policy_proof_ns},
             {"solver_nodes", cfg.o.solver_nodes},
             {"solver_cache", cfg.o.solver_cache},
             {"checker_nodes", cfg.o.checker_nodes},
             {"checker_cache", cfg.o.checker_cache},
             {"schema_nodes", cfg.o.schema_nodes},
             {"schema_cache", cfg.o.schema_cache}}}};
    if (candidate.method == TLSF_GR1_CHECK_CERTIFICATE)
      evidence.as_object()["policy_sha256"] = policy_hash;
    if (window.fold) {
      fold_evidence["discovery_probes"] = window.fold_probes;
      fold_evidence["discovery_reductions"] = window.fold_reductions;
      evidence.as_object()["fold"] = fold_evidence;
      if (!candidate_only)
        evidence.as_object()["checker_order"] = candidate.checker_order;
    }
    candidate.evidence = dump(evidence);
    cfg.bytes(candidate.evidence.size(), "publish");
    result.game_size = candidate.game.size();
    result.game_aag = copy_bytes(candidate.game);
    result.certificate_size = candidate.certificate.size();
    result.certificate_aag = copy_bytes(candidate.certificate);
    result.certificate_json_size = candidate.certificate_json.size();
    result.certificate_json = copy_bytes(candidate.certificate_json);
    result.policy_size = candidate.policy.size();
    if (!candidate.policy.empty())
      result.policy_aag = copy_bytes(candidate.policy);
    result.policy_json_size = candidate.policy_json.size();
    if (!candidate.policy_json.empty())
      result.policy_json = copy_bytes(candidate.policy_json);
    result.check_json_size = candidate.check_json.size();
    result.check_json = copy_bytes(candidate.check_json);
    result.evidence_size = candidate.evidence.size();
    result.evidence_json = copy_bytes(candidate.evidence);
    result.semantics = semantics;
    result.method = candidate.method;
    result.verdict = candidate.verdict;
  } catch (const Failure &e) {
    if (folding) {
      SeedDeclines log{result.decline_detail};
      log.at("fold");
      log.note(parametric ? "param_failed" : "fold_failed");
      log.failure(e);
    }
    throw;
  } catch (const std::bad_alloc &) {
    if (folding) {
      SeedDeclines log{result.decline_detail};
      log.note(parametric ? "param_failed" : "fold_failed");
      log.exception("fold", "resource", "host allocation failed");
    }
    throw;
  } catch (const std::exception &e) {
    if (folding) {
      SeedDeclines log{result.decline_detail};
      log.note(parametric ? "param_failed" : "fold_failed");
      log.exception("fold", "error", e.what());
    }
    throw;
  }
}
} // namespace gr1_lift_internal

struct TlsfGr1LiftTarget {
  TrustedTarget trusted;
  std::string prepared_seal;
  mutable std::array<std::string, 7> checked_hashes;
  mutable TlsfGr1CheckMethod checked_method = TLSF_GR1_CHECK_CERTIFICATE;
  mutable TlsfGr1CheckVerdict checked_verdict = TLSF_GR1_CHECK_UNKNOWN;
};

namespace gr1_lift_internal {
Config lift_config(const TlsfGr1LiftOptions *options) {
  Config cfg{defaults(options)};
  static const TlsfGr1ConstructionBudget empty_budget{};
  cfg.budget = options ? &options->budget : &empty_budget;
  cfg.stats = options ? options->stats : nullptr;
  cfg.work = cfg.stats ? &cfg.stats->work : nullptr;
  cfg.stats_callback = cfg.o.stats_callback;
  cfg.stats_context = cfg.o.stats_context;
  const auto &phase = cfg.o.phase_budget;
  if (phase.max_seed_probes)
    cfg.max_seed_probes = phase.max_seed_probes;
  if (phase.max_discovery_bdd_ops)
    cfg.max_bdd_ops = phase.max_discovery_bdd_ops;
  if (phase.max_policy_bdd_ops)
    cfg.max_policy_bdd_ops = phase.max_policy_bdd_ops;
  if (phase.policy_proof_ns)
    cfg.policy_proof_ns = phase.policy_proof_ns;
  return cfg;
}
void lift_error(TlsfGr1LiftError *error, TlsfGr1LiftStats *stats,
                TlsfGr1LiftStatus status, const char *stage,
                const char *message) {
  if (stats)
    snprintf(stats->final_stage, sizeof stats->final_stage, "%s", stage);
  if (error) {
    error->status = status;
    snprintf(error->stage, sizeof error->stage, "%s", stage);
    snprintf(error->message, sizeof error->message, "%s", message);
  }
}
template <typename Action>
TlsfGr1LiftStatus invoke_lift(Action action, TlsfGr1LiftError *error,
                              TlsfGr1LiftStats *stats,
                              TlsfGr1LiftStatus *failure_status = nullptr) {
  if (error)
    memset(error, 0, sizeof *error);
  try {
    action();
    if (error)
      error->status = TLSF_GR1_LIFT_OK;
    return TLSF_GR1_LIFT_OK;
  } catch (const Failure &e) {
    lift_error(error, stats, e.status, e.stage.c_str(), e.what());
    if (failure_status)
      *failure_status = e.failure_status;
    return e.status;
  } catch (const std::bad_alloc &) {
    if (failure_status)
      *failure_status = diagnostic_status(FailureCause::resource);
    lift_error(error, stats, TLSF_GR1_LIFT_LIMIT, "allocation",
               "host allocation failed");
    return TLSF_GR1_LIFT_LIMIT;
  } catch (const std::exception &e) {
    if (failure_status)
      *failure_status = diagnostic_status(FailureCause::error);
    lift_error(error, stats, TLSF_GR1_LIFT_ERROR, "internal", e.what());
    return TLSF_GR1_LIFT_ERROR;
  } catch (...) {
    if (failure_status)
      *failure_status = diagnostic_status(FailureCause::error);
    lift_error(error, stats, TLSF_GR1_LIFT_ERROR, "internal",
               "unknown exception");
    return TLSF_GR1_LIFT_ERROR;
  }
}
std::map<std::string, int64_t> lift_overrides(const ParamOverride *rows,
                                              size_t count) {
  std::map<std::string, int64_t> overrides;
  for (size_t p = 0; p < count; p++) {
    const auto &row = rows[p];
    if (!row.name || !*row.name ||
        !overrides.emplace(row.name, row.value).second)
      throw Failure(TLSF_GR1_LIFT_INVALID, FailureCause::invalid, "override",
                    "empty or duplicate target override");
  }
  return overrides;
}
std::array<std::string, 7> result_hashes(const TlsfGr1LiftResult &result) {
  const std::array<std::pair<const char *, size_t>, 7> artifacts{
      {{result.game_aag, result.game_size},
       {result.certificate_aag, result.certificate_size},
       {result.certificate_json, result.certificate_json_size},
       {result.policy_aag, result.policy_size},
       {result.policy_json, result.policy_json_size},
       {result.check_json, result.check_json_size},
       {result.evidence_json, result.evidence_size}}};
  std::array<std::string, 7> hashes;
  for (size_t i = 0; i < artifacts.size(); i++) {
    const auto &[bytes, size] = artifacts[i];
    if (!bytes && size)
      return {};
    char digest[65]{};
    sha256_hex(bytes ? bytes : "", size, digest);
    hashes[i] = digest;
  }
  return hashes;
}

void both_decline(TlsfGr1BothResult &out, const char *stage) noexcept {
  if (!out.decline_stage[0])
    snprintf(out.decline_stage, sizeof out.decline_stage, "%s", stage);
  size_t used = strlen(out.decline_stages);
  if (used < sizeof out.decline_stages - 1)
    snprintf(out.decline_stages + used, sizeof out.decline_stages - used,
             "%s%s", used ? "," : "", stage);
}

Candidate direct_candidate(const TrustedTarget &trusted, const Config &cfg) {
  BothPhase phase("native_direct_solve", trusted.game_hash.c_str());
  cfg.check("direct_solve");
  auto game = parse_aig(trusted.game_aag.data(), trusted.game_aag.size());
  OxiddFailure failure{};
  char *cert = nullptr, *meta = nullptr, *policy = nullptr,
       *policy_meta = nullptr;
  size_t cert_size = 0, meta_size = 0, policy_size = 0, policy_meta_size = 0;
  Gr1CertificateOptions export_options{};
  export_options.semantics = GR1_CERTIFICATE_SEMANTICS_EXACT;
  export_options.aag_bytes = &cert;
  export_options.aag_size = &cert_size;
  export_options.json_bytes = &meta;
  export_options.json_size = &meta_size;
  export_options.policy_aag_bytes = &policy;
  export_options.policy_aag_size = &policy_size;
  export_options.policy_json_bytes = &policy_meta;
  export_options.policy_json_size = &policy_meta_size;
  export_options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  Gr1SolveOptions options{};
  options.oxidd = oxidd_solve_options_default();
  options.oxidd.node_cap = 1u << 22;
  options.oxidd.cache_cap = 1u << 20;
  options.oxidd.deadline_mono_ns = cfg.o.deadline_mono_ns;
  options.oxidd.cancelled = cfg.o.cancelled;
  options.oxidd.cancel_ctx = cfg.o.cancel_ctx;
  options.oxidd.max_artifact_bytes = cfg.o.max_artifact_bytes;
  options.oxidd.failure = &failure;
  options.certificate = &export_options;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd(game.release(), &unreal, &options);
  const bool real = strategy && !unreal;
  aig_free(strategy);
  std::unique_ptr<char, decltype(&free)> cert_owner(cert, &free),
      meta_owner(meta, &free), policy_owner(policy, &free),
      policy_meta_owner(policy_meta, &free);
  if (failure.kind == OXIDD_FAILURE_DEADLINE)
    throw Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline,
                  "direct_solve", "deadline exceeded");
  cfg.check("direct_solve");
  if (failure.kind != OXIDD_FAILURE_NONE || export_options.failed ||
      (!real && !unreal) || !cert || !meta || !policy || !policy_meta)
    throw Failure(TLSF_GR1_LIFT_DECLINED, solver_failure_cause(failure.kind),
                  "direct_solve", "direct exact proof unavailable");
  Candidate candidate;
  candidate.game = trusted.game_aag;
  candidate.certificate.assign(cert, cert_size);
  candidate.certificate_json.assign(meta, meta_size);
  candidate.policy.assign(policy, policy_size);
  candidate.policy_json.assign(policy_meta, policy_meta_size);
  candidate.method = TLSF_GR1_CHECK_CERTIFICATE;
  candidate.verdict = TLSF_GR1_CHECK_UNKNOWN;
  return candidate;
}

void both_check(const TrustedTarget &trusted, const Config &cfg,
                Candidate &candidate, bool unreal, TlsfGr1BothResult &out) {
  BothPhase phase("native_target_check", trusted.game_hash.c_str());
  cfg.check("target_check");
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if ((both_test_check_fault == 1 &&
       candidate.method == TLSF_GR1_CHECK_REGION) ||
      (both_test_check_fault == 2 &&
       candidate.method == TLSF_GR1_CHECK_CERTIFICATE))
    const_cast<TrustedTarget &>(trusted).game_aag[0] = 'X';
#endif
  char hash[65]{};
  sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), hash);
  if (trusted.game_hash != hash ||
      trusted.game_aag !=
          std::string(trusted.instance->r.aag, trusted.instance->r.aag_size))
    decline(FailureCause::error, "target_binding",
            "prepared game changed before verification");
  if (candidate.fold) {
    SeedDeclines log{out.decline_detail};
    log.at("fold");
    verify_fold(trusted, candidate, cfg, log, &out.target_checks);
  } else {
    auto checked =
        check(trusted, candidate, cfg, candidate.method, cfg.o.deadline_mono_ns,
              TLSF_GR1_CHECK_VAR_ORDER_AUTO, &out.target_checks);
    const auto status = checked.status;
    const auto verdict = checked.verdict;
    const auto expected = candidate.method == TLSF_GR1_CHECK_REGION
                              ? TLSF_GR1_CHECK_REGION_VERIFIED
                              : TLSF_GR1_CHECK_VERIFIED;
    const bool verified =
        status == TLSF_GR1_CHECK_OK && checked.verdict == expected;
    if (verified) {
      candidate.verdict = checked.verdict;
      if (checked.json)
        candidate.check_json.assign(checked.json, checked.json_size);
    }
    tlsf_gr1_check_result_clear(&checked);
    if (status == TLSF_GR1_CHECK_DEADLINE && cfg.o.deadline_mono_ns &&
        now_ns() >= cfg.o.deadline_mono_ns)
      throw Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline,
                    "target_check", "deadline exceeded");
    if (!verified) {
      const auto cause = check_failure_cause(status, verdict);
      throw Failure(TLSF_GR1_LIFT_DECLINED, cause, "target_check",
                    "candidate proof did not verify");
    }
  }
  const O metadata = j::parse(candidate.certificate_json).as_object();
  if (s(metadata, "side") != (unreal ? "environment" : "system"))
    decline(FailureCause::error, "target_check",
            "certificate side differs from route");
}

void publish_both(const TrustedTarget &trusted, const Candidate &candidate,
                  TlsfGr1BothResult &out) {
  char cert_hash[65]{}, policy_hash[65]{};
  sha256_hex(candidate.certificate.data(), candidate.certificate.size(),
             cert_hash);
  if (!candidate.policy.empty())
    sha256_hex(candidate.policy.data(), candidate.policy.size(), policy_hash);
  const char *route = out.route == TLSF_GR1_BOTH_REAL_LIFT  ? "R"
                      : out.route == TLSF_GR1_BOTH_ENV_LIFT ? "U"
                                                            : "direct";
  const char *polarity = out.seed_polarity == TLSF_GR1_SEEDS_REAL     ? "REAL"
                         : out.seed_polarity == TLSF_GR1_SEEDS_UNREAL ? "UNREAL"
                         : out.seed_polarity == TLSF_GR1_SEEDS_MIXED  ? "mixed"
                         : out.seed_polarity == TLSF_GR1_SEEDS_UNKNOWN
                             ? "unknown"
                             : "none";
  J evidence =
      O{{"format", TLSF_GR1_LIFT_EVIDENCE_FORMAT},
        {"source_sha256", trusted.source_hash},
        {"game_sha256", trusted.game_hash},
        {"certificate_sha256", cert_hash},
        {"reduction_semantics", "exact"},
        {"method", candidate.method == TLSF_GR1_CHECK_REGION ? "gr1-region-v1"
                                                             : "certificate"},
        {"verdict", candidate.verdict == TLSF_GR1_CHECK_REGION_VERIFIED
                        ? "REGION_VERIFIED"
                        : "VERIFIED"},
        {"move_source", "target_transition"},
        {"route", route},
        {"seed_polarity", polarity},
        {"decline_stages", out.decline_stages},
        {"target_checks", out.target_checks},
        {"target_reductions", out.target_reductions},
        {"seed_probes", out.seed_probes},
        {"seed_reductions", out.seed_reductions},
        {"seed_solves", out.seed_solves},
        {"seed_checks", out.seed_checks},
        {"seed_cache_hits", out.seed_cache_hits}};
  if (!candidate.policy.empty())
    evidence.as_object()["policy_sha256"] = policy_hash;
  if (candidate.fold) {
    evidence.as_object()["fold"] = candidate.fold_evidence;
    evidence.as_object()["checker_order"] = candidate.checker_order;
  }
  auto &proof = out.proof;
  proof.game_size = candidate.game.size();
  proof.game_aag = copy_bytes(candidate.game);
  proof.certificate_size = candidate.certificate.size();
  proof.certificate_aag = copy_bytes(candidate.certificate);
  proof.certificate_json_size = candidate.certificate_json.size();
  proof.certificate_json = copy_bytes(candidate.certificate_json);
  proof.policy_size = candidate.policy.size();
  if (!candidate.policy.empty())
    proof.policy_aag = copy_bytes(candidate.policy);
  proof.policy_json_size = candidate.policy_json.size();
  if (!candidate.policy_json.empty())
    proof.policy_json = copy_bytes(candidate.policy_json);
  proof.check_json_size = candidate.check_json.size();
  if (!candidate.check_json.empty())
    proof.check_json = copy_bytes(candidate.check_json);
  std::string evidence_bytes = dump(evidence);
  proof.evidence_size = evidence_bytes.size();
  proof.evidence_json = copy_bytes(evidence_bytes);
  proof.semantics = TLSF_GR1_EXACT;
  proof.method = candidate.method;
  proof.verdict = candidate.verdict;
}

} // namespace gr1_lift_internal

#ifdef TLSF_GR1_LIFT_TEST_FAULT
/* Compiled only into native_lift_api, never into the installed library. */
extern "C" void tlsf_gr1_lift_test_set_fault(int fault) {
  lift_test_fault = fault;
  lift_test_reduction_calls = 0;
  lift_test_check_json_clears = 0;
  lift_test_generated_certificate_json.clear();
  lift_test_checked_game_aag.clear();
  lift_test_fallback_started_before_deadline = false;
}
extern "C" void tlsf_gr1_lift_test_set_param_activation(
    void (*callback)(TlsfGr1LiftOptions *)) {
  lift_test_param_activation = callback;
}
extern "C" void
tlsf_gr1_lift_test_set_axis_scan(void (*callback)(TlsfGr1LiftOptions *, bool)) {
  lift_test_axis_scan = callback;
}
extern "C" unsigned tlsf_gr1_lift_test_check_json_clears() {
  return lift_test_check_json_clears;
}
extern "C" uint64_t tlsf_gr1_lift_test_reduction_calls() {
  return lift_test_reduction_calls;
}
extern "C" void tlsf_gr1_both_test_set_seed_fault(int fault) {
  both_test_seed_fault = fault;
}
extern "C" void tlsf_gr1_both_test_set_candidate_ns(uint64_t duration) {
  both_test_candidate_ns = duration;
}
extern "C" void tlsf_gr1_both_test_set_check_fault(int fault) {
  both_test_check_fault = fault;
}
extern "C" void tlsf_gr1_both_test_set_env_rss_spike(size_t bytes) {
  both_test_env_rss_spike_bytes = bytes;
}
extern "C" const char *tlsf_gr1_lift_test_generated_certificate_json() {
  return lift_test_generated_certificate_json.c_str();
}
extern "C" int tlsf_gr1_lift_test_fallback_started_before_deadline() {
  return lift_test_fallback_started_before_deadline;
}
extern "C" int tlsf_gr1_lift_test_checked_game_equals(const char *bytes,
                                                      size_t size) {
  return lift_test_checked_game_aag.size() == size &&
         !memcmp(lift_test_checked_game_aag.data(), bytes, size);
}
extern "C" int
tlsf_gr1_lift_test_prepared_game_equals(const TlsfGr1LiftTarget *target,
                                        const char *bytes, size_t size) {
  return target && target->trusted.game_aag.size() == size &&
         !memcmp(target->trusted.game_aag.data(), bytes, size);
}
extern "C" unsigned
tlsf_gr1_lift_test_pair_monitors(const TlsfGr1LiftTarget *target) {
  std::set<std::string> families;
  const A &monitors = target->trusted.instance->data.at("monitors").as_array();
  for (const J &v : monitors) {
    const O &o = v.as_object().at("source_origin").as_object();
    if (o.at("bindings").as_array().size() == 2)
      families.insert(s(o, "source_formula_id"));
  }
  unsigned count = 0;
  // Singleton expansion drops the inner binder on the final ordered pair.
  for (const J &v : monitors)
    count += families.count(
        s(v.as_object().at("source_origin").as_object(), "source_formula_id"));
  return count;
}
extern "C" void
tlsf_gr1_lift_test_corrupt_prepared_game(TlsfGr1LiftTarget *target) {
  if (target && !target->trusted.game_aag.empty())
    target->trusted.game_aag[0] = 'X';
}
extern "C" void tlsf_gr1_env_test_swap_rehashed_game(TlsfGr1LiftTarget *target,
                                                     TlsfGr1LiftTarget *other) {
  if (!target || !other)
    return;
  auto &trusted = target->trusted;
  auto &left = trusted.instance->r;
  auto &right = other->trusted.instance->r;
  std::swap(left.game, right.game);
  std::swap(left.aag, right.aag);
  std::swap(left.aag_size, right.aag_size);
  trusted.game_aag.assign(trusted.instance->r.aag,
                          trusted.instance->r.aag_size);
  char hash[65]{};
  sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), hash);
  trusted.game_hash = hash;
  O metadata = j::parse(std::string_view(trusted.instance->r.metadata_json,
                                         trusted.instance->r.metadata_size))
                   .as_object();
  metadata["game_sha256"] = trusted.game_hash;
  std::string updated = dump(metadata);
  free(trusted.instance->r.metadata_json);
  trusted.instance->r.metadata_json = copy_bytes(updated);
  trusted.instance->r.metadata_size = updated.size();
}
#endif

extern "C" void tlsf_gr1_lift_result_clear(TlsfGr1LiftResult *result) {
  if (!result)
    return;
  free(result->game_aag);
  free(result->certificate_aag);
  free(result->certificate_json);
  free(result->policy_aag);
  free(result->policy_json);
  free(result->check_json);
  free(result->evidence_json);
  memset(result, 0, sizeof *result);
  result->verdict = TLSF_GR1_CHECK_UNKNOWN;
}
extern "C" TlsfGr1LiftStatus
tlsf_gr1_lift(const uint8_t *source, size_t source_size,
              const ParamOverride *target_overrides,
              size_t target_override_count, const TlsfGr1LiftOptions *options,
              TlsfGr1LiftResult *result, TlsfGr1LiftError *error) {
  auto *stats = options ? options->stats : nullptr;
  if (stats)
    memset(stats, 0, sizeof *stats);
  if (!result) {
    lift_error(error, stats, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid arguments");
    return TLSF_GR1_LIFT_INVALID;
  }
  if (result->game_aag || result->certificate_aag || result->certificate_json ||
      result->policy_aag || result->policy_json || result->check_json ||
      result->evidence_json) {
    lift_error(error, stats, TLSF_GR1_LIFT_INVALID, "arguments",
               "result must be empty");
    return TLSF_GR1_LIFT_INVALID;
  }
  result->verdict = TLSF_GR1_CHECK_UNKNOWN;
  result->decline_detail[0] = '\0';
  TlsfGr1LiftTarget *target = nullptr;
  auto status = tlsf_gr1_lift_target_prepare(
      source, source_size, target_overrides, target_override_count, options,
      &target, error);
  if (status != TLSF_GR1_LIFT_OK)
    return status;
  status = tlsf_gr1_lift_from_target(target, options, result, error);
  tlsf_gr1_lift_target_free(target);
  return status;
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_lift_target_prepare_v1(
    const uint8_t *source, size_t source_size,
    const ParamOverride *target_overrides, size_t target_override_count,
    const TlsfGr1LiftOptions *options, TlsfGr1LiftTarget **target,
    TlsfGr1LiftError *error, TlsfGr1LiftStatus *failure_status) {
  if (failure_status)
    *failure_status = TLSF_GR1_LIFT_OK;
  auto *stats = options ? options->stats : nullptr;
  if (stats)
    memset(stats, 0, sizeof *stats);
  if (!target || *target || !source || !source_size ||
      (target_override_count && !target_overrides)) {
    lift_error(error, stats, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid arguments");
    if (failure_status)
      *failure_status = TLSF_GR1_LIFT_INVALID;
    return TLSF_GR1_LIFT_INVALID;
  }
  return invoke_lift(
      [&] {
        auto cfg = lift_config(options);
        if (cfg.o.proof_order != TLSF_GR1_LIFT_POLICY_FIRST &&
            cfg.o.proof_order != TLSF_GR1_LIFT_REGION_FIRST)
          throw Failure(TLSF_GR1_LIFT_INVALID, FailureCause::invalid,
                        "arguments", "invalid proof order");
        cfg.bytes(source_size, "source");
        auto overrides =
            lift_overrides(target_overrides, target_override_count);
        auto owned = std::make_unique<TlsfGr1LiftTarget>();
        owned->trusted = prepare(source, source_size, overrides, cfg);
        owned->prepared_seal = owned->trusted.game_hash;
        *target = owned.release();
      },
      error, stats, failure_status);
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_lift_target_prepare_exact_v1(
    const uint8_t *source, size_t source_size,
    const TlsfGr1LiftOptions *options, TlsfGr1LiftTarget **target,
    TlsfGr1LiftError *error, TlsfGr1LiftStatus *failure_status) {
  if (failure_status)
    *failure_status = TLSF_GR1_LIFT_OK;
  auto *stats = options ? options->stats : nullptr;
  if (stats)
    memset(stats, 0, sizeof *stats);
  if (!target || *target || !source || !source_size) {
    lift_error(error, stats, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid arguments");
    if (failure_status)
      *failure_status = TLSF_GR1_LIFT_INVALID;
    return TLSF_GR1_LIFT_INVALID;
  }
  return invoke_lift(
      [&] {
        auto cfg = lift_config(options);
        cfg.bytes(source_size, "source");
        auto owned = std::make_unique<TlsfGr1LiftTarget>();
        owned->trusted = prepare(source, source_size, {}, cfg, true, true);
        owned->prepared_seal = owned->trusted.game_hash;
        *target = owned.release();
      },
      error, stats, failure_status);
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_lift_target_prepare(
    const uint8_t *source, size_t source_size,
    const ParamOverride *target_overrides, size_t target_override_count,
    const TlsfGr1LiftOptions *options, TlsfGr1LiftTarget **target,
    TlsfGr1LiftError *error) {
  return tlsf_gr1_lift_target_prepare_v1(source, source_size, target_overrides,
                                         target_override_count, options, target,
                                         error, nullptr);
}
extern "C" TlsfGr1LiftStatus
tlsf_gr1_lift_target_prepare_exact(const uint8_t *source, size_t source_size,
                                   const TlsfGr1LiftOptions *options,
                                   TlsfGr1LiftTarget **target,
                                   TlsfGr1LiftError *error) {
  return tlsf_gr1_lift_target_prepare_exact_v1(source, source_size, options,
                                               target, error, nullptr);
}

extern "C" void tlsf_gr1_lift_target_free(TlsfGr1LiftTarget *target) {
  delete target;
}

extern "C" TlsfGr1LiftStatus
tlsf_gr1_lift_from_target_v1(const TlsfGr1LiftTarget *target,
                             const TlsfGr1LiftOptions *options,
                             TlsfGr1LiftResult *result, TlsfGr1LiftError *error,
                             TlsfGr1LiftStatus *failure_status) {
  auto *stats = options ? options->stats : nullptr;
  if (failure_status)
    *failure_status = TLSF_GR1_LIFT_OK;
  if (!target || !result || result->game_aag || result->certificate_aag ||
      result->certificate_json || result->policy_aag || result->policy_json ||
      result->check_json || result->evidence_json) {
    lift_error(error, stats, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid or nonempty result");
    if (failure_status)
      *failure_status = TLSF_GR1_LIFT_INVALID;
    return TLSF_GR1_LIFT_INVALID;
  }
  memset(result, 0, sizeof *result);
  result->verdict = TLSF_GR1_CHECK_UNKNOWN;
  auto status = invoke_lift(
      [&] {
        auto cfg = lift_config(options);
        if (cfg.o.proof_order != TLSF_GR1_LIFT_POLICY_FIRST &&
            cfg.o.proof_order != TLSF_GR1_LIFT_REGION_FIRST)
          throw Failure(TLSF_GR1_LIFT_INVALID, FailureCause::invalid,
                        "arguments", "invalid proof order");
        run(target->trusted, cfg, *result);
        target->checked_hashes = result_hashes(*result);
        if (target->checked_hashes[0].empty())
          throw Failure(TLSF_GR1_LIFT_ERROR, FailureCause::error, "publish",
                        "artifact seal failed");
        target->checked_method = result->method;
        target->checked_verdict = result->verdict;
      },
      error, stats, failure_status);
  if (status != TLSF_GR1_LIFT_OK) {
    if (failure_status && *failure_status == TLSF_GR1_LIFT_OK)
      *failure_status = status;
    char detail[sizeof result->decline_detail];
    memcpy(detail, result->decline_detail, sizeof detail);
    tlsf_gr1_lift_result_clear(result);
    memcpy(result->decline_detail, detail, sizeof detail);
    if (error && *detail) {
      const size_t used = strlen(error->message);
      snprintf(error->message + used, sizeof error->message - used, ": %s",
               detail);
    }
  }
  return status;
}

extern "C" TlsfGr1LiftStatus
tlsf_gr1_lift_from_target(const TlsfGr1LiftTarget *target,
                          const TlsfGr1LiftOptions *options,
                          TlsfGr1LiftResult *result, TlsfGr1LiftError *error) {
  return tlsf_gr1_lift_from_target_v1(target, options, result, error, nullptr);
}

extern "C" int tlsf_gr1_lift_target_matches(const TlsfGr1LiftTarget *target,
                                            const TlsfGr1LiftResult *result) {
  if (!target || !result || !result->game_aag)
    return 0;
  const auto &trusted = target->trusted;
  return target->prepared_seal == trusted.game_hash &&
         result->semantics == trusted.semantics &&
         result->game_size == trusted.game_aag.size() &&
         memcmp(result->game_aag, trusted.game_aag.data(), result->game_size) ==
             0 &&
         result->method == target->checked_method &&
         result->verdict == target->checked_verdict &&
         target->checked_verdict != TLSF_GR1_CHECK_UNKNOWN &&
         result_hashes(*result) == target->checked_hashes;
}

extern "C" void tlsf_gr1_both_result_clear(TlsfGr1BothResult *result) {
  if (!result)
    return;
  tlsf_gr1_lift_result_clear(&result->proof);
  memset(result, 0, sizeof *result);
  result->proof.verdict = TLSF_GR1_CHECK_UNKNOWN;
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_both_from_target_v2(
    const TlsfGr1LiftTarget *target, const TlsfGr1BothOptionsV2 *routing,
    TlsfGr1BothResult *result, TlsfGr1LiftError *error) {
  const auto *options = routing ? routing->lift : nullptr;
  const auto *observer = routing ? routing->observer : nullptr;
  struct ObserverScope {
    const TlsfGr1BothObserverV1 *previous = phase_observer;
    explicit ObserverScope(const TlsfGr1BothObserverV1 *value) {
      phase_observer = value;
    }
    ~ObserverScope() { phase_observer = previous; }
  } phase_scope(observer);

  const bool disable_real_lift = routing && routing->disable_real_lift;
  TlsfGr1BothEventRoute live_route = TLSF_GR1_BOTH_EVENT_SEEDS;
  int proof_unreal = -1;
  TlsfGr1LiftStatus failure_status = TLSF_GR1_LIFT_OK;
  const auto failure_kind = [](FailureCause cause) {
    return is_applicability(cause) ? TLSF_GR1_BOTH_EVENT_DECLINE
                                   : TLSF_GR1_BOTH_EVENT_STOPPED;
  };
  bool initialized = false;
  const auto emit = [&](TlsfGr1BothEventKind kind, const char *stage,
                        const char *reason = "none",
                        TlsfGr1LiftStatus cause = TLSF_GR1_LIFT_OK) noexcept {
    if (observer && observer->event) {
      char message[TLSF_GR1_LIFT_DECLINE_DETAIL_SIZE + 512];
      if (initialized && result->decline_detail[0] &&
          (kind == TLSF_GR1_BOTH_EVENT_DECLINE ||
           kind == TLSF_GR1_BOTH_EVENT_STOPPED ||
           kind == TLSF_GR1_BOTH_EVENT_VERIFIED)) {
        snprintf(message, sizeof message, "%.509s: %s", reason,
                 result->decline_detail);
        reason = message;
      }
      try {
        observer->event(observer->context, kind, live_route, proof_unreal,
                        stage, reason, cause);
      } catch (...) {
        // Observer failures cannot change solving or escape the C API.
      }
    }
  };
  const auto select = [&](TlsfGr1BothEventRoute route, int side,
                          const char *stage) {
    live_route = route;
    proof_unreal = side;
    emit(TLSF_GR1_BOTH_EVENT_SELECTED, stage);
    emit(TLSF_GR1_BOTH_EVENT_START, stage);
  };
  TlsfGr1LiftError observed_error{};
  if (observer && !error)
    error = &observed_error;
  if (!target || !result || result->proof.game_aag ||
      result->proof.certificate_aag || result->proof.evidence_json) {
    lift_error(error, nullptr, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid or nonempty result");
    emit(TLSF_GR1_BOTH_EVENT_STOPPED, "arguments", "invalid or nonempty result",
         TLSF_GR1_LIFT_INVALID);
    return TLSF_GR1_LIFT_INVALID;
  }
  memset(result, 0, sizeof *result);
  result->proof.verdict = TLSF_GR1_CHECK_UNKNOWN;
  result->target_reductions = 1;
  initialized = true;
  auto status = invoke_lift(
      [&] {
        Config cfg = lift_config(options);
        const TrustedTarget &trusted = target->trusted;
        char source_hash[65]{}, game_hash[65]{};
        sha256_hex(trusted.snapshot.data(), trusted.snapshot.size(),
                   source_hash);
        sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), game_hash);
        if (trusted.semantics != TLSF_GR1_EXACT ||
            trusted.source_hash != source_hash ||
            trusted.game_hash != game_hash ||
            target->prepared_seal != game_hash ||
            trusted.game_aag != std::string(trusted.instance->r.aag,
                                            trusted.instance->r.aag_size))
          decline(FailureCause::error, "target_binding",
                  "trusted source or game changed");

        Candidate winner;
        bool have_winner = false;
        if (!disable_real_lift || !cfg.o.disable_env_lift) {
          bool fold_active = false;
          try {
            select(TLSF_GR1_BOTH_EVENT_SEEDS, -1, "seed_discovery");
            SharedSeeds cache =
                discover_shared(trusted, cfg, *result, disable_real_lift,
                                SeedDeclines{result->decline_detail});
            fold_active = cache.fold;
            if (cache.axis.empty()) {
              both_decline(*result, "seed_window");
              emit(TLSF_GR1_BOTH_EVENT_DECLINE, "seed_window",
                   "no stable index axis", TLSF_GR1_LIFT_DECLINED);
            } else {
              std::set<int> selected(cache.real_sizes.begin(),
                                     cache.real_sizes.end());
              for (int size : cache.env_sizes)
                if (!selected.insert(size).second)
                  result->seed_cache_hits++;
              TlsfGr1SeedPolarity common = TLSF_GR1_SEEDS_NONE;
              auto solve = [&](int size) {
                auto &entry = cache.entries.at(size);
                char hash[65]{};
                sha256_hex(entry.instance->r.aag, entry.instance->r.aag_size,
                           hash);
                if (entry.key.find(hash) == std::string::npos)
                  decline(FailureCause::error, "seed_binding",
                          "seed cache key differs from game");
                TlsfGr1SeedPolarity side;
                try {
                  side = solve_shared_seed(*entry.instance, cfg, *result,
                                           cache.fold);
                } catch (const Failure &e) {
                  if (cache.fold) {
                    SeedDeclines log{result->decline_detail};
                    log.at(cache.axis, size, size, ":fold");
                    log.note("fold_seed_failed");
                    log.failure(e);
                  }
                  throw;
                }
                return side;
              };
              for (int size : selected) {
                auto side = solve(size);
#ifdef TLSF_GR1_LIFT_TEST_FAULT
                if (both_test_seed_fault == 4 && size == *selected.begin() &&
                    cfg.o.deadline_mono_ns) {
                  while (now_ns() < cfg.o.deadline_mono_ns)
                    std::this_thread::sleep_for(std::chrono::milliseconds(1));
                  cfg.check("seed_solve");
                }
                if (both_test_seed_fault == 1 && size == *selected.rbegin())
                  side = side == TLSF_GR1_SEEDS_REAL ? TLSF_GR1_SEEDS_UNREAL
                                                     : TLSF_GR1_SEEDS_REAL;
                if (both_test_seed_fault == 2 && size == *selected.rbegin())
                  decline(FailureCause::error, "seed_error",
                          "injected unknown seed");
#endif
                if (common == TLSF_GR1_SEEDS_NONE)
                  common = side;
                else if (common != side)
                  common = TLSF_GR1_SEEDS_MIXED;
              }
              result->seed_polarity = common;
              // U keeps priority for UNREAL seeds. Select the pending fold
              // across all cached probes, reusing U's checked REAL seeds.
              if (common == TLSF_GR1_SEEDS_REAL && cache.real_sizes.empty() &&
                  cache.param_pending &&
                  param_support(*trusted.instance, cfg,
                                SeedDeclines{result->decline_detail})) {
                SeedDeclines log{result->decline_detail};
                log.at(cache.axis, 0, 0, ":param");
                try {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
                  if (lift_test_fault == 26)
                    throw std::bad_alloc();
#endif
                  ParamProbes probes;
                  for (auto &[k, entry] : cache.entries)
                    probes.emplace_back(k, std::move(entry.instance));
                  FoldProbes budget;
                  auto window =
                      discover_param((const uint8_t *)trusted.snapshot.data(),
                                     trusted.snapshot.size(), *trusted.instance,
                                     TLSF_GR1_EXACT, cfg, budget, log,
                                     &result->seed_reductions,
                                     &result->seed_probes, cache.axis, &probes);
                  if (window.axis != cache.axis)
                    selected.clear();
                  cache = shared_window(std::move(window), trusted);
                  fold_active = true;
                  for (int size : cache.real_sizes) {
                    if (selected.count(size)) {
                      result->seed_cache_hits++;
                      continue;
                    }
                    if (solve(size) != TLSF_GR1_SEEDS_REAL)
                      common = TLSF_GR1_SEEDS_MIXED;
                  }
                  result->seed_polarity = common;
                } catch (const std::bad_alloc &) {
                  log.exception("param_discovery", "resource",
                                "host allocation failed");
                  throw;
                } catch (const Failure &e) {
                  if (!is_applicability(e.cause))
                    throw;
                  cfg.decline_search("seed_window", "no stable index axis");
                }
              }
              if (cache.fold && common != TLSF_GR1_SEEDS_REAL) {
                SeedDeclines log{result->decline_detail};
                log.at(cache.axis, 0, 0, ":fold");
                log.note("fold_seed_polarity");
              }
              if (common == TLSF_GR1_SEEDS_REAL && !cache.real_sizes.empty()) {
                select(TLSF_GR1_BOTH_EVENT_R, 0, "R");
                Window window;
                window.axis = cache.axis;
                window.sizes = cache.real_sizes;
                window.target_members = cache.target_members;
                window.modes = cache.modes;
                window.fold = cache.fold;
                window.param = cache.param;
                window.fold_probes = cache.fold_probes;
                window.fold_reductions = cache.fold_reductions;
                for (int size : cache.real_sizes)
                  window.seeds.push_back(
                      std::move(cache.entries.at(size).instance));
                TlsfGr1LiftResult candidate_proof{};
                struct ProofGuard {
                  TlsfGr1LiftResult &value;
                  ~ProofGuard() { tlsf_gr1_lift_result_clear(&value); }
                } proof_guard{candidate_proof};
                const bool candidate_only = true;
                try {
                  run(trusted, cfg, candidate_proof, &window, candidate_only,
                      &result->seed_checks);
                } catch (...) {
                  if (cache.fold) {
                    SeedDeclines log{result->decline_detail};
                    log.at("fold");
                    log.note(candidate_proof.decline_detail);
                  }
                  throw;
                }
                if (cfg.stats && cfg.stats->internal_checks)
                  decline(FailureCause::error, "candidate_integrity",
                          "R candidate checked target");
                Candidate candidate;
                candidate.fold = cache.fold;
                candidate.param = cache.param;
                if (cache.fold) {
                  candidate.fold_evidence =
                      j::parse(std::string_view(candidate_proof.evidence_json,
                                                candidate_proof.evidence_size))
                          .as_object()
                          .at("fold")
                          .as_object();
                }
                candidate.game.assign(candidate_proof.game_aag,
                                      candidate_proof.game_size);
                candidate.certificate.assign(candidate_proof.certificate_aag,
                                             candidate_proof.certificate_size);
                candidate.certificate_json.assign(
                    candidate_proof.certificate_json,
                    candidate_proof.certificate_json_size);
                candidate.method = TLSF_GR1_CHECK_REGION;
                emit(TLSF_GR1_BOTH_EVENT_CHECK_START, "target_check");
                both_check(trusted, cfg, candidate, false, *result);
                emit(TLSF_GR1_BOTH_EVENT_VERIFIED, "target_check");
                winner = std::move(candidate);
                result->route = TLSF_GR1_BOTH_REAL_LIFT;
                have_winner = true;
              } else if (!cfg.o.disable_env_lift &&
                         common == TLSF_GR1_SEEDS_UNREAL &&
                         !cache.env_sizes.empty()) {
                select(TLSF_GR1_BOTH_EVENT_U, 1, "U");
#ifdef TLSF_GR1_LIFT_TEST_FAULT
                if (both_test_seed_fault == 3)
                  throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                                "schema_capacity",
                                "injected candidate capacity stop");
#endif
                CachedSeedWindow window;
                window.axis = cache.axis;
                window.target_members = cache.target_members;
                for (int size : cache.env_sizes)
                  window.seeds.push_back(
                      std::move(cache.entries.at(size).instance));
                TlsfGr1EnvLiftResult candidate{};
                struct EnvGuard {
                  TlsfGr1EnvLiftResult &value;
                  ~EnvGuard() { tlsf_gr1_env_lift_result_clear(&value); }
                } env_guard{candidate};
                Config env_cfg = cfg;
                env_cfg.env_candidate = true;
                env_cfg.env_budget = options ? &options->env_budget : nullptr;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
                if (both_test_env_rss_spike_bytes) {
                  std::vector<uint8_t> spike(both_test_env_rss_spike_bytes);
                  volatile uint8_t *pages = spike.data();
                  for (size_t i = 0; i < spike.size(); i += 4096)
                    pages[i] = 1;
                  env_cfg.check("env_candidate");
                }
#endif
                uint64_t started = now_ns();
                uint64_t allowance = 12000000000ull;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
                if (both_test_candidate_ns)
                  allowance = both_test_candidate_ns;
#endif
                env_cfg.phase_deadline_ns = allowance > UINT64_MAX - started
                                                ? UINT64_MAX
                                                : started + allowance;
                env_run(trusted, env_cfg, candidate.rank, &candidate, &window);
                if (candidate.target_checks)
                  decline(FailureCause::error, "candidate_integrity",
                          "environment candidate checked target");
                try {
                  emit(TLSF_GR1_BOTH_EVENT_CHECK_START, "target_check");
                  env_check(trusted, cfg, candidate);
                } catch (...) {
                  result->target_checks += candidate.target_checks;
                  throw;
                }
                result->target_checks += candidate.target_checks;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
                if (lift_test_fault == 8)
                  candidate.verdict = TLSF_GR1_CHECK_UNKNOWN;
#endif
                if (candidate.verdict != TLSF_GR1_CHECK_VERIFIED)
                  decline(FailureCause::error, "target_check",
                          "environment proof did not verify");
                emit(TLSF_GR1_BOTH_EVENT_VERIFIED, "target_check");
                winner.game = trusted.game_aag;
                winner.certificate.assign(candidate.certificate_aag,
                                          candidate.certificate_size);
                winner.certificate_json.assign(candidate.certificate_json,
                                               candidate.certificate_json_size);
                winner.policy.assign(candidate.policy_aag,
                                     candidate.policy_size);
                winner.policy_json.assign(candidate.policy_json,
                                          candidate.policy_json_size);
                if (candidate.check_json)
                  winner.check_json.assign(candidate.check_json,
                                           candidate.check_json_size);
                winner.method = TLSF_GR1_CHECK_CERTIFICATE;
                winner.verdict = TLSF_GR1_CHECK_VERIFIED;
                result->route = TLSF_GR1_BOTH_ENV_LIFT;
                have_winner = true;
              } else {
                both_decline(*result, common == TLSF_GR1_SEEDS_MIXED
                                          ? "seed_mixed"
                                          : "seed_polarity");
                const char *reason = common == TLSF_GR1_SEEDS_MIXED
                                         ? "mixed seed polarity"
                                         : "seed route unavailable";
                emit(TLSF_GR1_BOTH_EVENT_DECLINE, result->decline_stage, reason,
                     TLSF_GR1_LIFT_DECLINED);
              }
            }
          } catch (const Failure &e) {
            if (fold_active) {
              SeedDeclines log{result->decline_detail};
              log.at("fold");
              log.note("fold_failed");
              log.failure(e);
            }
            if (e.status == TLSF_GR1_LIFT_DEADLINE ||
                e.status == TLSF_GR1_LIFT_CANCELLED ||
                e.stage == "target_binding")
              throw;
            if (cfg.o.deadline_mono_ns && now_ns() >= cfg.o.deadline_mono_ns)
              throw Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline,
                            e.stage, "worker deadline exceeded");
            both_decline(*result, e.stage.c_str());
            emit(failure_kind(e.cause), e.stage.c_str(), e.what(),
                 e.failure_status);
            result->seed_polarity =
                result->seed_solves &&
                        result->seed_polarity == TLSF_GR1_SEEDS_NONE
                    ? TLSF_GR1_SEEDS_UNKNOWN
                    : result->seed_polarity;
          } catch (const std::bad_alloc &) {
            if (fold_active) {
              SeedDeclines log{result->decline_detail};
              log.note("fold_failed");
              log.exception("fold", "resource", "host allocation failed");
            }
            throw;
          } catch (const std::exception &e) {
            if (fold_active) {
              SeedDeclines log{result->decline_detail};
              log.note("fold_failed");
              log.exception("fold", "error", e.what());
            }
            throw;
          }
        }
        if (!have_winner) {
          select(TLSF_GR1_BOTH_EVENT_DIRECT, -1, "direct");
      // The seed cache and U's BDD/policy state are out of scope here.
      // Return allocator-held pages before applying the direct budget.
#ifdef __GLIBC__
          malloc_trim(0);
#endif
          cfg.check("direct_solve", true);
          Config direct_cfg = cfg;
          direct_cfg.o.max_artifact_bytes = 64u * 1024u * 1024u;
          direct_cfg.o.checker_nodes = 1u << 22;
          direct_cfg.o.checker_cache = 1u << 20;
          winner = direct_candidate(trusted, direct_cfg);
          const bool unreal = j::parse(winner.certificate_json)
                                  .as_object()
                                  .at("side")
                                  .as_string() == "environment";
          proof_unreal = unreal ? 1 : 0;
          emit(TLSF_GR1_BOTH_EVENT_CHECK_START, "target_check");
          both_check(trusted, direct_cfg, winner, unreal, *result);
          emit(TLSF_GR1_BOTH_EVENT_VERIFIED, "target_check");
          result->route = TLSF_GR1_BOTH_DIRECT;
        }
        publish_both(trusted, winner, *result);
        target->checked_hashes = result_hashes(result->proof);
        target->checked_method = result->proof.method;
        target->checked_verdict = result->proof.verdict;
      },
      error, options ? options->stats : nullptr, &failure_status);
  if (status != TLSF_GR1_LIFT_OK) {
    const auto cause =
        failure_status == TLSF_GR1_LIFT_OK ? status : failure_status;
    emit(failure_kind(failure_cause(cause)), error ? error->stage : "unknown",
         error ? error->message : "unknown", cause);
    tlsf_gr1_lift_result_clear(&result->proof);
  }
  return status;
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_both_from_target_v1(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    const TlsfGr1BothObserverV1 *observer, TlsfGr1BothResult *result,
    TlsfGr1LiftError *error) {
  const TlsfGr1BothOptionsV2 routing{options, observer, 0};
  return tlsf_gr1_both_from_target_v2(target, &routing, result, error);
}

extern "C" TlsfGr1LiftStatus
tlsf_gr1_both_from_target(const TlsfGr1LiftTarget *target,
                          const TlsfGr1LiftOptions *options,
                          TlsfGr1BothResult *result, TlsfGr1LiftError *error) {
  return tlsf_gr1_both_from_target_v1(target, options, nullptr, result, error);
}

extern "C" void tlsf_gr1_env_rank_result_clear(TlsfGr1EnvRankResult *result) {
  if (!result)
    return;
  free(result->rank_aag);
  free(result->class_trace_json);
  memset(result, 0, sizeof *result);
}

static Config env_candidate_config(const TlsfGr1LiftOptions *options) {
  Config cfg = lift_config(options);
  cfg.env_candidate = true;
  cfg.env_budget = options ? &options->env_budget : nullptr;
  uint64_t allowance = options && options->env_candidate_ns
                           ? options->env_candidate_ns
                           : TLSF_GR1_ENV_DEFAULT_CANDIDATE_NS;
  uint64_t started = now_ns();
  cfg.phase_deadline_ns =
      allowance > UINT64_MAX - started ? UINT64_MAX : started + allowance;
  return cfg;
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_env_rank_from_target(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    TlsfGr1EnvRankResult *result, TlsfGr1LiftError *error) {
  if (!target || !result || result->rank_aag || result->class_trace_json) {
    lift_error(error, nullptr, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid or nonempty result");
    return TLSF_GR1_LIFT_INVALID;
  }
  memset(result, 0, sizeof *result);
  return invoke_lift(
      [&] {
        Config cfg = env_candidate_config(options);
        env_run(target->trusted, cfg, *result);
      },
      error, nullptr);
}

extern "C" void tlsf_gr1_env_lift_result_clear(TlsfGr1EnvLiftResult *result) {
  if (!result)
    return;
  tlsf_gr1_env_rank_result_clear(&result->rank);
  free(result->certificate_aag);
  free(result->certificate_json);
  free(result->policy_aag);
  free(result->policy_json);
  free(result->check_json);
  memset(result, 0, sizeof *result);
  result->verdict = TLSF_GR1_CHECK_UNKNOWN;
}

static TlsfGr1LiftStatus env_lift_entry(const TlsfGr1LiftTarget *target,
                                        const TlsfGr1LiftOptions *options,
                                        TlsfGr1EnvLiftResult *result,
                                        TlsfGr1LiftError *error, bool check) {
  if (!target || !result || result->rank.rank_aag ||
      result->rank.class_trace_json || result->certificate_aag ||
      result->certificate_json || result->policy_aag || result->policy_json ||
      result->check_json) {
    lift_error(error, nullptr, TLSF_GR1_LIFT_INVALID, "arguments",
               "invalid or nonempty result");
    return TLSF_GR1_LIFT_INVALID;
  }
  memset(result, 0, sizeof *result);
  result->verdict = TLSF_GR1_CHECK_UNKNOWN;
  return invoke_lift(
      [&] {
        Config cfg = lift_config(options);
        Config candidate_cfg = env_candidate_config(options);
        env_run(target->trusted, candidate_cfg, result->rank, result);
        if (check)
          env_check(target->trusted, cfg, *result);
      },
      error, nullptr);
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_env_candidate_from_target(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    TlsfGr1EnvLiftResult *result, TlsfGr1LiftError *error) {
  return env_lift_entry(target, options, result, error, false);
}

extern "C" TlsfGr1LiftStatus tlsf_gr1_env_lift_from_target(
    const TlsfGr1LiftTarget *target, const TlsfGr1LiftOptions *options,
    TlsfGr1EnvLiftResult *result, TlsfGr1LiftError *error) {
  return env_lift_entry(target, options, result, error, true);
}
