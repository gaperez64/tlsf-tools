#pragma once

#include <tlsf/gr1_lift.h>
#include "oxidd_common.h"
#include "yyjson_cpp.hh"
#include <algorithm>
#include <cstdio>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <sys/resource.h>
#include <time.h>
#include <vector>

namespace gr1_lift_internal {
extern const char env_stage_seed_window[];
extern const char env_side_system[];
namespace j = tlsf_json;
using namespace oxidd::capi;
using J = j::value;
using O = j::object;
using A = j::array;
enum class FailureCause {
  applicability,
  unsupported,
  resource,
  deadline,
  cancelled,
  invalid,
  error
};
inline TlsfGr1LiftStatus diagnostic_status(FailureCause cause) {
  switch (cause) {
  case FailureCause::applicability:
    return TLSF_GR1_LIFT_DECLINED;
  case FailureCause::unsupported:
    return TLSF_GR1_LIFT_UNSUPPORTED;
  case FailureCause::resource:
    return TLSF_GR1_LIFT_LIMIT;
  case FailureCause::deadline:
    return TLSF_GR1_LIFT_DEADLINE;
  case FailureCause::cancelled:
    return TLSF_GR1_LIFT_CANCELLED;
  case FailureCause::invalid:
    return TLSF_GR1_LIFT_INVALID;
  case FailureCause::error:
    return TLSF_GR1_LIFT_ERROR;
  }
  return TLSF_GR1_LIFT_ERROR;
}
inline FailureCause failure_cause(TlsfGr1LiftStatus status) {
  switch (status) {
  case TLSF_GR1_LIFT_DECLINED:
    return FailureCause::applicability;
  case TLSF_GR1_LIFT_UNSUPPORTED:
    return FailureCause::unsupported;
  case TLSF_GR1_LIFT_LIMIT:
    return FailureCause::resource;
  case TLSF_GR1_LIFT_DEADLINE:
    return FailureCause::deadline;
  case TLSF_GR1_LIFT_CANCELLED:
    return FailureCause::cancelled;
  case TLSF_GR1_LIFT_INVALID:
    return FailureCause::invalid;
  default:
    return FailureCause::error;
  }
}
inline bool is_applicability(FailureCause cause) {
  return cause == FailureCause::applicability ||
         cause == FailureCause::unsupported;
}
struct Failure : std::runtime_error {
  const TlsfGr1LiftStatus status, failure_status;
  const FailureCause cause;
  std::string stage;
  // Return/fallback policy is independent of the required diagnostic cause.
  Failure(TlsfGr1LiftStatus s, FailureCause why_kind, std::string at,
          std::string why)
      : std::runtime_error(why), status(s),
        failure_status(diagnostic_status(why_kind)), cause(why_kind),
        stage(std::move(at)) {}
};
[[noreturn]] inline void decline(FailureCause cause, const char *stage,
                                 const char *why) {
  throw Failure(TLSF_GR1_LIFT_DECLINED, cause, stage, why);
}
uint64_t now_ns();
FailureCause check_failure_cause(TlsfGr1CheckStatus status,
                                 TlsfGr1CheckVerdict verdict);
struct Config {
  TlsfGr1LiftOptions o{};
  TlsfGr1StructureGuardOptionsV1 structure_guard{1};
  mutable std::optional<FailureCause> search_cause;
  mutable std::string search_stage, search_message;
  void note_failure(const Failure &e) const {
    if (!is_applicability(e.cause)) {
      search_cause = e.cause;
      search_stage = e.stage;
      search_message = e.what();
    }
  }
  [[noreturn]] void decline_search(const char *stage, const char *why) const {
    if (search_cause)
      throw Failure(TLSF_GR1_LIFT_DECLINED, *search_cause, "search_error",
                    search_stage + ": " + search_message);
    decline(FailureCause::applicability, stage, why);
  }
  // The caller's budget, read live so a stats callback may tighten it.
  const TlsfGr1ConstructionBudget *budget = nullptr;
  const TlsfGr1ConstructionBudget *env_budget = nullptr;
  TlsfGr1ConstructionWork *work = nullptr;
  TlsfGr1LiftStats *stats = nullptr;
  void (*stats_callback)(void *, TlsfGr1LiftStatsStage,
                         const TlsfGr1LiftStageStats *) = nullptr;
  void *stats_context = nullptr;
  uint64_t max_seed_probes = TLSF_GR1_LIFT_DEFAULT_SEED_PROBES;
  uint64_t max_bdd_ops = TLSF_GR1_LIFT_DEFAULT_DISCOVERY_BDD_OPS;
  uint64_t max_policy_bdd_ops = TLSF_GR1_LIFT_DEFAULT_POLICY_BDD_OPS;
  uint64_t policy_proof_ns = TLSF_GR1_LIFT_DEFAULT_POLICY_PROOF_NS;
  uint64_t phase_deadline_ns = 0;
  bool env_candidate = false;
  // BDD cooperation may call check thousands of times per second. Keep
  // deadline/cancellation checks frequent, but bound the RSS syscalls.
  mutable uint64_t last_rss_sample_ns = 0;
  mutable uint64_t last_rss_limit = 0;
  uint64_t effective_deadline() const {
    if (!phase_deadline_ns)
      return o.deadline_mono_ns;
    return o.deadline_mono_ns ? std::min(phase_deadline_ns, o.deadline_mono_ns)
                              : phase_deadline_ns;
  }
  Failure deadline_failure(const char *stage) const {
    if (!env_candidate) {
      if (o.deadline_mono_ns && now_ns() >= o.deadline_mono_ns)
        return Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline, stage,
                       "deadline exceeded");
      if (phase_deadline_ns)
        return Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, stage,
                       "fixed phase budget exhausted");
      return Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline, stage,
                     "deadline exceeded");
    }
    if (o.deadline_mono_ns &&
        (!phase_deadline_ns || o.deadline_mono_ns <= phase_deadline_ns))
      return Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline, stage,
                     "deadline exceeded");
    if (phase_deadline_ns)
      return Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                     "candidate_allowance",
                     std::string("candidate allowance expired at ") + stage);
    return Failure(TLSF_GR1_LIFT_DEADLINE, FailureCause::deadline, stage,
                   "deadline exceeded");
  }
  void check(const char *stage, bool force_rss = false) const {
    if (o.cancelled && o.cancelled(o.cancel_ctx))
      throw Failure(TLSF_GR1_LIFT_CANCELLED, FailureCause::cancelled, stage,
                    "cancelled");
    if (effective_deadline() && now_ns() >= effective_deadline())
      throw deadline_failure(stage);
    uint64_t rss_limit = budget ? budget->max_rss_bytes : 0;
    if (env_budget && env_budget->max_rss_bytes &&
        (!rss_limit || env_budget->max_rss_bytes < rss_limit))
      rss_limit = env_budget->max_rss_bytes;
    if (rss_limit) {
      const uint64_t current_ns = now_ns();
      if (!force_rss && rss_limit == last_rss_limit && last_rss_sample_ns &&
          current_ns - last_rss_sample_ns < 10000000ull)
        return;
      last_rss_sample_ns = current_ns;
      last_rss_limit = rss_limit;
      rusage usage{};
      bool sample_current = true;
      if (getrusage(RUSAGE_SELF, &usage) == 0) {
        const uint64_t kb = usage.ru_maxrss > 0 ? uint64_t(usage.ru_maxrss) : 0;
        const uint64_t peak = kb > UINT64_MAX / 1024u ? UINT64_MAX : kb * 1024u;
        if (work)
          work->peak_rss_bytes = std::max(work->peak_rss_bytes, peak);
        // Current RSS cannot exceed the process peak. Avoid opening /proc
        // during the many BDD cooperation checks below the soft limit.
        sample_current = peak > rss_limit;
      }
      // The peak is diagnostic only: a released U candidate must not consume
      // the direct solve's memory allowance.
      if (sample_current) {
        if (FILE *file = fopen("/proc/self/status", "r")) {
          char line[256];
          uint64_t current = 0;
          while (fgets(line, sizeof line, file)) {
            unsigned long long kb = 0;
            if (sscanf(line, "VmRSS: %llu kB", &kb) == 1) {
              current = kb > UINT64_MAX / 1024u ? UINT64_MAX : kb * 1024u;
              break;
            }
          }
          fclose(file);
          if (current > rss_limit)
            throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource,
                          "budget-memory",
                          std::string("construction RSS exceeded arm memory ") +
                              "share at " + stage);
        }
      }
    }
  }
  void bytes(size_t n, const char *stage) const {
    check(stage);
    if (n > o.max_artifact_bytes)
      throw Failure(TLSF_GR1_LIFT_LIMIT, FailureCause::resource, stage,
                    "artifact byte cap exceeded");
  }
};
std::string str(const J &v);
std::string s(const O &o, const char *k);
int64_t num(const J &v);
int64_t n(const O &o, const char *k);
std::string dump(const J &v);
std::vector<int> ints(const A &a);
std::string join(const std::vector<std::string> &v);
template <typename T> std::string field(const T &v) {
  return std::to_string(v);
}
std::string key(std::initializer_list<std::string> parts);
template <typename Fn>
void subsets(const std::vector<int> &members, int arity, Fn &&fn) {
  std::vector<int> chosen;
  std::function<void(size_t)> visit = [&](size_t start) {
    if (int(chosen.size()) == arity) {
      fn(chosen);
      return;
    }
    for (size_t p = start; p < members.size(); p++) {
      chosen.push_back(members[p]);
      visit(p + 1);
      chosen.pop_back();
    }
  };
  visit(0);
}

struct Instance {
  TlsfGr1Reduction r{};
  O data;
  std::map<std::string, int64_t> overrides;
  std::vector<int> members;
  std::string cert_aag, cert_json;
  std::string env_policy_aag, env_policy_json;
  std::unique_ptr<Aig, decltype(&aig_free)> cert{nullptr, &aig_free};
  O cert_meta;
  ~Instance() { tlsf_gr1_reduction_clear(&r); }
  Instance() = default;
  Instance(const Instance &) = delete;
};

struct TrustedTarget {
  std::string snapshot;
  std::string source_hash;
  std::string game_aag;
  std::string game_hash;
  TlsfGr1ReductionSemantics semantics = TLSF_GR1_EXACT;
  std::unique_ptr<Instance> instance;
};

struct CachedSeedWindow {
  std::string axis;
  std::vector<int> target_members;
  std::vector<std::unique_ptr<Instance>> seeds;
};

std::unique_ptr<Aig, decltype(&aig_free)> parse_aig(const char *bytes,
                                                    size_t size);
std::string render_aig(const Aig *game, const Config &cfg);
std::unique_ptr<Instance> lower(const uint8_t *source, size_t size,
                                const std::map<std::string, int64_t> &overrides,
                                TlsfGr1ReductionSemantics semantics,
                                const Config &cfg);
std::map<std::string, int64_t> parameters(const Instance &instance);
std::pair<std::vector<int>, std::vector<int>>
axis_members(const Instance &target, const Instance &seed);
char *copy_bytes(const std::string &value);
void env_run(const TrustedTarget &trusted, const Config &cfg,
             TlsfGr1EnvRankResult &out,
             TlsfGr1EnvLiftResult *candidate = nullptr,
             CachedSeedWindow *shared_window = nullptr);
void env_check(const TrustedTarget &trusted, const Config &cfg,
               TlsfGr1EnvLiftResult &candidate);
void env_typed_axis(const Instance &i, const std::string &axis);
std::pair<std::set<std::string>, std::set<std::string>>
env_typed_classes(const Instance &i);
} // namespace gr1_lift_internal
