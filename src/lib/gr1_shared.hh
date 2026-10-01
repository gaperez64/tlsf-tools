#pragma once

#include <tlsf/gr1_lift.h>
#include "oxidd_common.h"
#include "yyjson_cpp.hh"
#include <algorithm>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
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
struct Failure : std::runtime_error {
  TlsfGr1LiftStatus status;
  std::string stage;
  Failure(TlsfGr1LiftStatus s, std::string at, std::string why)
      : std::runtime_error(why), status(s), stage(std::move(at)) {}
};
[[noreturn]] inline void decline(const char *stage, const char *why) {
  throw Failure(TLSF_GR1_LIFT_DECLINED, stage, why);
}
uint64_t now_ns();
[[noreturn]] void decline(const char *stage, const char *why);
struct Config {
  TlsfGr1LiftOptions o{};
  // The caller's budget, read live so a stats callback may tighten it.
  const TlsfGr1ConstructionBudget *budget = nullptr;
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
  uint64_t effective_deadline() const {
    if (!phase_deadline_ns)
      return o.deadline_mono_ns;
    return o.deadline_mono_ns ? std::min(phase_deadline_ns, o.deadline_mono_ns)
                              : phase_deadline_ns;
  }
  void check(const char *stage) const {
    if (o.cancelled && o.cancelled(o.cancel_ctx))
      throw Failure(TLSF_GR1_LIFT_CANCELLED, stage, "cancelled");
    if (o.deadline_mono_ns && now_ns() >= o.deadline_mono_ns)
      throw Failure(TLSF_GR1_LIFT_DEADLINE, stage, "deadline exceeded");
    if (phase_deadline_ns && now_ns() >= phase_deadline_ns)
      throw Failure(TLSF_GR1_LIFT_LIMIT, stage, "fixed phase budget exhausted");
    if (budget && budget->max_rss_bytes) {
      rusage usage{};
      if (getrusage(RUSAGE_SELF, &usage) == 0) {
        const uint64_t kb = usage.ru_maxrss > 0 ? uint64_t(usage.ru_maxrss) : 0;
        const uint64_t peak = kb > UINT64_MAX / 1024u ? UINT64_MAX : kb * 1024u;
        if (work)
          work->peak_rss_bytes = std::max(work->peak_rss_bytes, peak);
        if (peak > budget->max_rss_bytes)
          throw Failure(
              TLSF_GR1_LIFT_LIMIT, "budget-memory",
              std::string(
                  "construction RSS peak exceeded arm memory share at ") +
                  stage);
      }
    }
  }
  void bytes(size_t n, const char *stage) const {
    check(stage);
    if (n > o.max_artifact_bytes)
      throw Failure(TLSF_GR1_LIFT_LIMIT, stage, "artifact byte cap exceeded");
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
             TlsfGr1EnvRankResult &out);
} // namespace gr1_lift_internal
