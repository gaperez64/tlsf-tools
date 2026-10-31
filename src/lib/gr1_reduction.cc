#define _GNU_SOURCE
#include "tlsf/gr1_reduction.h"

extern "C" {
#include "sha256.h"
#include "classify.h"
#include "dpa_buchi.h"
#include "print_ltlxba.h"
#include "tlsf/spec.h"
}

#include "yyjson_cpp.hh"
#include "gr1_formula.hh"
#include <algorithm>
#include <chrono>
#include <cctype>
#include <ctime>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <limits>
#include <map>
#ifdef __GLIBC__
#include <malloc.h>
#endif
#include <memory>
#include <new>
#include <regex>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>
#include <sys/resource.h>

#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
void reduction_test_source(const TlsfSpec *);
void reduction_test_provenance(TlsfGr1Reduction *, TlsfGr1ReductionSemantics);
char reduction_test_class(char, TlsfGr1ReductionSemantics);
void reduction_test_rejecting(std::vector<bool> &);
#endif

namespace {
namespace json = tlsf_json;
using Formula = gr1_formula::Formula;
using Op = gr1_formula::Op;

uint64_t stats_clock(clockid_t clock) noexcept {
  timespec ts{};
  return clock_gettime(clock, &ts) == 0
             ? uint64_t(ts.tv_sec) * 1000000000ull + uint64_t(ts.tv_nsec)
             : 0;
}
struct StatsScope {
  TlsfGr1ReductionStats *stats;
  TlsfGr1ReductionStatsStage stage;
  void (*callback)(void *, TlsfGr1ReductionStatsStage,
                   const TlsfGr1ReductionStageStats *);
  void *context;
  uint64_t wall = 0, cpu = 0;
  StatsScope(const TlsfGr1ReductionOptions &options,
             TlsfGr1ReductionStatsStage which) noexcept
      : stats(options.stats), stage(which), callback(options.stats_callback),
        context(options.stats_context) {
    if (stats) {
      wall = stats_clock(CLOCK_MONOTONIC);
      cpu = stats_clock(CLOCK_PROCESS_CPUTIME_ID);
    }
  }
  ~StatsScope() noexcept { finish(); }
  void finish() noexcept {
    if (!stats || !wall)
      return;
    auto &row = stats->stages[stage];
    row.wall_ns += stats_clock(CLOCK_MONOTONIC) - wall;
    row.cpu_ns += stats_clock(CLOCK_PROCESS_CPUTIME_ID) - cpu;
    row.rss_kb = -1;
    if (FILE *file = fopen("/proc/self/status", "r")) {
      char line[256];
      while (fgets(line, sizeof line, file))
        if (sscanf(line, "VmRSS: %ld kB", &row.rss_kb) == 1)
          break;
      fclose(file);
    }
    rusage usage{};
    getrusage(RUSAGE_SELF, &usage);
    row.peak_rss_kb = usage.ru_maxrss;
#ifdef __APPLE__
    row.peak_rss_kb /= 1024;
#endif
#if defined(__GLIBC__) &&                                                      \
    (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 33))
    const auto heap = mallinfo2();
    row.arena = heap.arena;
    row.hblkhd = heap.hblkhd;
    row.uordblks = heap.uordblks;
    row.fordblks = heap.fordblks;
#endif
    wall = 0;
    if (callback)
      callback(context, stage, &row);
  }
};

struct Failure : std::runtime_error {
  const TlsfGr1ReductionStatus status, failure_status;
  const char *stage;
  Failure(TlsfGr1ReductionStatus s, TlsfGr1ReductionStatus cause,
          const char *at, const std::string &why)
      : std::runtime_error(why), status(s), failure_status(cause), stage(at) {}
};

struct Limits {
  // The caller's options; the budget is read live at each check.
  const TlsfGr1ReductionOptions &options;
  TlsfGr1ConstructionWork &work;
  void check(const char *stage) const {
    const TlsfGr1ConstructionBudget &budget = options.budget;
    if (options.cancelled && options.cancelled(options.cancel_ctx))
      throw Failure(TLSF_GR1_REDUCE_CANCELLED, TLSF_GR1_REDUCE_CANCELLED, stage,
                    "cancelled");
    if (options.deadline_mono_ns) {
      struct timespec now;
      if (clock_gettime(CLOCK_MONOTONIC, &now) != 0)
        throw Failure(TLSF_GR1_REDUCE_ERROR, TLSF_GR1_REDUCE_ERROR, stage,
                      "monotonic clock failed");
      uint64_t ns = uint64_t(now.tv_sec) * 1000000000ull + now.tv_nsec;
      if (ns >= options.deadline_mono_ns)
        throw Failure(TLSF_GR1_REDUCE_DEADLINE, TLSF_GR1_REDUCE_DEADLINE, stage,
                      "deadline exceeded");
    }
    if (budget.max_rss_bytes) {
      rusage usage{};
      if (getrusage(RUSAGE_SELF, &usage) == 0) {
#ifdef __APPLE__
        const uint64_t peak =
            usage.ru_maxrss > 0 ? uint64_t(usage.ru_maxrss) : 0;
#else
        const uint64_t kb = usage.ru_maxrss > 0 ? uint64_t(usage.ru_maxrss) : 0;
        const uint64_t peak = kb > UINT64_MAX / 1024u ? UINT64_MAX : kb * 1024u;
#endif
        work.peak_rss_bytes = std::max(work.peak_rss_bytes, peak);
        if (peak > budget.max_rss_bytes)
          throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT,
                        "budget-memory",
                        "construction RSS peak exceeded arm memory share");
      }
    }
  }
  void bytes(size_t n, const char *stage) const {
    check(stage);
    if (options.max_artifact_bytes && n > options.max_artifact_bytes)
      throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, stage,
                    "artifact byte cap exceeded");
  }
};

uint64_t checked_add(uint64_t a, uint64_t b, const char *stage) {
  if (b > UINT64_MAX - a)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, stage,
                  "construction size overflow");
  return a + b;
}
struct Shape {
  uint64_t nodes = 0, temporal_depth = 0;
};
Shape shape(Formula formula, uint64_t depth = 0) {
  switch (formula.kind()) {
  case Op::X:
  case Op::F:
  case Op::G:
  case Op::U:
  case Op::R:
  case Op::W:
  case Op::M:
    depth = checked_add(depth, 1, "budget-structure");
    break;
  default:
    break;
  }
  Shape result{1, depth};
  for (Formula child : formula) {
    Shape part = shape(child, depth);
    result.nodes = checked_add(result.nodes, part.nodes, "budget-structure");
    result.temporal_depth =
        std::max(result.temporal_depth, part.temporal_depth);
  }
  return result;
}
void precheck(const std::vector<Formula> &assumptions,
              const std::vector<Formula> &guarantees, uint64_t ap_count,
              const Limits &limits) {
  auto &b = limits.options.budget;
  auto &w = limits.work;
  w.ap_count = ap_count;
  w.conjuncts =
      checked_add(assumptions.size(), guarantees.size(), "budget-structure");
  for (const auto *items : {&assumptions, &guarantees})
    for (Formula item : *items) {
      const Shape s = shape(item);
      w.formula_nodes =
          checked_add(w.formula_nodes, s.nodes, "budget-structure");
      w.max_conjunct_nodes = std::max(w.max_conjunct_nodes, s.nodes);
      w.max_temporal_depth = std::max(w.max_temporal_depth, s.temporal_depth);
      // A cheap structural estimate, not an automaton guarantee. Saturate
      // instead of wrapping when a deeply nested formula is encountered.
      const uint64_t factor = uint64_t{1}
                              << std::min<uint64_t>(s.temporal_depth, 20);
      const uint64_t estimate =
          s.nodes > UINT64_MAX / factor ? UINT64_MAX : s.nodes * factor;
      w.predicted_monitor_states =
          estimate > UINT64_MAX - w.predicted_monitor_states
              ? UINT64_MAX
              : w.predicted_monitor_states + estimate;
    }
  if ((b.max_formula_nodes && w.formula_nodes > b.max_formula_nodes) ||
      (b.max_ap_count && w.ap_count > b.max_ap_count) ||
      (b.max_conjuncts && w.conjuncts > b.max_conjuncts) ||
      (b.max_conjunct_nodes && w.max_conjunct_nodes > b.max_conjunct_nodes) ||
      (b.max_temporal_depth && w.max_temporal_depth > b.max_temporal_depth) ||
      (b.max_predicted_monitor_states &&
       w.predicted_monitor_states > b.max_predicted_monitor_states))
    throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT,
                  "budget-structure", "structural construction limit exceeded");
  limits.check("budget-structure");
}

template <typename F>
auto checked_call(const Limits &limits, const char *stage, F &&call) {
  limits.check(stage);
  auto result = call();
  limits.check(stage);
  return result;
}

// G(a R b) = G(b). Preserve the construction formula separately, but remove
// this inessential support from the normalized provenance, as before.
Formula monitor_normal_form(Formula formula) {
  if (formula.children().empty())
    return formula;
  std::vector<Formula> children;
  for (auto child : formula)
    children.push_back(monitor_normal_form(child));
  Formula result = Formula::make(formula.kind(), children);
  if (result.kind() == Op::G && result[0].kind() == Op::R)
    return Formula::G(result[0][1]);
  return result;
}

std::string canonical_formula_text(Formula formula) {
  auto kind = formula.kind();
  if (kind == Op::And || kind == Op::Or) {
    std::vector<std::string> children;
    for (Formula child : formula)
      children.push_back(canonical_formula_text(child));
    std::sort(children.begin(), children.end());
    std::string text = "(";
    for (size_t i = 0; i < children.size(); ++i) {
      if (i)
        text += kind == Op::And ? " & " : " | ";
      text += children[i];
    }
    return text + ")";
  }
  const char *prefix = nullptr;
  switch (kind) {
  case Op::G:
    prefix = "G";
    break;
  case Op::F:
    prefix = "F";
    break;
  case Op::X:
    prefix = "X";
    break;
  case Op::Not:
    prefix = "!";
    break;
  default:
    break;
  }
  if (prefix)
    return std::string(prefix) + "(" + canonical_formula_text(formula[0]) + ")";
  const char *binary = nullptr;
  switch (kind) {
  case Op::Implies:
    binary = "->";
    break;
  case Op::Equiv:
    binary = "<->";
    break;
  case Op::U:
    binary = "U";
    break;
  case Op::R:
    binary = "R";
    break;
  case Op::W:
    binary = "W";
    break;
  case Op::M:
    binary = "M";
    break;
  default:
    break;
  }
  if (binary) {
    std::string lhs = canonical_formula_text(formula[0]);
    std::string rhs = canonical_formula_text(formula[1]);
    if (kind == Op::Equiv && lhs > rhs)
      std::swap(lhs, rhs);
    return "(" + lhs + " " + binary + " " + rhs + ")";
  }
  if (formula.is_tt())
    return "1";
  if (formula.is_ff())
    return "0";
  const auto &name = formula.ap_name();
  bool plain = !name.empty() &&
               (std::isalpha((unsigned char)name[0]) || name[0] == '_') &&
               std::all_of(name.begin(), name.end(), [](unsigned char c) {
                 return std::isalnum(c) || c == '_';
               });
  if (name == "true" || name == "false" ||
      (name.size() == 1 &&
       std::string("XFGURWM").find(name[0]) != std::string::npos))
    plain = false;
  return plain ? name : json::serialize(json::value(name));
}

struct FileCloser {
  void operator()(FILE *fp) const {
    if (fp)
      fclose(fp);
  }
};
using File = std::unique_ptr<FILE, FileCloser>;

Formula lowered_formula(TlsfSpec *spec) {
  ClassifiedSpec *classes = classify_spec(spec);
  Node *root = classes ? build_spec_formula(spec, classes, PRINT_ALL) : nullptr;
  if (!root)
    throw std::bad_alloc();
  return gr1_formula::from_node(root);
}

std::string canonicalize(const std::string &text,
                         const std::map<std::string, std::string> &symbols) {
  auto initial = [](unsigned char c) {
    return std::isalpha(c) || c == '_' || c == '@';
  };
  auto subsequent = [](unsigned char c) {
    return std::isalnum(c) || c == '_' || c == '@' || c == '\'';
  };
  std::string result;
  for (size_t i = 0; i < text.size();) {
    if (text[i] == '"') {
      size_t j = i + 1;
      while (j < text.size()) {
        if (text[j] == '\\' && j + 1 < text.size()) {
          j += 2;
          continue;
        }
        if (text[j++] == '"')
          break;
      }
      std::string token = text.substr(i, j - i);
      auto value = json::parse(token);
      auto found = symbols.find(std::string(value.as_string()));
      result += found == symbols.end() ? token : found->second;
      i = j;
    } else if (initial(static_cast<unsigned char>(text[i]))) {
      size_t j = i + 1;
      while (j < text.size() && subsequent(static_cast<unsigned char>(text[j])))
        ++j;
      std::string token = text.substr(i, j - i);
      auto found = symbols.find(token);
      result += found == symbols.end() ? token : found->second;
      i = j;
    } else {
      result += text[i++];
    }
  }
  return result;
}

void conjuncts(Formula formula, std::vector<Formula> &out) {
  if (formula.kind() == Op::And) {
    for (Formula child : formula)
      conjuncts(child, out);
  } else if (formula.kind() == Op::G && formula[0].kind() == Op::And) {
    for (Formula child : formula[0])
      conjuncts(Formula::G(child), out);
  } else if (!formula.is_tt()) {
    out.push_back(formula);
  }
}

struct Automaton {
  struct Edge {
    unsigned dst;
    uint32_t label;
    bool acc;
  };
  std::unique_ptr<TlsfDpa, decltype(&tlsf_dpa_free)> context{nullptr,
                                                             tlsf_dpa_free};
  std::vector<std::vector<Edge>> rows;
  std::unordered_map<uint32_t, TlsfDpaLabelNode> labels;
  std::vector<std::string> names;
  size_t num_states() const { return rows.size(); }
  size_t num_edges() const {
    size_t n = 0;
    for (const auto &row : rows)
      n += row.size();
    return n;
  }
  unsigned get_init_state_number() const { return 0; }
  auto &out(unsigned state) { return rows.at(state); }
  const auto &out(unsigned state) const { return rows.at(state); }
};

struct Monitor {
  bool assumption;
  Formula formula;
  char mp_class;
  std::shared_ptr<Automaton> automaton;
  std::vector<bool> accepting, rejecting;
  std::vector<uint32_t> latches;
  std::string role;
  bool fallback_used = false; // retained metadata field; construction is direct
  std::string construction_formula;
};

std::vector<bool> rejecting_states(const Monitor &monitor,
                                   const Limits &limits) {
  size_t count = monitor.automaton->num_states();
  std::vector<std::vector<unsigned>> succ(count), pred(count);
  for (unsigned source = 0; source < count; ++source) {
    limits.check("monitor-scc");
    for (const auto &edge : monitor.automaton->out(source)) {
      succ[source].push_back(edge.dst);
      pred[edge.dst].push_back(source);
    }
  }
  std::vector<int> index(count, -1), low(count), stack;
  std::vector<bool> on_stack(count), live(count);
  int next_index = 0;
  std::function<void(unsigned)> visit = [&](unsigned state) {
    limits.check("monitor-scc");
    index[state] = low[state] = next_index++;
    stack.push_back(state);
    on_stack[state] = true;
    for (unsigned dst : succ[state]) {
      if (index[dst] < 0) {
        visit(dst);
        low[state] = std::min(low[state], low[dst]);
      } else if (on_stack[dst]) {
        low[state] = std::min(low[state], index[dst]);
      }
    }
    if (low[state] == index[state]) {
      std::vector<unsigned> component;
      unsigned member;
      do {
        member = unsigned(stack.back());
        stack.pop_back();
        on_stack[member] = false;
        component.push_back(member);
      } while (member != state);
      bool cyclic = component.size() > 1 ||
                    std::find(succ[state].begin(), succ[state].end(), state) !=
                        succ[state].end();
      if (cyclic &&
          std::any_of(component.begin(), component.end(),
                      [&](unsigned s) { return monitor.accepting[s]; }))
        for (unsigned s : component)
          live[s] = true;
    }
  };
  for (unsigned state = 0; state < count; ++state)
    if (index[state] < 0)
      visit(state);
  std::vector<unsigned> pending;
  for (unsigned state = 0; state < count; ++state)
    if (live[state])
      pending.push_back(state);
  while (!pending.empty()) {
    limits.check("monitor-scc");
    unsigned state = pending.back();
    pending.pop_back();
    for (unsigned parent : pred[state])
      if (!live[parent]) {
        live[parent] = true;
        pending.push_back(parent);
      }
  }
  for (size_t state = 0; state < count; ++state)
    live[state] = !live[state];
  return live;
}

void dpa_result(TlsfDpaStatus status, const Limits &limits, const char *stage) {
  limits.check(stage);
  if (status.code == TLSF_DPA_OK)
    return;
  auto code = status.code == TLSF_DPA_DECLINED ? TLSF_GR1_REDUCE_LIMIT
                                               : TLSF_GR1_REDUCE_ERROR;
  if (status.reason == TLSF_DPA_UNSUPPORTED)
    code = TLSF_GR1_REDUCE_UNSUPPORTED;
  if (status.reason == TLSF_DPA_CANCELLED)
    code = TLSF_GR1_REDUCE_CANCELLED;
  if (status.reason == TLSF_DPA_DEADLINE)
    code = TLSF_GR1_REDUCE_DEADLINE;
  throw Failure(code, code, stage,
                code == TLSF_GR1_REDUCE_UNSUPPORTED
                    ? "outside proved DPA Buchi fragment"
                    : "DPA construction declined (reason " +
                          std::to_string(status.reason) + ")");
}
TlsfDpaBudget dpa_budget(const Limits &limits) {
  TlsfDpaBudget budget{};
  budget.deadline_mono_ns = limits.options.deadline_mono_ns;
  budget.cancelled = [](void *opaque) -> int {
    const auto &l = *static_cast<const Limits *>(opaque);
    if (l.options.cancelled && l.options.cancelled(l.options.cancel_ctx))
      return 1;
    rusage usage{};
    if (l.options.budget.max_rss_bytes && getrusage(RUSAGE_SELF, &usage) == 0) {
#ifdef __APPLE__
      uint64_t peak = uint64_t(usage.ru_maxrss);
#else
      uint64_t peak = uint64_t(usage.ru_maxrss) * 1024u;
#endif
      if (peak > l.options.budget.max_rss_bytes)
        return 1;
    }
    return 0;
  };
  budget.cancel_ctx = const_cast<Limits *>(&limits);
  return budget;
}

#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
void reduction_test_monitor(const char *, std::shared_ptr<Automaton> &);
void reduction_test_formula(const char *, Formula &);
#endif

Monitor make_monitor(Formula formula, bool assumption, const Limits &limits) {
  limits.check("monitor");
  std::set<std::string> support;
  auto collect = [&](auto &self, Formula f) -> void {
    if (f.kind() == Op::ap)
      support.insert(f.ap_name());
    for (auto child : f)
      self(self, child);
  };
  collect(collect, formula);
  std::vector<const char *> names;
  for (const auto &name : support)
    names.push_back(name.c_str());
  auto automaton = std::make_shared<Automaton>();
  TlsfDpa *context = nullptr;
  auto budget = dpa_budget(limits);
  const auto &b = limits.options.budget;
  const uint64_t remaining =
      b.max_total_states
          ? b.max_total_states -
                std::min<uint64_t>(b.max_total_states, limits.work.states)
          : UINT64_MAX;
  const uint64_t cap = std::min<uint64_t>(
      remaining, limits.options.max_monitor_states -
                     std::min<uint64_t>(limits.options.max_monitor_states,
                                        limits.work.states));
  if (!cap) {
    ++limits.work.states; // the excluded initial state is known to be needed
    throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT,
                  "budget-monitor-states", "monitor state budget exhausted");
  }
  budget.max_states = size_t(cap);
  char klass = 0;
  auto status = dpa_buchi_create(
      reinterpret_cast<const TlsfAstNode *>(formula.node()), names.data(),
      uint32_t(names.size()), &budget, &context, &klass);
  automaton->context.reset(context);
  dpa_result(status, limits, "mp-class");
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
  klass = reduction_test_class(klass, limits.options.semantics);
#endif
  if (std::string("BGSOR").find(klass) == std::string::npos)
    throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_UNSUPPORTED,
                  "mp-class", "outside proved DPA Buchi fragment");
  uint64_t edges_seen = 0;
  for (uint32_t state = 0; state < tlsf_dpa_state_count(context); ++state) {
    limits.check("monitor");
    const TlsfDpaEdge *row = nullptr;
    size_t count = 0;
    status = tlsf_dpa_successors(context, state, &row, &count);
    if (status.reason == TLSF_DPA_STATE_LIMIT) {
      // The excluded state is not interned. Record the first excluded count
      // as a lower bound, together with edges of completed expansion rows.
      limits.work.states += tlsf_dpa_state_count(context) + 1;
      limits.work.edges += edges_seen;
      dpa_result(status, limits, "budget-monitor-states");
    }
    if (status.code != TLSF_DPA_OK) {
      limits.work.states += tlsf_dpa_state_count(context);
      limits.work.edges += edges_seen;
    }
    dpa_result(status, limits, "monitor");
    edges_seen += count;
    if (b.max_total_states &&
        tlsf_dpa_state_count(context) >
            b.max_total_states -
                std::min<uint64_t>(b.max_total_states, limits.work.states)) {
      limits.work.states += tlsf_dpa_state_count(context);
      limits.work.edges += edges_seen;
      throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT,
                    "budget-monitor-states",
                    "DPA expansion exceeded live state budget");
    }
    if (b.max_total_edges &&
        edges_seen >
            b.max_total_edges -
                std::min<uint64_t>(b.max_total_edges, limits.work.edges)) {
      limits.work.states += tlsf_dpa_state_count(context);
      limits.work.edges += edges_seen;
      throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT,
                    "budget-monitor-edges",
                    "DPA expansion exceeded edge budget");
    }
    std::vector<Automaton::Edge> converted;
    for (size_t i = 0; i < count; ++i)
      converted.push_back(
          {row[i].successor, row[i].label, bool(row[i].priority)});
    automaton->rows.push_back(std::move(converted));
  }
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
  reduction_test_monitor("complete", automaton);
#endif
  for (const auto &row : automaton->rows) {
    std::vector<uint32_t> labels;
    for (auto edge : row)
      labels.push_back(edge.label);
    bool partition =
        dpa_labels_partition(context, labels.data(), labels.size());
    dpa_result(tlsf_dpa_status(context), limits, "monitor");
    if (!partition)
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                    "monitor", "nondeterministic or incomplete monitor");
  }
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
  reduction_test_monitor("state-acceptance", automaton);
#endif
  Monitor monitor{assumption, monitor_normal_form(formula),
                  klass,      automaton,
                  {},         {},
                  {},         {},
                  false,      {}};
  for (const auto &row : automaton->rows) {
    int mark = -1;
    for (auto edge : row) {
      if (mark >= 0 && mark != int(edge.acc))
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                      "monitor", "non-state-based acceptance");
      mark = edge.acc;
    }
    if (mark < 0)
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                    "monitor", "empty state");
    monitor.accepting.push_back(bool(mark));
  }
  monitor.rejecting = rejecting_states(monitor, limits);
  // Preserve semantic constant monitors in provenance. Emptiness follows
  // from the live-SCC analysis. Universality is absence of a reachable cycle
  // consisting entirely of non-accepting states in this complete DBA.
  bool empty = monitor.rejecting[0];
  std::vector<size_t> indegree(automaton->num_states());
  size_t nonaccepting = 0;
  for (unsigned state = 0; state < automaton->num_states(); ++state) {
    limits.check("monitor-scc");
    if (monitor.accepting[state])
      continue;
    ++nonaccepting;
    for (auto edge : automaton->out(state))
      if (!monitor.accepting[edge.dst])
        ++indegree[edge.dst];
  }
  std::vector<unsigned> pending;
  for (unsigned state = 0; state < automaton->num_states(); ++state)
    if (!monitor.accepting[state] && !indegree[state])
      pending.push_back(state);
  size_t removed = 0;
  while (!pending.empty()) {
    limits.check("monitor-scc");
    unsigned state = pending.back();
    pending.pop_back();
    ++removed;
    for (auto edge : automaton->out(state))
      if (!monitor.accepting[edge.dst] && !--indegree[edge.dst])
        pending.push_back(edge.dst);
  }
  if (empty || removed == nonaccepting) {
    monitor.formula = empty ? Formula::ff() : Formula::tt();
    monitor.mp_class = klass = 'B';
  }

#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
  reduction_test_rejecting(monitor.rejecting);
#endif
  if (klass == 'B' || klass == 'S')
    for (unsigned state = 0; state < automaton->num_states(); ++state)
      if (monitor.rejecting[state])
        for (const auto &edge : automaton->out(state))
          if (!monitor.rejecting[edge.dst])
            throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                          "monitor", "non-sticky safety rejecting region");
  // Retain just the exported Boolean label DAG. A separate symbolic manager
  // per completed monitor would multiply its reserved BDD capacity by the
  // number of conjuncts, although encoding needs only these small rows.
  for (uint32_t ap = 0; ap < tlsf_dpa_ap_count(context); ++ap)
    automaton->names.emplace_back(tlsf_dpa_ap_name(context, ap));
  auto copy_label = [&](auto &self, uint32_t id) -> void {
    if (automaton->labels.count(id))
      return;
    limits.check("monitor-labels");
    const auto *node = tlsf_dpa_label_node(context, id);
    if (!node)
      throw std::runtime_error("invalid DPA label");
    automaton->labels.emplace(id, *node);
    if (node->kind == TLSF_DPA_DECISION) {
      self(self, node->low);
      self(self, node->high);
    }
  };
  for (const auto &row : automaton->rows)
    for (auto edge : row)
      copy_label(copy_label, edge.label);
  automaton->context.reset();
  return monitor;
}

#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
#include "gr1_reduction_test_hooks.hh"
#endif

struct AagBuilder {
  struct Latch {
    uint32_t current, next, reset;
    std::string name;
  };
  struct And {
    uint32_t lhs, left, right;
  };
  std::vector<std::string> names;
  std::map<std::string, uint32_t> literals;
  uint32_t next_var = 0;
  std::vector<Latch> latches;
  std::vector<And> ands;
  std::map<std::pair<uint32_t, uint32_t>, uint32_t> cache;
  uint32_t variable() {
    if (next_var >= UINT32_MAX / 2u)
      throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, "aag-size",
                    "AAG literal overflow");
    return 2u * ++next_var;
  }
  explicit AagBuilder(std::vector<std::string> inputs)
      : names(std::move(inputs)) {
    for (const auto &name : names)
      literals.emplace(name, variable());
  }
  uint32_t latch(uint32_t reset, std::string name) {
    uint32_t current = variable();
    latches.push_back({current, 0, reset, std::move(name)});
    return current;
  }
  void set_next(uint32_t current, uint32_t next) {
    for (auto &item : latches)
      if (item.current == current) {
        item.next = next;
        return;
      }
    throw Failure(TLSF_GR1_REDUCE_ERROR, TLSF_GR1_REDUCE_ERROR, "aag",
                  "unknown latch");
  }
  uint32_t land(uint32_t a, uint32_t b) {
    if (!a || !b || a == (b ^ 1u))
      return 0;
    if (a == 1 || a == b)
      return b;
    if (b == 1)
      return a;
    if (a > b)
      std::swap(a, b);
    auto key = std::make_pair(a, b);
    if (auto found = cache.find(key); found != cache.end())
      return found->second;
    uint32_t result = variable();
    ands.push_back({result, a, b});
    cache.emplace(key, result);
    return result;
  }
  uint32_t lor(uint32_t a, uint32_t b) { return land(a ^ 1u, b ^ 1u) ^ 1u; }
  uint32_t compile_atom(Formula f) {
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
    reduction_test_formula("transition", f);
#endif
    if (f.is_tt())
      return 1;
    if (f.is_ff())
      return 0;
    switch (f.kind()) {
    case Op::ap: {
      auto found = literals.find(f.ap_name());
      if (found == literals.end())
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                      "transition", "monitor refers to undeclared AP");
      return found->second;
    }
    default:
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                    "transition", "non-Boolean monitor transition label");
    }
  }
  std::map<std::pair<const Automaton *, uint32_t>, uint32_t> label_cache;
  uint32_t compile_label(const Automaton &automaton, uint32_t label) {
    auto key = std::make_pair(&automaton, label);
    if (auto it = label_cache.find(key); it != label_cache.end())
      return it->second;
    const auto &node = automaton.labels.at(label);
    uint32_t result;
    if (node.kind == TLSF_DPA_TRUE)
      result = compile_atom(Formula::tt());
    else if (node.kind == TLSF_DPA_FALSE)
      result = compile_atom(Formula::ff());
    else {
      uint32_t ap = compile_atom(Formula::ap(automaton.names.at(node.ap)));
      uint32_t low = compile_label(automaton, node.low),
               high = compile_label(automaton, node.high);
      result = lor(land(ap ^ 1u, low), land(ap, high));
    }
    label_cache.emplace(key, result);
    return result;
  }
  std::string render(uint32_t bad, const std::vector<uint32_t> &justice,
                     const std::vector<uint32_t> &fairness) const {
    std::string out = "aag " + std::to_string(next_var) + " " +
                      std::to_string(names.size()) + " " +
                      std::to_string(latches.size()) + " 1 " +
                      std::to_string(ands.size()) + " 0 0 " +
                      std::to_string(std::max<size_t>(1, justice.size())) +
                      " " + std::to_string(fairness.size()) + "\n";
    for (const auto &name : names)
      out += std::to_string(literals.at(name)) + "\n";
    for (const auto &item : latches)
      out += std::to_string(item.current) + " " + std::to_string(item.next) +
             " " + std::to_string(item.reset) + "\n";
    out += std::to_string(bad) + "\n";
    for (size_t i = 0; i < std::max<size_t>(1, justice.size()); ++i)
      out += "1\n";
    if (justice.empty())
      out += "1\n";
    else
      for (uint32_t lit : justice)
        out += std::to_string(lit) + "\n";
    for (uint32_t lit : fairness)
      out += std::to_string(lit) + "\n";
    for (const auto &item : ands)
      out += std::to_string(item.lhs) + " " + std::to_string(item.left) + " " +
             std::to_string(item.right) + "\n";
    for (size_t i = 0; i < names.size(); ++i)
      out += "i" + std::to_string(i) + " " + names[i] + "\n";
    for (size_t i = 0; i < latches.size(); ++i)
      out += "l" + std::to_string(i) + " " + latches[i].name + "\n";
    out += "o0 bad\n";
    for (size_t i = 0; i < std::max<size_t>(1, justice.size()); ++i)
      out += "j" + std::to_string(i) + " guarantee_monitor_" +
             std::to_string(i) + "\n";
    for (size_t i = 0; i < fairness.size(); ++i)
      out += "f" + std::to_string(i) + " assumption_monitor_" +
             std::to_string(i) + "\n";
    out += "c\ngenerated by gr1_monitor_game.py; one-hot DBA monitors\n";
    return out;
  }
};

struct Encoded {
  std::string aag;
  uint32_t violated = 0;
  bool has_violated = false;
  unsigned justice = 0, fairness = 0;
};

Encoded encode(std::vector<Monitor> &monitors,
               const std::vector<std::string> &inputs,
               const std::vector<std::string> &outputs, bool strict,
               const Limits &limits) {
  std::vector<std::string> names;
  for (size_t i = 0; i < inputs.size(); ++i)
    names.push_back("uncontrollable_i" + std::to_string(i));
  for (size_t i = 0; i < outputs.size(); ++i)
    names.push_back("controllable_o" + std::to_string(i));
  AagBuilder builder(std::move(names));
  for (auto &monitor : monitors) {
    unsigned initial = monitor.automaton->get_init_state_number();
    for (unsigned state = 0; state < monitor.automaton->num_states(); ++state)
      monitor.latches.push_back(builder.latch(
          unsigned(state == initial),
          "monitor_" + std::to_string(&monitor - monitors.data()) + "_state_" +
              std::to_string(state)));
  }
  bool safety_assumptions = false;
  for (const auto &monitor : monitors)
    safety_assumptions |= strict && monitor.assumption &&
                          (monitor.mp_class == 'B' || monitor.mp_class == 'S');
  Encoded encoded;
  if (safety_assumptions) {
    encoded.has_violated = true;
    encoded.violated = builder.latch(0, "assumption_safety_violated");
  }
  for (auto &monitor : monitors) {
    std::vector<std::vector<uint32_t>> incoming(monitor.latches.size());
    for (unsigned source = 0; source < monitor.latches.size(); ++source) {
      limits.check("transitions");
      for (const auto &edge : monitor.automaton->out(source)) {
        uint32_t literal =
            builder.compile_label(*monitor.automaton, edge.label);
        incoming[edge.dst].push_back(
            builder.land(monitor.latches[source], literal));
      }
    }
    for (size_t state = 0; state < monitor.latches.size(); ++state) {
      uint32_t next = 0;
      for (uint32_t lit : incoming[state])
        next = builder.lor(next, lit);
      builder.set_next(monitor.latches[state], next);
    }
  }
  std::vector<uint32_t> accepting, rejecting;
  for (const auto &monitor : monitors) {
    uint32_t yes = 0, no = 0;
    for (size_t state = 0; state < monitor.latches.size(); ++state) {
      if (monitor.accepting[state])
        yes = builder.lor(yes, monitor.latches[state]);
      if (monitor.rejecting[state])
        no = builder.lor(no, monitor.latches[state]);
    }
    accepting.push_back(yes);
    rejecting.push_back(no);
  }
  uint32_t release = encoded.has_violated ? encoded.violated : 0;
  if (encoded.has_violated) {
    uint32_t current = 0;
    for (size_t i = 0; i < monitors.size(); ++i)
      if (monitors[i].assumption &&
          (monitors[i].mp_class == 'B' || monitors[i].mp_class == 'S'))
        current = builder.lor(current, rejecting[i]);
    release = builder.lor(encoded.violated, current);
    builder.set_next(encoded.violated, release);
  }
  std::vector<uint32_t> justice, fairness;
  uint32_t bad_terms = 0;
  bool has_bad_terms = false;
  for (size_t i = 0; i < monitors.size(); ++i) {
    auto &monitor = monitors[i];
    bool safety = monitor.mp_class == 'B' || monitor.mp_class == 'S';
    if (!strict) {
      if (monitor.assumption) {
        monitor.role = "fairness";
        fairness.push_back(accepting[i]);
      } else {
        monitor.role = "justice";
        justice.push_back(accepting[i]);
      }
    } else if (safety) {
      if (monitor.assumption)
        monitor.role = "violated";
      else {
        monitor.role = "bad";
        bad_terms = builder.lor(bad_terms, rejecting[i]);
        has_bad_terms = true;
      }
    } else if (monitor.assumption) {
      monitor.role = "fairness";
      fairness.push_back(accepting[i]);
    } else {
      monitor.role = "justice";
      justice.push_back(builder.lor(accepting[i], release));
    }
  }
  uint32_t bad =
      strict && has_bad_terms ? builder.land(bad_terms, release ^ 1u) : 0;
  encoded.justice = unsigned(std::max<size_t>(1, justice.size()));
  encoded.fairness = unsigned(fairness.size());
  encoded.aag = builder.render(bad, justice, fairness);
  limits.bytes(encoded.aag.size(), "aag");
  return encoded;
}

Formula raw_formula(Formula canonical,
                    const std::map<std::string, std::string> &symbols) {
  gr1_formula::Replacements replacements;
  for (const auto &[raw, encoded] : symbols)
    replacements.emplace(encoded, Formula::ap(raw));
  return gr1_formula::relabel(canonical, &replacements);
}

std::pair<std::string, std::vector<unsigned>>
split_signal_index(const std::string &name) {
  static const std::regex pattern("^(.*?)(_(?:[0-9]+)(?:_[0-9]+)*)$");
  std::smatch match;
  if (!std::regex_match(name, match, pattern))
    return {name, {}};
  std::vector<unsigned> indices;
  std::string suffix = match[2];
  size_t pos = 1;
  while (pos < suffix.size()) {
    size_t end = suffix.find('_', pos);
    indices.push_back(unsigned(std::stoul(suffix.substr(pos, end - pos))));
    if (end == std::string::npos)
      break;
    pos = end + 1;
  }
  return {match[1], indices};
}

json::array numbers(const std::vector<unsigned> &values) {
  json::array out;
  for (unsigned value : values)
    out.push_back(value);
  return out;
}

std::pair<std::string, json::array> index_template(const std::string &text) {
  static const std::regex pattern(
      R"(\b([A-Za-z][A-Za-z0-9]*?(?:_[A-Za-z][A-Za-z0-9]*)*)((?:_[0-9]+)+)\b)");
  std::map<unsigned, unsigned> positions;
  json::array concrete;
  std::string out;
  std::sregex_iterator it(text.begin(), text.end(), pattern), end;
  size_t last = 0;
  for (; it != end; ++it) {
    auto match = *it;
    out += text.substr(last, size_t(match.position()) - last);
    out += match[1].str();
    std::string suffix = match[2].str();
    size_t pos = 1;
    while (pos < suffix.size()) {
      size_t next = suffix.find('_', pos);
      unsigned value = unsigned(std::stoul(suffix.substr(pos, next - pos)));
      auto found = positions.find(value);
      if (found == positions.end()) {
        unsigned slot = unsigned(positions.size());
        positions.emplace(value, slot);
        concrete.push_back(value);
        out += "_i" + std::to_string(slot);
      } else {
        out += "_i" + std::to_string(found->second);
      }
      if (next == std::string::npos)
        break;
      pos = next + 1;
    }
    last = size_t(match.position() + match.length());
  }
  out += text.substr(last);
  return {out, concrete};
}

std::set<std::string> ap_names(Formula formula) {
  std::set<std::string> names;
  if (formula.kind() == Op::ap)
    names.insert(formula.ap_name());
  for (Formula child : formula) {
    auto part = ap_names(child);
    names.insert(part.begin(), part.end());
  }
  return names;
}

using BusMember = std::pair<std::string, std::vector<unsigned>>;
using Buses = std::map<std::string, std::vector<BusMember>>;

std::vector<unsigned> json_indices(const json::value &value) {
  std::vector<unsigned> out;
  for (const auto &item : value.as_array())
    out.push_back(unsigned(item.as_int64()));
  return out;
}

std::string structural_template(Formula formula, const json::object &signals,
                                const Limits &limits) {
  std::vector<
      std::tuple<std::string, unsigned, std::vector<unsigned>, std::string>>
      ordered;
  for (const std::string &name : ap_names(formula)) {
    const auto &record = signals.at(name).as_object();
    std::string id = std::string(record.at("declaration_id").as_string());
    std::string direction = std::string(record.at("direction").as_string());
    size_t colon = id.find(':');
    unsigned ordinal = unsigned(std::stoul(id.substr(colon + 1)));
    ordered.emplace_back(direction, ordinal,
                         json_indices(record.at("index_tuple")), name);
  }
  std::sort(ordered.begin(), ordered.end());
  std::map<unsigned, unsigned> coordinates;
  gr1_formula::Replacements replacements;
  for (const auto &[direction, ordinal, indices, name] : ordered) {
    std::string alias = "s_" + direction + "_" + std::to_string(ordinal);
    for (unsigned value : indices) {
      auto [it, inserted] = coordinates.emplace(value, coordinates.size());
      (void)inserted;
      alias += "_i" + std::to_string(it->second);
    }
    replacements.emplace(name, Formula::ap(alias));
  }
  return canonical_formula_text(checked_call(limits, "template-relabel", [&] {
    return gr1_formula::relabel(formula, &replacements);
  }));
}

json::object monitor_support(Formula formula, const Buses &buses,
                             std::string &arity_kind) {
  auto names = ap_names(formula);
  std::set<std::string> bus_aps;
  json::object supports;
  arity_kind = "local";
  for (const auto &[base, members] : buses) {
    std::vector<std::vector<unsigned>> present;
    for (const auto &[name, indices] : members)
      if (names.count(name)) {
        present.push_back(indices);
        bus_aps.insert(name);
      }
    if (present.empty())
      continue;
    if (present.size() == members.size())
      arity_kind = "bus_wide";
    bool single =
        std::all_of(present.begin(), present.end(),
                    [](const auto &tuple) { return tuple.size() == 1; });
    json::array display;
    for (const auto &tuple : present)
      display.push_back(single ? json::value(tuple[0])
                               : json::value(numbers(tuple)));
    supports[base] = std::move(display);
  }
  json::array scalars;
  for (const std::string &name : names)
    if (!bus_aps.count(name))
      scalars.push_back(json::value(name));
  return {{"buses", supports}, {"scalars", scalars}};
}

bool formula_equal(Formula a, Formula b, const Limits &limits) {
  if (a.key() == b.key())
    return true;
  a = monitor_normal_form(a);
  b = monitor_normal_form(b);
  if (a.key() == b.key())
    return true;
  auto support = ap_names(a), other = ap_names(b);
  // Binding may conservatively be unavailable. Different temporal supports
  // cannot be matched by syntax; skip their potentially large product. Keep
  // Boolean/constant comparisons, which can remove inessential atoms.
  bool both_temporal = !a.is_boolean() && !b.is_boolean();
  if (support != other && both_temporal)
    return false;
  bool temporal = !(a.is_boolean() && b.is_boolean());
  support.insert(other.begin(), other.end());
  std::vector<const char *> names;
  for (const auto &name : support)
    names.push_back(name.c_str());
  auto budget = dpa_budget(limits);
  bool equal = false;
  auto status = dpa_formula_equal(
      reinterpret_cast<const TlsfAstNode *>(a.node()),
      reinterpret_cast<const TlsfAstNode *>(b.node()), names.data(),
      uint32_t(names.size()), &budget, temporal, &equal);
  dpa_result(status, limits, "provenance-equivalence");
  return equal;
}

bool boolean_eval(Formula formula,
                  const std::map<std::string, bool> &valuation) {
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
  reduction_test_formula("symmetric-body", formula);
#endif
  if (formula.is_tt())
    return true;
  if (formula.is_ff())
    return false;
  switch (formula.kind()) {
  case Op::ap:
    return valuation.at(formula.ap_name());
  case Op::Not:
    return !boolean_eval(formula[0], valuation);
  case Op::And:
    for (Formula child : formula)
      if (!boolean_eval(child, valuation))
        return false;
    return true;
  case Op::Or:
    for (Formula child : formula)
      if (boolean_eval(child, valuation))
        return true;
    return false;
  case Op::Implies:
    return !boolean_eval(formula[0], valuation) ||
           boolean_eval(formula[1], valuation);
  case Op::Equiv:
    return boolean_eval(formula[0], valuation) ==
           boolean_eval(formula[1], valuation);
  default:
    throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                  "provenance", "non-Boolean symmetric monitor body");
  }
}

json::value symmetric_signature(Formula formula, const Buses &buses,
                                const Limits &limits) {
  if (formula.kind() != Op::G || !formula[0].is_boolean())
    return nullptr;
  Formula body = formula[0];
  auto names = ap_names(body);
  Buses relevant;
  for (const auto &[base, members] : buses)
    for (const auto &[name, indices] : members)
      if (names.count(name)) {
        relevant.emplace(base, members);
        break;
      }
  if (relevant.empty())
    return nullptr;
  std::set<std::string> bus_names;
  for (const auto &[base, members] : relevant) {
    for (size_t i = 1; i < members.size(); ++i) {
      limits.check("symmetry");
      gr1_formula::Replacements swap;
      swap.emplace(members[i - 1].first, Formula::ap(members[i].first));
      swap.emplace(members[i].first, Formula::ap(members[i - 1].first));
      Formula swapped = checked_call(limits, "symmetry-relabel", [&] {
        return gr1_formula::relabel(body, &swap);
      });
      if (!checked_call(limits, "symmetry-equivalence",
                        [&] { return formula_equal(body, swapped, limits); }))
        return false;
    }
    for (const auto &[name, indices] : members)
      bus_names.insert(name);
  }
  for (const std::string &scalar : names)
    if (!bus_names.count(scalar)) {
      limits.check("symmetry");
      gr1_formula::Replacements when_false, when_true;
      when_false.emplace(scalar, Formula::ff());
      when_true.emplace(scalar, Formula::tt());
      Formula lhs = checked_call(limits, "symmetry-relabel", [&] {
        return gr1_formula::relabel(body, &when_false);
      });
      Formula rhs = checked_call(limits, "symmetry-relabel", [&] {
        return gr1_formula::relabel(body, &when_true);
      });
      if (!checked_call(limits, "symmetry-equivalence",
                        [&] { return formula_equal(lhs, rhs, limits); }))
        return false;
    }
  std::vector<std::pair<std::string, std::vector<BusMember>>> ordered(
      relevant.begin(), relevant.end());
  size_t valuations = 1;
  for (const auto &[base, members] : ordered) {
    (void)base;
    if (valuations > 1000000 / (members.size() + 1))
      throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, "symmetry",
                    "symmetric signature valuation cap exceeded");
    valuations *= members.size() + 1;
  }
  std::set<std::vector<unsigned>> true_counts;
  std::vector<unsigned> current(ordered.size());
  std::function<void(size_t)> enumerate = [&](size_t axis) {
    limits.check("symmetry");
    if (axis < ordered.size()) {
      for (unsigned count = 0; count <= ordered[axis].second.size(); ++count) {
        current[axis] = count;
        enumerate(axis + 1);
      }
      return;
    }
    std::map<std::string, bool> valuation;
    for (const auto &name : names)
      valuation.emplace(name, false);
    for (size_t i = 0; i < ordered.size(); ++i)
      for (unsigned k = 0; k < current[i]; ++k)
        valuation[ordered[i].second[k].first] = true;
    if (boolean_eval(body, valuation))
      true_counts.insert(current);
  };
  enumerate(0);
  std::vector<std::set<unsigned>> allowed(ordered.size());
  for (const auto &tuple : true_counts)
    for (size_t i = 0; i < tuple.size(); ++i)
      allowed[i].insert(tuple[i]);
  size_t represented = 1;
  for (const auto &axis : allowed)
    represented *= axis.size();
  if (represented != true_counts.size())
    return false;
  json::object signature;
  for (size_t i = 0; i < ordered.size(); ++i) {
    json::array counts;
    for (unsigned count : allowed[i])
      counts.push_back(count);
    signature[ordered[i].first] = std::move(counts);
  }
  return signature;
}

json::value provenance(const TlsfPipeline *pipeline,
                       const std::vector<Monitor> &monitors,
                       const std::vector<std::string> &inputs,
                       const std::vector<std::string> &outputs,
                       const std::map<std::string, std::string> &symbols,
                       bool strict, const Encoded &encoded,
                       const Limits &limits) {
  json::value frontend;
  bool frontend_valid = false;
  json::object signal_by_name;
  std::vector<std::pair<Formula, json::object>> candidates;
  if (pipeline->frontend_provenance_json) {
    frontend = json::parse(pipeline->frontend_provenance_json);
    const auto &object = frontend.as_object();
    frontend_valid =
        object.at("schema") == "tlsf-tools.frontend-provenance.v1" &&
        object.at("ambiguous") == false &&
        object.at("source_sha256") == pipeline->source_sha256;
    std::vector<std::string> actual_inputs, actual_outputs;
    std::set<std::string> seen_signals;
    for (const auto &value : object.at("signals").as_array()) {
      const auto &signal = value.as_object();
      std::string name(signal.at("name").as_string());
      frontend_valid &= seen_signals.insert(name).second;
      signal_by_name[name] = signal;
      if (signal.at("direction") == "input")
        actual_inputs.push_back(name);
      else if (signal.at("direction") == "output")
        actual_outputs.push_back(name);
      else
        frontend_valid = false;
    }
    frontend_valid &= actual_inputs == inputs && actual_outputs == outputs;
    std::set<std::pair<std::string, int64_t>> seen_conjuncts;
    for (const auto &value : object.at("conjuncts").as_array()) {
      const auto &item = value.as_object();
      int64_t position = item.at("generated_position").as_int64();
      frontend_valid &=
          position >= 0 &&
          seen_conjuncts
              .emplace(std::string(item.at("source_formula_id").as_string()),
                       position)
              .second;
    }
    if (frontend_valid)
      for (const auto &value : object.at("conjuncts").as_array()) {
        const auto &item = value.as_object();
        std::string text(item.at("formula").as_string());
        Formula parsed = checked_call(limits, "provenance-parse", [&] {
          return raw_formula(
              gr1_formula::parse_formula(canonicalize(text, symbols)), symbols);
        });
        if (item.at("block") == "REQUIRE" || item.at("block") == "ASSERT")
          parsed = Formula::G(parsed);
        json::object row = item;
        row["normalized_formula"] = canonical_formula_text(parsed);
        json::array refs;
        for (const auto &name : row.at("signals").as_array()) {
          const auto &signal = signal_by_name.at(name.as_string()).as_object();
          refs.push_back(
              json::object{{"declaration_id", signal.at("declaration_id")},
                           {"index_tuple", signal.at("index_tuple")},
                           {"index_role", signal.at("index_role")}});
        }
        row["signal_refs"] = std::move(refs);
        candidates.emplace_back(parsed, std::move(row));
      }
  }
  json::array source_conjuncts;
  for (const auto &candidate : candidates)
    source_conjuncts.push_back(candidate.second);
  Buses buses;
  auto add_bus = [&](const std::string &name) {
    if (frontend_valid) {
      const auto &signal = signal_by_name.at(name).as_object();
      if (signal.at("dimensions").as_int64())
        buses[std::string(signal.at("declaration_id").as_string())]
            .emplace_back(name, json_indices(signal.at("index_tuple")));
    } else {
      auto [base, indices] = split_signal_index(name);
      if (!indices.empty())
        buses[base].emplace_back(name, indices);
    }
  };
  for (const auto &name : inputs)
    add_bus(name);
  for (const auto &name : outputs)
    add_bus(name);
  for (auto &[base, members] : buses)
    std::sort(members.begin(), members.end(),
              [](const auto &a, const auto &b) { return a.second < b.second; });
  auto signal_record = [&](const std::string &name,
                           uint32_t literal) -> json::object {
    auto [base, indices] = split_signal_index(name);
    json::object record{{"name", name},
                        {"base_name", base},
                        {"index_tuple", numbers(indices)},
                        {"provenance_source", "suffix-heuristic"},
                        {"game_symbol", symbols.at(name)},
                        {"game_literal", literal}};
    if (frontend_valid) {
      for (const auto &[key, value] : signal_by_name.at(name).as_object())
        record[key] = value;
      record["base_name"] = record.at("source_name");
      record["provenance_source"] = "frontend";
    }
    return record;
  };
  json::array input_records, output_records, monitor_records;
  for (size_t p = 0; p < inputs.size(); ++p)
    input_records.push_back(signal_record(inputs[p], uint32_t(2 * (p + 1))));
  for (size_t p = 0; p < outputs.size(); ++p)
    output_records.push_back(
        signal_record(outputs[p], uint32_t(2 * (inputs.size() + p + 1))));
  bool available = frontend_valid;
  unsigned justice_index = 0;
  for (size_t index = 0; index < monitors.size(); ++index) {
    limits.check("provenance");
    const auto &monitor = monitors[index];
    Formula raw = checked_call(limits, "provenance-relabel", [&] {
      return raw_formula(monitor.formula, symbols);
    });
    std::string text = canonical_formula_text(raw);
    auto [templ, indices] = index_template(text);
    if (frontend_valid)
      templ = structural_template(raw, signal_by_name, limits);
    std::string arity_kind;
    json::object support = monitor_support(raw, buses, arity_kind);
    json::array latch_literals;
    for (uint32_t lit : monitor.latches)
      latch_literals.push_back(lit);
    json::object record{
        {"monitor", index},
        {"side", monitor.assumption ? "assumption" : "guarantee"},
        {"mp_class", std::string(1, monitor.mp_class)},
        {"conjunct", text},
        {"construction_formula", monitor.construction_formula},
        {"template", templ},
        {"template_source", frontend_valid ? "frontend" : "suffix-heuristic"},
        {"index_tuple", indices},
        {"support", support},
        {"arity_kind", arity_kind},
        {"state_count", monitor.automaton->num_states()},
        {"latch_literals", latch_literals},
        {"role", monitor.role},
        {"source_origin", nullptr},
        {"provenance_source", "suffix-heuristic"}};
    if (monitor.role == "justice")
      record["justice_index"] = justice_index++;
    if (frontend_valid) {
      const json::object *matched = nullptr;
      for (const auto &[candidate, item] : candidates) {
        limits.check("provenance-match");
        if (canonical_formula_text(candidate) == text ||
            checked_call(limits, "provenance-equivalence", [&] {
              return formula_equal(candidate, raw, limits);
            })) {
          if (matched) {
            matched = nullptr;
            break;
          }
          matched = &item;
        }
      }
      if (matched) {
        const auto &bindings = matched->at("bindings").as_array();
        json::array bound_indices;
        for (const auto &binding : bindings)
          bound_indices.push_back(binding.as_object().at("value"));
        record["source_origin"] = json::object{
            {"block", matched->at("block")},
            {"source_formula_id", matched->at("source_formula_id")},
            {"source_node_id", matched->at("source_node_id")},
            {"generated_position", matched->at("generated_position")},
            {"bindings", bindings},
            {"index_tuple", bound_indices},
            {"signal_refs", matched->at("signal_refs")},
            {"signals", matched->at("signals")}};
        record["source_binding"] = json::object{
            {"source_formula_id", matched->at("source_formula_id")},
            {"generated_position", matched->at("generated_position")},
            {"source_node_id", matched->at("source_node_id")}};
        record["index_tuple"] = bound_indices;
        record["provenance_source"] = "frontend";
      }
    }
    available &= record.at("provenance_source") == "frontend";
    if (arity_kind == "bus_wide" && raw.kind() == Op::G &&
        raw[0].is_boolean()) {
      json::value signature = symmetric_signature(raw, buses, limits);
      record["symmetric"] = signature.is_object();
      if (signature.is_object())
        record["symmetric_signature"] = signature;
    }
    monitor_records.push_back(std::move(record));
  }
  std::string reason;
  if (!available) {
    if (!pipeline->frontend_provenance_json)
      reason = "frontend provenance was not requested";
    else if (!frontend_valid)
      reason = "frontend provenance is ambiguous or signal inventory differs";
    else
      reason = "expanded monitor has no unique source conjunct";
  }
  json::object origin{
      {"available", available},
      {"provenance_source", available ? "frontend" : "suffix-heuristic"},
      {"reason", available ? json::value(nullptr) : json::value(reason)},
      {"source_sha256", frontend_valid ? json::value(pipeline->source_sha256)
                                       : json::value(nullptr)}};
  return json::object{
      {"schema", "tlsf-tools.gr1-monitor-game.provenance.v3"},
      {"provenance_source", available ? "frontend" : "suffix-heuristic"},
      {"semantics", strict ? "strict" : "exact"},
      {"latch_encoding", "one-hot"},
      {"inputs", input_records},
      {"outputs", output_records},
      {"source_parameters", frontend_valid
                                ? frontend.as_object().at("parameters")
                                : json::value(json::array{})},
      {"source_conjuncts", source_conjuncts},
      {"monitors", monitor_records},
      {"violated_latch_literal", encoded.has_violated
                                     ? json::value(encoded.violated)
                                     : json::value(nullptr)},
      {"source_origin_metadata", origin}};
}

char *copy_text(const std::string &text) {
  if (text.size() == SIZE_MAX)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, "publish-size",
                  "text size overflow");
  char *result = static_cast<char *>(malloc(text.size() + 1));
  if (!result)
    throw std::bad_alloc();
  memcpy(result, text.data(), text.size());
  result[text.size()] = '\0';
  return result;
}

void report(TlsfGr1ReductionError *error, TlsfGr1ReductionStatus status,
            const char *stage, const char *message) {
  if (!error)
    return;
  *error = {};
  error->status = status;
  snprintf(error->stage, sizeof error->stage, "%s", stage);
  snprintf(error->message, sizeof error->message, "%s", message);
}

} // namespace

extern "C" void tlsf_gr1_reduction_clear(TlsfGr1Reduction *result) {
  if (!result)
    return;
  aig_free(result->game);
  free(result->aag);
  free(result->metadata_json);
  free(result->provenance_json);
  free(result->symbol_map);
  *result = {};
}

extern "C" TlsfGr1ReductionStatus
tlsf_gr1_reduce_v1(const TlsfPipeline *pipeline,
                   const TlsfGr1ReductionOptions *options,
                   TlsfGr1Reduction *result, TlsfGr1ReductionError *error,
                   TlsfGr1ReductionStatus *failure_status) {
  if (failure_status)
    *failure_status = TLSF_GR1_REDUCE_OK;
  TlsfGr1ReductionStats *stats = options ? options->stats : nullptr;
  if (stats)
    *stats = {};
  if (result && (result->game || result->aag || result->aag_size ||
                 result->metadata_json || result->metadata_size ||
                 result->provenance_json || result->provenance_size ||
                 result->symbol_map || result->symbol_map_size)) {
    report(error, TLSF_GR1_REDUCE_INVALID, "reduce", "result must be empty");
    if (failure_status)
      *failure_status = TLSF_GR1_REDUCE_INVALID;
    return TLSF_GR1_REDUCE_INVALID;
  }
  if (!pipeline || !pipeline->spec || !pipeline->source_bytes ||
      !pipeline->source_size || !options || !result ||
      !options->max_artifact_bytes || !options->max_monitor_states ||
      (options->semantics != TLSF_GR1_EXACT &&
       options->semantics != TLSF_GR1_STRICT)) {
    report(error, TLSF_GR1_REDUCE_INVALID, "reduce", "invalid argument");
    if (failure_status)
      *failure_status = TLSF_GR1_REDUCE_INVALID;
    return TLSF_GR1_REDUCE_INVALID;
  }
  TlsfGr1ConstructionWork local_work{};
  TlsfGr1ConstructionWork &work = stats ? stats->work : local_work;
  const TlsfGr1ConstructionBudget &budget = options->budget;
  try {
    StatsScope source_stats(*options, TLSF_GR1_REDUCE_STATS_SOURCE);
    Limits limits{*options, work};
    limits.check("reduce");
    char snapshot_sha256[65];
    sha256_hex(pipeline->source_bytes, pipeline->source_size, snapshot_sha256);
    if (memcmp(snapshot_sha256, pipeline->source_sha256,
               sizeof snapshot_sha256) != 0)
      throw Failure(TLSF_GR1_REDUCE_INVALID, TLSF_GR1_REDUCE_INVALID, "source",
                    "source snapshot SHA-256 mismatch");
    const TlsfSpec *spec = pipeline->spec;
    if (spec->info.semantics != SEM_MEALY || spec->info.target != TARGET_MEALY)
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_UNSUPPORTED,
                    "semantics", "unsupported non-Mealy SEMANTICS/TARGET");
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
    reduction_test_source(spec);
#endif
    std::vector<std::string> inputs, outputs;
    std::map<std::string, std::string> symbols;
    for (uint32_t i = 0; i < spec->input_count; ++i) {
      std::string name(spec->inputs[i].name);
      if (!symbols.emplace(name, "uncontrollable_i" + std::to_string(i)).second)
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                      "signals", "expanded TLSF signal names are not unique");
      inputs.push_back(name);
    }
    for (uint32_t i = 0; i < spec->output_count; ++i) {
      std::string name(spec->outputs[i].name);
      if (!symbols.emplace(name, "controllable_o" + std::to_string(i)).second)
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                      "signals", "expanded TLSF signal names are not unique");
      outputs.push_back(name);
    }
    Formula formula = checked_call(limits, "parse-formula", [&] {
      gr1_formula::Replacements replacements;
      for (const auto &[raw, encoded] : symbols)
        replacements.emplace(raw, Formula::ap(encoded));
      return gr1_formula::relabel(lowered_formula(const_cast<TlsfSpec *>(spec)),
                                  &replacements);
    });
    std::set<std::string> encoded_names;
    for (const auto &[raw, encoded] : symbols)
      encoded_names.insert(encoded);
    // Declared names are encoded above. Retain the legacy error disposition
    // for malformed lowered names, before the ordinary undeclared-AP guard.
    for (const auto &name : ap_names(formula))
      if (!encoded_names.count(name) &&
          std::any_of(name.begin(), name.end(), [](unsigned char c) {
            return !std::isalnum(c) && c != '_';
          }))
        throw Failure(TLSF_GR1_REDUCE_ERROR, TLSF_GR1_REDUCE_ERROR, "formula",
                      "lowered formula has undeclared APs");
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
    reduction_test_formula("source", formula);
#endif
    for (const auto &name : ap_names(formula))
      if (!encoded_names.count(name))
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, TLSF_GR1_REDUCE_ERROR,
                      "formula", "lowered formula has undeclared APs");
    std::vector<Formula> assumptions, guarantees;
    if (formula.kind() == Op::Implies) {
      conjuncts(formula[0], assumptions);
      conjuncts(formula[1], guarantees);
    } else {
      conjuncts(formula, guarantees);
    }
    precheck(assumptions, guarantees, ap_names(formula).size(), limits);
    source_stats.finish();
    StatsScope monitor_stats(*options, TLSF_GR1_REDUCE_STATS_MONITORS);
    std::vector<Monitor> monitors;
    auto append = [&](Formula item, bool assumption) {
      Monitor monitor = make_monitor(item, assumption, limits);
      monitor.construction_formula =
          checked_call(limits, "provenance-construction", [&] {
            return canonical_formula_text(raw_formula(item, symbols));
          });
      work.states = checked_add(work.states, monitor.automaton->num_states(),
                                "budget-monitor");
      work.edges = checked_add(work.edges, monitor.automaton->num_edges(),
                               "budget-monitor");
      work.monitors_completed++;
      if ((budget.max_total_states && work.states > budget.max_total_states) ||
          (budget.max_total_edges && work.edges > budget.max_total_edges))
        throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT,
                      "budget-monitor",
                      "total monitor state or edge limit exceeded");
      if (stats)
        stats->monitor_states = work.states;
      if (work.states > options->max_monitor_states)
        throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, "monitor",
                      "total monitor state cap exceeded");
      monitors.push_back(std::move(monitor));
      if (stats)
        stats->monitor_count = monitors.size();
    };
    for (Formula item : assumptions)
      append(item, true);
    for (Formula item : guarantees)
      append(item, false);
    if (stats) {
      stats->monitor_count = monitors.size();
      stats->monitor_states = work.states;
    }
    monitor_stats.finish();
    StatsScope encode_stats(*options, TLSF_GR1_REDUCE_STATS_ENCODE);
    bool strict = options->semantics == TLSF_GR1_STRICT;
    Encoded encoded = encode(monitors, inputs, outputs, strict, limits);
    encode_stats.finish();
    StatsScope publish_stats(*options, TLSF_GR1_REDUCE_STATS_PUBLISH);
    std::string provenance_json = json::serialize(provenance(
        pipeline, monitors, inputs, outputs, symbols, strict, encoded, limits));
    provenance_json += '\n';
    limits.bytes(provenance_json.size(), "provenance");
    char aag_sha256[65];
    sha256_hex(encoded.aag.data(), encoded.aag.size(), aag_sha256);
    std::string symbol_map = "tlsf-tools.game-symbol-map.v1\n";
    symbol_map += aag_sha256;
    symbol_map += '\n';
    for (const auto &name : inputs)
      symbol_map += "I\t" + symbols.at(name) + "\t" + name + "\n";
    for (const auto &name : outputs)
      symbol_map += "O\t" + symbols.at(name) + "\t" + name + "\n";
    json::object metadata{{"schema", "tlsf-tools.gr1-monitor-game.metadata.v1"},
                          {"semantics", strict ? "strict" : "exact"},
                          {"game_sha256", aag_sha256},
                          {"source_sha256", pipeline->source_sha256},
                          {"monitor_count", monitors.size()},
                          {"fallback_monitor_count",
                           std::count_if(monitors.begin(), monitors.end(),
                                         [](const Monitor &monitor) {
                                           return monitor.fallback_used;
                                         })},
                          {"justice_count", encoded.justice},
                          {"fairness_count", encoded.fairness}};
    std::string metadata_json = json::serialize(metadata) + '\n';
    limits.bytes(
        checked_add(metadata_json.size(), symbol_map.size(), "metadata-size"),
        "metadata");
    File source(fmemopen(encoded.aag.data(), encoded.aag.size(), "r"));
    if (!source)
      throw Failure(TLSF_GR1_REDUCE_LIMIT, TLSF_GR1_REDUCE_LIMIT, "aag",
                    "cannot open memory stream");
    Aig *game = aig_read_aag(source.get());
    if (!game)
      throw Failure(TLSF_GR1_REDUCE_ERROR, TLSF_GR1_REDUCE_ERROR, "aag",
                    "generated AAG is invalid");
    if (stats) {
      stats->game_latches = aig_num_latches(game);
      stats->game_ands = aig_num_ands(game);
    }
    result->game = game;
    result->aag = copy_text(encoded.aag);
    result->aag_size = encoded.aag.size();
    result->metadata_json = copy_text(metadata_json);
    result->metadata_size = metadata_json.size();
    result->provenance_json = copy_text(provenance_json);
    result->provenance_size = provenance_json.size();
    result->symbol_map = copy_text(symbol_map);
    result->symbol_map_size = symbol_map.size();
#ifdef TLSF_GR1_REDUCTION_TEST_FAULT
    reduction_test_provenance(result, options->semantics);
#endif
    report(error, TLSF_GR1_REDUCE_OK, "reduce", "");
    return TLSF_GR1_REDUCE_OK;
  } catch (const Failure &failure) {
    tlsf_gr1_reduction_clear(result);
    report(error, failure.status, failure.stage, failure.what());
    if (failure_status)
      *failure_status = failure.failure_status;
    return failure.status;
  } catch (const std::bad_alloc &) {
    tlsf_gr1_reduction_clear(result);
    report(error, TLSF_GR1_REDUCE_LIMIT, "allocation",
           "host allocation failed");
    if (failure_status)
      *failure_status = TLSF_GR1_REDUCE_LIMIT;
    return TLSF_GR1_REDUCE_LIMIT;
  } catch (const std::exception &failure) {
    tlsf_gr1_reduction_clear(result);
    report(error, TLSF_GR1_REDUCE_ERROR, "reduce", failure.what());
    if (failure_status)
      *failure_status = TLSF_GR1_REDUCE_ERROR;
    return TLSF_GR1_REDUCE_ERROR;
  } catch (...) {
    tlsf_gr1_reduction_clear(result);
    report(error, TLSF_GR1_REDUCE_ERROR, "reduce", "unknown exception");
    if (failure_status)
      *failure_status = TLSF_GR1_REDUCE_ERROR;
    return TLSF_GR1_REDUCE_ERROR;
  }
}

extern "C" TlsfGr1ReductionStatus
tlsf_gr1_reduce(const TlsfPipeline *pipeline,
                const TlsfGr1ReductionOptions *options,
                TlsfGr1Reduction *result, TlsfGr1ReductionError *error) {
  return tlsf_gr1_reduce_v1(pipeline, options, result, error, nullptr);
}
