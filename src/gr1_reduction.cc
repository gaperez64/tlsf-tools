#define _GNU_SOURCE
#include "tlsf/gr1_reduction.h"

extern "C" {
#include "sha256.h"
#include "tlsf/classify.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/spec.h"
}

#include "yyjson_cpp.hh"
#include <spot/misc/optionmap.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/hierarchy.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/tl/relabel.hh>
#include <spot/tl/simplify.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/translate.hh>

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
#include <memory>
#include <regex>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {
namespace json = tlsf_json;
using Formula = spot::formula;

struct Failure : std::runtime_error {
  TlsfGr1ReductionStatus status;
  const char *stage;
  Failure(TlsfGr1ReductionStatus s, const char *at, const std::string &why)
      : std::runtime_error(why), status(s), stage(at) {}
};

struct Limits {
  const TlsfGr1ReductionOptions &options;
  void check(const char *stage) const {
    if (options.cancelled && options.cancelled(options.cancel_ctx))
      throw Failure(TLSF_GR1_REDUCE_CANCELLED, stage, "cancelled");
    if (options.deadline_mono_ns) {
      struct timespec now;
      if (clock_gettime(CLOCK_MONOTONIC, &now) != 0)
        throw Failure(TLSF_GR1_REDUCE_ERROR, stage, "monotonic clock failed");
      uint64_t ns = uint64_t(now.tv_sec) * 1000000000ull + now.tv_nsec;
      if (ns >= options.deadline_mono_ns)
        throw Failure(TLSF_GR1_REDUCE_DEADLINE, stage, "deadline exceeded");
    }
  }
  void bytes(size_t n, const char *stage) const {
    check(stage);
    if (options.max_artifact_bytes && n > options.max_artifact_bytes)
      throw Failure(TLSF_GR1_REDUCE_LIMIT, stage, "artifact byte cap exceeded");
  }
};

template <typename F>
auto spot_call(const Limits &limits, const char *stage, F &&call) {
  limits.check(stage);
  auto result = call();
  limits.check(stage);
  return result;
}

std::string canonical_formula_text(Formula formula) {
  auto kind = formula.kind();
  if (kind == spot::op::And || kind == spot::op::Or) {
    std::vector<std::string> children;
    for (Formula child : formula)
      children.push_back(canonical_formula_text(child));
    std::sort(children.begin(), children.end());
    std::string text = "(";
    for (size_t i = 0; i < children.size(); ++i) {
      if (i)
        text += kind == spot::op::And ? " & " : " | ";
      text += children[i];
    }
    return text + ")";
  }
  const char *prefix = nullptr;
  switch (kind) {
  case spot::op::G:
    prefix = "G";
    break;
  case spot::op::F:
    prefix = "F";
    break;
  case spot::op::X:
    prefix = "X";
    break;
  case spot::op::Not:
    prefix = "!";
    break;
  default:
    break;
  }
  if (prefix)
    return std::string(prefix) + "(" + canonical_formula_text(formula[0]) + ")";
  const char *binary = nullptr;
  switch (kind) {
  case spot::op::Xor:
    binary = "xor";
    break;
  case spot::op::Implies:
    binary = "->";
    break;
  case spot::op::Equiv:
    binary = "<->";
    break;
  case spot::op::U:
    binary = "U";
    break;
  case spot::op::R:
    binary = "R";
    break;
  case spot::op::W:
    binary = "W";
    break;
  case spot::op::M:
    binary = "M";
    break;
  default:
    break;
  }
  if (binary) {
    std::string lhs = canonical_formula_text(formula[0]);
    std::string rhs = canonical_formula_text(formula[1]);
    if ((kind == spot::op::Xor || kind == spot::op::Equiv) && lhs > rhs)
      std::swap(lhs, rhs);
    return "(" + lhs + " " + binary + " " + rhs + ")";
  }
  return spot::str_psl(formula);
}

struct FileCloser {
  void operator()(FILE *fp) const {
    if (fp)
      fclose(fp);
  }
};
using File = std::unique_ptr<FILE, FileCloser>;

std::string printed_ltl(TlsfSpec *spec) {
  ClassifiedSpec *classes = classify_spec(spec);
  if (!classes)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, "lower", "classification failed");
  Node *root = build_spec_formula(spec, classes, PRINT_ALL);
  if (!root)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, "lower", "formula build failed");
  char *buffer = nullptr;
  size_t length = 0;
  File stream(open_memstream(&buffer, &length));
  if (!stream)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, "lower", "out of memory");
  print_ltl(stream.get(), root, LTL_FMT_LTL, false, false, false);
  if (fflush(stream.get()) != 0) {
    stream.reset();
    free(buffer);
    throw Failure(TLSF_GR1_REDUCE_LIMIT, "lower", "formula output failed");
  }
  stream.reset();
  std::unique_ptr<char, void (*)(void *)> owned(buffer, free);
  std::string result(buffer, length);
  return result;
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
  if (formula.kind() == spot::op::And) {
    for (Formula child : formula)
      conjuncts(child, out);
  } else if (formula.kind() == spot::op::G &&
             formula[0].kind() == spot::op::And) {
    for (Formula child : formula[0])
      conjuncts(Formula::G(child), out);
  } else if (!formula.is_tt()) {
    out.push_back(formula);
  }
}

struct Monitor {
  bool assumption;
  Formula formula;
  char mp_class;
  spot::twa_graph_ptr automaton;
  std::vector<bool> accepting;
  std::vector<bool> rejecting;
  std::vector<uint32_t> latches;
  std::string role;
  bool fallback_used = false;
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

Monitor make_monitor(Formula formula, bool assumption, const Limits &limits) {
  limits.check("monitor");
  char klass =
      spot_call(limits, "mp-class", [&] { return spot::mp_class(formula); });
  if (std::string("BGSOR").find(klass) == std::string::npos)
    throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "mp-class",
                  "not DBA reducible: " + spot::str_psl(formula));
  spot::option_map spot_options;
  spot_options.set("det-max-states",
                   int(std::min<uint32_t>(limits.options.max_monitor_states,
                                          std::numeric_limits<int>::max())));
  spot_options.set(
      "wdba-det-max",
      int(std::min<uint32_t>(limits.options.max_monitor_states, 4096)));
  spot::translator translator(&spot_options);
  translator.set_type(spot::postprocessor::BA);
  translator.set_pref(spot::postprocessor::Complete |
                      spot::postprocessor::SBAcc |
                      spot::postprocessor::Deterministic);
  auto automaton =
      spot_call(limits, "translate", [&] { return translator.run(&formula); });
  if (!automaton)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, "translate",
                  "Spot translation reached its state limit");
  bool fallback_used = false;
  if (!spot_call(limits, "determinism",
                 [&] { return spot::is_deterministic(automaton); })) {
    fallback_used = true;
    spot::output_aborter aborter(limits.options.max_monitor_states);
    auto parity = spot_call(limits, "determinize", [&] {
      return spot::tgba_determinize(automaton, false, true, true, true,
                                    &aborter);
    });
    if (!parity)
      throw Failure(TLSF_GR1_REDUCE_LIMIT, "determinize",
                    "Spot determinization failed");
    auto deterministic = spot_call(limits, "parity-to-buchi", [&] {
      return spot::rabin_to_buchi_if_realizable(parity);
    });
    if (!deterministic)
      deterministic = spot_call(limits, "parity-to-buchi", [&] {
        return spot::rabin_to_buchi_maybe(parity);
      });
    if (!deterministic)
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "determinize",
                    "Spot could not construct recurrence DBA monitor");
    automaton = deterministic;
  }
  automaton =
      spot_call(limits, "sbacc", [&] { return spot::sbacc(automaton); });
  automaton =
      spot_call(limits, "complete", [&] { return spot::complete(automaton); });
  if (!spot_call(limits, "determinism",
                 [&] { return spot::is_deterministic(automaton); }) ||
      !spot_call(limits, "completeness",
                 [&] { return spot::is_complete(automaton); }))
    throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "monitor",
                  "Spot produced nondeterministic or incomplete monitor");
  if (limits.options.max_monitor_states &&
      automaton->num_states() > limits.options.max_monitor_states)
    throw Failure(TLSF_GR1_REDUCE_LIMIT, "monitor",
                  "monitor state cap exceeded");
  Monitor monitor{assumption, formula, klass, automaton,    {},
                  {},         {},      {},    fallback_used};
  for (unsigned state = 0; state < automaton->num_states(); ++state) {
    limits.check("monitor");
    int mark = -1;
    for (const auto &edge : automaton->out(state)) {
      int current = bool(edge.acc);
      if (mark >= 0 && mark != current)
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "monitor",
                      "Spot did not produce state-based acceptance");
      mark = current;
    }
    if (mark < 0)
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "monitor", "empty state");
    monitor.accepting.push_back(bool(mark));
  }
  monitor.rejecting = rejecting_states(monitor, limits);
  if (klass == 'B' || klass == 'S')
    for (unsigned state = 0; state < automaton->num_states(); ++state)
      if (monitor.rejecting[state])
        for (const auto &edge : automaton->out(state))
          if (!monitor.rejecting[edge.dst])
            throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "monitor",
                          "non-sticky safety rejecting region");
  return monitor;
}

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
  explicit AagBuilder(std::vector<std::string> inputs)
      : names(std::move(inputs)) {
    for (const auto &name : names)
      literals.emplace(name, 2 * ++next_var);
  }
  uint32_t latch(uint32_t reset, std::string name) {
    uint32_t current = 2 * ++next_var;
    latches.push_back({current, 0, reset, std::move(name)});
    return current;
  }
  void set_next(uint32_t current, uint32_t next) {
    for (auto &item : latches)
      if (item.current == current) {
        item.next = next;
        return;
      }
    throw Failure(TLSF_GR1_REDUCE_ERROR, "aag", "unknown latch");
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
    uint32_t result = 2 * ++next_var;
    ands.push_back({result, a, b});
    cache.emplace(key, result);
    return result;
  }
  uint32_t lor(uint32_t a, uint32_t b) { return land(a ^ 1u, b ^ 1u) ^ 1u; }
  uint32_t compile(Formula f) {
    if (f.is_tt())
      return 1;
    if (f.is_ff())
      return 0;
    switch (f.kind()) {
    case spot::op::ap: {
      auto found = literals.find(f.ap_name());
      if (found == literals.end())
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "transition",
                      "monitor refers to undeclared AP");
      return found->second;
    }
    case spot::op::Not:
      return compile(f[0]) ^ 1u;
    case spot::op::And: {
      uint32_t result = 1;
      for (Formula child : f)
        result = land(result, compile(child));
      return result;
    }
    case spot::op::Or: {
      uint32_t result = 0;
      for (Formula child : f)
        result = lor(result, compile(child));
      return result;
    }
    case spot::op::Xor: {
      uint32_t a = compile(f[0]), b = compile(f[1]);
      return lor(land(a, b ^ 1u), land(a ^ 1u, b));
    }
    case spot::op::Implies:
      return lor(compile(f[0]) ^ 1u, compile(f[1]));
    case spot::op::Equiv: {
      uint32_t a = compile(f[0]), b = compile(f[1]);
      return lor(land(a, b), land(a ^ 1u, b ^ 1u));
    }
    default:
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "transition",
                    "non-Boolean monitor transition label");
    }
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
        Formula condition = spot_call(limits, "transition-formula", [&] {
          return spot::parse_formula(spot::bdd_format_formula(
              monitor.automaton->get_dict(), edge.cond));
        });
        uint32_t literal = builder.compile(condition);
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
  spot::relabeling_map replacements;
  for (const auto &[raw, encoded] : symbols)
    replacements.emplace(Formula::ap(encoded), Formula::ap(raw));
  return spot::relabel_apply(canonical, &replacements);
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
  spot::atomic_prop_set aps;
  spot::atomic_prop_collect(formula, &aps);
  for (Formula ap : aps)
    names.insert(ap.ap_name());
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
  spot::relabeling_map replacements;
  for (const auto &[direction, ordinal, indices, name] : ordered) {
    std::string alias = "s_" + direction + "_" + std::to_string(ordinal);
    for (unsigned value : indices) {
      auto [it, inserted] = coordinates.emplace(value, coordinates.size());
      (void)inserted;
      alias += "_i" + std::to_string(it->second);
    }
    replacements.emplace(Formula::ap(name), Formula::ap(alias));
  }
  return canonical_formula_text(spot_call(limits, "template-relabel", [&] {
    return spot::relabel_apply(formula, &replacements);
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

bool boolean_eval(Formula formula,
                  const std::map<std::string, bool> &valuation) {
  if (formula.is_tt())
    return true;
  if (formula.is_ff())
    return false;
  switch (formula.kind()) {
  case spot::op::ap:
    return valuation.at(formula.ap_name());
  case spot::op::Not:
    return !boolean_eval(formula[0], valuation);
  case spot::op::And:
    for (Formula child : formula)
      if (!boolean_eval(child, valuation))
        return false;
    return true;
  case spot::op::Or:
    for (Formula child : formula)
      if (boolean_eval(child, valuation))
        return true;
    return false;
  case spot::op::Xor:
    return boolean_eval(formula[0], valuation) !=
           boolean_eval(formula[1], valuation);
  case spot::op::Implies:
    return !boolean_eval(formula[0], valuation) ||
           boolean_eval(formula[1], valuation);
  case spot::op::Equiv:
    return boolean_eval(formula[0], valuation) ==
           boolean_eval(formula[1], valuation);
  default:
    throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "provenance",
                  "non-Boolean symmetric monitor body");
  }
}

json::value symmetric_signature(Formula formula, const Buses &buses,
                                const Limits &limits) {
  if (formula.kind() != spot::op::G || !formula[0].is_boolean())
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
      spot::relabeling_map swap;
      swap.emplace(Formula::ap(members[i - 1].first),
                   Formula::ap(members[i].first));
      swap.emplace(Formula::ap(members[i].first),
                   Formula::ap(members[i - 1].first));
      Formula swapped = spot_call(limits, "symmetry-relabel", [&] {
        return spot::relabel_apply(body, &swap);
      });
      if (!spot_call(limits, "symmetry-equivalence",
                     [&] { return spot::are_equivalent(body, swapped); }))
        return false;
    }
    for (const auto &[name, indices] : members)
      bus_names.insert(name);
  }
  for (const std::string &scalar : names)
    if (!bus_names.count(scalar)) {
      limits.check("symmetry");
      spot::relabeling_map when_false, when_true;
      when_false.emplace(Formula::ap(scalar), Formula::ff());
      when_true.emplace(Formula::ap(scalar), Formula::tt());
      Formula lhs = spot_call(limits, "symmetry-relabel", [&] {
        return spot::relabel_apply(body, &when_false);
      });
      Formula rhs = spot_call(limits, "symmetry-relabel", [&] {
        return spot::relabel_apply(body, &when_true);
      });
      if (!spot_call(limits, "symmetry-equivalence",
                     [&] { return spot::are_equivalent(lhs, rhs); }))
        return false;
    }
  std::vector<std::pair<std::string, std::vector<BusMember>>> ordered(
      relevant.begin(), relevant.end());
  size_t valuations = 1;
  for (const auto &[base, members] : ordered) {
    (void)base;
    if (valuations > 1000000 / (members.size() + 1))
      throw Failure(TLSF_GR1_REDUCE_LIMIT, "symmetry",
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
        Formula parsed = spot_call(limits, "provenance-parse", [&] {
          return raw_formula(spot::parse_formula(canonicalize(text, symbols)),
                             symbols);
        });
        if (item.at("block") == "REQUIRE" || item.at("block") == "ASSERT")
          parsed = Formula::G(parsed);
        json::object row = item;
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
    Formula raw = spot_call(limits, "provenance-relabel", [&] {
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
            spot_call(limits, "provenance-equivalence",
                      [&] { return spot::are_equivalent(candidate, raw); })) {
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
        record["index_tuple"] = bound_indices;
        record["provenance_source"] = "frontend";
      }
    }
    available &= record.at("provenance_source") == "frontend";
    if (arity_kind == "bus_wide" && raw.kind() == spot::op::G &&
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
tlsf_gr1_reduce(const TlsfPipeline *pipeline,
                const TlsfGr1ReductionOptions *options,
                TlsfGr1Reduction *result, TlsfGr1ReductionError *error) {
  if (result && (result->game || result->aag || result->aag_size ||
                 result->metadata_json || result->metadata_size ||
                 result->provenance_json || result->provenance_size ||
                 result->symbol_map || result->symbol_map_size)) {
    report(error, TLSF_GR1_REDUCE_INVALID, "reduce", "result must be empty");
    return TLSF_GR1_REDUCE_INVALID;
  }
  if (!pipeline || !pipeline->spec || !pipeline->source_bytes ||
      !pipeline->source_size || !options || !result ||
      !options->max_artifact_bytes || !options->max_monitor_states ||
      (options->semantics != TLSF_GR1_EXACT &&
       options->semantics != TLSF_GR1_STRICT)) {
    report(error, TLSF_GR1_REDUCE_INVALID, "reduce", "invalid argument");
    return TLSF_GR1_REDUCE_INVALID;
  }
  try {
    Limits limits{*options};
    limits.check("reduce");
    char snapshot_sha256[65];
    sha256_hex(pipeline->source_bytes, pipeline->source_size, snapshot_sha256);
    if (memcmp(snapshot_sha256, pipeline->source_sha256,
               sizeof snapshot_sha256) != 0)
      throw Failure(TLSF_GR1_REDUCE_INVALID, "source",
                    "source snapshot SHA-256 mismatch");
    const TlsfSpec *spec = pipeline->spec;
    if (spec->info.semantics != SEM_MEALY || spec->info.target != TARGET_MEALY)
      throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "semantics",
                    "unsupported non-Mealy SEMANTICS/TARGET");
    std::vector<std::string> inputs, outputs;
    std::map<std::string, std::string> symbols;
    for (uint32_t i = 0; i < spec->input_count; ++i) {
      std::string name(spec->inputs[i].name);
      if (!symbols.emplace(name, "uncontrollable_i" + std::to_string(i)).second)
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "signals",
                      "expanded TLSF signal names are not unique");
      inputs.push_back(name);
    }
    for (uint32_t i = 0; i < spec->output_count; ++i) {
      std::string name(spec->outputs[i].name);
      if (!symbols.emplace(name, "controllable_o" + std::to_string(i)).second)
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "signals",
                      "expanded TLSF signal names are not unique");
      outputs.push_back(name);
    }
    Formula formula = spot_call(limits, "parse-formula", [&] {
      return spot::parse_formula(
          canonicalize(printed_ltl(const_cast<TlsfSpec *>(spec)), symbols));
    });
    std::set<std::string> encoded_names;
    for (const auto &[raw, encoded] : symbols)
      encoded_names.insert(encoded);
    for (const auto &name : ap_names(formula))
      if (!encoded_names.count(name))
        throw Failure(TLSF_GR1_REDUCE_UNSUPPORTED, "formula",
                      "lowered formula has undeclared APs");
    std::vector<Formula> assumptions, guarantees;
    if (formula.kind() == spot::op::Implies) {
      conjuncts(formula[0], assumptions);
      conjuncts(formula[1], guarantees);
    } else {
      conjuncts(formula, guarantees);
    }
    std::vector<Monitor> monitors;
    uint64_t total_states = 0;
    auto append = [&](Formula item, bool assumption) {
      Monitor monitor = make_monitor(item, assumption, limits);
      total_states += monitor.automaton->num_states();
      if (total_states > options->max_monitor_states)
        throw Failure(TLSF_GR1_REDUCE_LIMIT, "monitor",
                      "total monitor state cap exceeded");
      monitors.push_back(std::move(monitor));
    };
    for (Formula item : assumptions)
      append(item, true);
    for (Formula item : guarantees)
      append(item, false);
    bool strict = options->semantics == TLSF_GR1_STRICT;
    Encoded encoded = encode(monitors, inputs, outputs, strict, limits);
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
    limits.bytes(metadata_json.size() + symbol_map.size(), "metadata");
    File source(fmemopen(encoded.aag.data(), encoded.aag.size(), "r"));
    if (!source)
      throw Failure(TLSF_GR1_REDUCE_LIMIT, "aag", "cannot open memory stream");
    Aig *game = aig_read_aag(source.get());
    if (!game)
      throw Failure(TLSF_GR1_REDUCE_ERROR, "aag", "generated AAG is invalid");
    result->game = game;
    result->aag = copy_text(encoded.aag);
    result->aag_size = encoded.aag.size();
    result->metadata_json = copy_text(metadata_json);
    result->metadata_size = metadata_json.size();
    result->provenance_json = copy_text(provenance_json);
    result->provenance_size = provenance_json.size();
    result->symbol_map = copy_text(symbol_map);
    result->symbol_map_size = symbol_map.size();
    report(error, TLSF_GR1_REDUCE_OK, "reduce", "");
    return TLSF_GR1_REDUCE_OK;
  } catch (const Failure &failure) {
    tlsf_gr1_reduction_clear(result);
    report(error, failure.status, failure.stage, failure.what());
    return failure.status;
  } catch (const std::bad_alloc &) {
    tlsf_gr1_reduction_clear(result);
    report(error, TLSF_GR1_REDUCE_LIMIT, "reduce", "out of memory");
    return TLSF_GR1_REDUCE_LIMIT;
  } catch (const std::exception &failure) {
    tlsf_gr1_reduction_clear(result);
    report(error, TLSF_GR1_REDUCE_ERROR, "reduce", failure.what());
    return TLSF_GR1_REDUCE_ERROR;
  } catch (...) {
    tlsf_gr1_reduction_clear(result);
    report(error, TLSF_GR1_REDUCE_ERROR, "reduce", "unknown exception");
    return TLSF_GR1_REDUCE_ERROR;
  }
}
