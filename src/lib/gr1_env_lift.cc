#include "gr1_shared.hh"
#include "tlsf/gr1_oxidd.h"
#include "tlsf/oxidd_options.h"
#include "pipeline_source_internal.h"
extern "C" {
#include "sha256.h"
}

#include <array>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <numeric>
#include <optional>
#include <regex>
#include <sstream>
#include <tuple>
#include <unordered_map>
#include <unordered_set>

namespace gr1_lift_internal {
struct EnvWindow {
  std::string axis;
  std::vector<int> target_members;
  std::vector<std::unique_ptr<Instance>> seeds;
};
#ifdef TLSF_GR1_LIFT_TEST_FAULT
thread_local int env_rank_fault = 0;
#endif

std::pair<std::set<std::string>, std::set<std::string>>
env_typed_classes(const Instance &i) {
  std::set<std::string> monitors, conjuncts;
  for (const J &value : i.data.at("monitors").as_array()) {
    const O &row = value.as_object();
    const O &origin = row.at("source_origin").as_object();
    monitors.insert(key({s(origin, "source_formula_id"), s(row, "role"),
                         s(row, "side"), s(row, "mp_class")}));
  }
  for (const J &value : i.data.at("source_conjuncts").as_array())
    conjuncts.insert(s(value.as_object(), "source_formula_id"));
  return {monitors, conjuncts};
}

void env_reduction_binding(const Instance &i, const std::string &source_hash) {
  if (!i.r.metadata_json || !i.r.aag)
    decline("target_binding", "missing reduction metadata or game");
  const O metadata =
      j::parse(std::string_view(i.r.metadata_json, i.r.metadata_size))
          .as_object();
  char game_hash[65]{};
  sha256_hex(i.r.aag, i.r.aag_size, game_hash);
  const O &origin = i.data.at("source_origin_metadata").as_object();
  if (s(metadata, "schema") != "tlsf-tools.gr1-monitor-game.metadata.v1" ||
      s(metadata, "semantics") != "exact" ||
      s(metadata, "source_sha256") != source_hash ||
      s(metadata, "game_sha256") != game_hash ||
      s(origin, "source_sha256") != source_hash)
    decline("target_binding", "source or reduction hash differs");
}

void env_typed_axis(const Instance &i, const std::string &axis) {
  std::string axis_id;
  std::set<std::string> parameter_ids;
  for (const J &value : i.data.at("source_parameters").as_array()) {
    const O &row = value.as_object();
    auto id = field(n(row, "id"));
    if (!parameter_ids.insert(id).second)
      decline("typed_alignment", "duplicate parameter identity");
    if (s(row, "name") == axis)
      axis_id = id;
  }
  if (axis_id.empty())
    decline("typed_alignment", "selected parameter identity is absent");
  std::map<std::string, std::pair<std::string, std::set<std::string>>> declared;
  bool indexed = false;
  for (const char *group : {"inputs", "outputs"})
    for (const J &value : i.data.at(group).as_array()) {
      const O &row = value.as_object();
      std::string role = s(row, "index_role");
      if (role != "scalar" && role != "element" && role != "representation-bit")
        decline("typed_alignment", "undetermined signal index role");
      std::set<std::string> ids;
      if (role == "element") {
        if (!row.at("width_binding_complete").as_bool() ||
            !row.at("width_parameter_ids").is_array())
          decline("typed_alignment", "incomplete element width identity");
        for (const J &part : row.at("width_parameter_ids").as_array()) {
          std::string id = field(num(part));
          if (!parameter_ids.count(id) || !ids.insert(id).second)
            decline("typed_alignment", "invalid width parameter identity");
        }
        indexed |= ids.count(axis_id) != 0;
      }
      auto pair = std::pair{role, ids};
      auto [at, fresh] = declared.emplace(s(row, "declaration_id"), pair);
      if (!fresh && at->second != pair)
        decline("typed_alignment", "inconsistent declaration binding");
    }
  if (!indexed)
    decline("typed_alignment", "axis has no typed element declaration");
}

EnvWindow env_window(const TrustedTarget &trusted, const Config &cfg,
                     TlsfGr1EnvRankResult &out) {
  const Instance &target = *trusted.instance;
  auto axes = parameters(target);
  std::string last_reason = "no eligible axis";
  for (const auto &[axis, value] : axes) {
    if (value <= 5)
      continue;
    try {
      env_typed_axis(target, axis);
      EnvWindow window;
      window.axis = axis;
      std::optional<std::pair<std::set<std::string>, std::set<std::string>>>
          expected_classes;
      for (int size : {3, 4, 5}) {
        cfg.check(env_stage_seed_window);
        if (out.seed_probes >= cfg.max_seed_probes)
          throw Failure(TLSF_GR1_LIFT_LIMIT, env_stage_seed_window,
                        "seed probe budget exhausted");
        out.seed_probes++;
        auto overrides = axes;
        overrides[axis] = size;
        auto seed =
            lower(reinterpret_cast<const uint8_t *>(trusted.snapshot.data()),
                  trusted.snapshot.size(), overrides, TLSF_GR1_EXACT, cfg);
        out.seed_reductions++;
        env_typed_axis(*seed, axis);
        auto members = axis_members(target, *seed);
        auto seed_classes = env_typed_classes(*seed);
        if (!expected_classes)
          expected_classes = seed_classes;
        if (members.second.size() != size_t(size) ||
            members.first.size() <= members.second.size() ||
            seed_classes != *expected_classes)
          decline(env_stage_seed_window, "unstable exact seed structure");
        if (window.target_members.empty())
          window.target_members = std::move(members.first);
        else if (window.target_members != members.first)
          decline(env_stage_seed_window, "target coordinate inventory changed");
        seed->members = std::move(members.second);
        window.seeds.push_back(std::move(seed));
      }
      return window;
    } catch (const Failure &e) {
      if (e.status == TLSF_GR1_LIFT_LIMIT ||
          e.status == TLSF_GR1_LIFT_DEADLINE ||
          e.status == TLSF_GR1_LIFT_CANCELLED)
        throw;
      last_reason = axis + ": " + e.stage + ": " + e.what();
    }
  }
  throw Failure(TLSF_GR1_LIFT_DECLINED, env_stage_seed_window, last_reason);
}

void env_solve_seed(Instance &seed, const Config &cfg,
                    TlsfGr1EnvRankResult &out) {
  cfg.check("seed_solve");
  char why[256]{};
  if (!tlsf_gr1_validate_game(seed.r.game, why, sizeof why))
    decline("seed_solve", why);
  auto game_copy = parse_aig(seed.r.aag, seed.r.aag_size);
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
  options.oxidd.deadline_mono_ns = cfg.effective_deadline();
  options.oxidd.cancelled = cfg.o.cancelled;
  options.oxidd.cancel_ctx = cfg.o.cancel_ctx;
  options.oxidd.max_artifact_bytes = cfg.o.max_artifact_bytes;
  options.oxidd.failure = &failure;
  options.certificate = &export_options;
  int unreal = 0;
  Aig *strategy = solve_gr1_oxidd(game_copy.release(), &unreal, &options);
  bool real = strategy && !unreal;
  aig_free(strategy);
  out.seed_solves++;
  std::unique_ptr<char, decltype(&free)> cert_owner(cert, &free),
      meta_owner(meta, &free), policy_owner(policy, &free),
      policy_meta_owner(policy_meta, &free);
  if (failure.kind == OXIDD_FAILURE_DEADLINE)
    throw cfg.deadline_failure("seed_solve");
  cfg.check("seed_solve");
  if (failure.kind == OXIDD_FAILURE_CANCELLED)
    throw Failure(TLSF_GR1_LIFT_CANCELLED, "seed_solve", "cancelled");
  if (failure.kind == OXIDD_FAILURE_BDD ||
      failure.kind == OXIDD_FAILURE_ARTIFACT_LIMIT ||
      failure.kind == OXIDD_FAILURE_HOST)
    throw Failure(TLSF_GR1_LIFT_LIMIT, "seed_solve",
                  "solver capacity exhausted");
  if (real && !export_options.failed && cert && meta) {
    cfg.bytes(cert_size, "seed_solve");
    cfg.bytes(meta_size, "seed_solve");
    const O real_meta = j::parse(std::string_view(meta, meta_size)).as_object();
    if (s(real_meta, "status") != "realizable" ||
        s(real_meta, "side") != env_side_system ||
        s(real_meta, "reduction_semantics") != "exact")
      decline("seed_check", "REAL seed certificate metadata mismatch");
    TlsfGr1CheckInput input{};
    input.game_aag = {(const uint8_t *)seed.r.aag, seed.r.aag_size};
    input.certificate_aag = {(const uint8_t *)cert, cert_size};
    input.certificate_json = {(const uint8_t *)meta, meta_size};
    TlsfGr1CheckOptions check_options{};
    check_options.method = TLSF_GR1_CHECK_REGION;
    check_options.node_cap = cfg.o.checker_nodes;
    check_options.cache_cap = cfg.o.checker_cache;
    check_options.max_artifact_bytes = cfg.o.max_artifact_bytes;
    check_options.deadline_mono_ns = cfg.effective_deadline();
    check_options.cancelled = cfg.o.cancelled;
    check_options.cancel_ctx = cfg.o.cancel_ctx;
    TlsfGr1CheckResult checked{};
    TlsfGr1CheckStatus check_status =
        tlsf_gr1_check(&input, &check_options, &checked);
    out.seed_checks++;
    if (check_status == TLSF_GR1_CHECK_DEADLINE) {
      tlsf_gr1_check_result_clear(&checked);
      throw cfg.deadline_failure("seed_check");
    }
    bool verified = check_status == TLSF_GR1_CHECK_OK &&
                    checked.verdict == TLSF_GR1_CHECK_REGION_VERIFIED;
    tlsf_gr1_check_result_clear(&checked);
    cfg.check("seed_check");
    if (!verified)
      decline("seed_check", "REAL seed certificate did not check");
    decline("seed_check", "checked REAL seed is ineligible for U");
  }
  if (real || !unreal || export_options.failed || !cert || !meta || !policy ||
      !policy_meta)
    decline("seed_solve", "checked environment seed is unavailable");
  for (size_t count : {cert_size, meta_size, policy_size, policy_meta_size})
    cfg.bytes(count, "seed_solve");
  seed.cert_aag.assign(cert, cert_size);
  seed.cert_json.assign(meta, meta_size);
  seed.env_policy_aag.assign(policy, policy_size);
  seed.env_policy_json.assign(policy_meta, policy_meta_size);
  seed.cert_meta = j::parse(seed.cert_json).as_object();
  if (s(seed.cert_meta, "status") != "unrealizable" ||
      s(seed.cert_meta, "side") != "environment" ||
      s(seed.cert_meta, "reduction_semantics") != "exact")
    decline("seed_solve", "environment seed metadata mismatch");
  TlsfGr1CheckInput input{};
  input.game_aag = {(const uint8_t *)seed.r.aag, seed.r.aag_size};
  input.certificate_aag = {(const uint8_t *)cert, cert_size};
  input.certificate_json = {(const uint8_t *)meta, meta_size};
  input.policy_aag = {(const uint8_t *)policy, policy_size};
  input.policy_json = {(const uint8_t *)policy_meta, policy_meta_size};
  TlsfGr1CheckOptions check_options{};
  check_options.method = TLSF_GR1_CHECK_CERTIFICATE;
  check_options.node_cap = cfg.o.checker_nodes;
  check_options.cache_cap = cfg.o.checker_cache;
  check_options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  check_options.deadline_mono_ns = cfg.effective_deadline();
  check_options.cancelled = cfg.o.cancelled;
  check_options.cancel_ctx = cfg.o.cancel_ctx;
  TlsfGr1CheckResult checked{};
  TlsfGr1CheckStatus check_status =
      tlsf_gr1_check(&input, &check_options, &checked);
  out.seed_checks++;
  if (check_status == TLSF_GR1_CHECK_DEADLINE) {
    tlsf_gr1_check_result_clear(&checked);
    throw cfg.deadline_failure("seed_check");
  }
  bool verified = check_status == TLSF_GR1_CHECK_OK &&
                  checked.verdict == TLSF_GR1_CHECK_VERIFIED;
  tlsf_gr1_check_result_clear(&checked);
  cfg.check("seed_check");
  if (!verified)
    decline("seed_check", "independent environment seed check failed");
  seed.cert = parse_aig(seed.cert_aag.data(), seed.cert_aag.size());
}

std::set<uint32_t> env_support(const Aig *aig, uint32_t root) {
  std::map<uint32_t, std::pair<uint32_t, uint32_t>> gates;
  for (uint32_t p = 0; p < aig_num_ands(aig); p++) {
    uint32_t lhs, left, right;
    aig_and_at(aig, p, &lhs, &left, &right);
    gates.emplace(lhs / 2, std::pair{left, right});
  }
  std::set<uint32_t> leaves, seen;
  std::function<void(uint32_t)> visit = [&](uint32_t lit) {
    uint32_t var = lit / 2;
    if (!var || !seen.insert(var).second)
      return;
    auto found = gates.find(var);
    if (found == gates.end()) {
      leaves.insert(var);
      return;
    }
    visit(found->second.first);
    visit(found->second.second);
  };
  visit(root);
  return leaves;
}

struct EnvAnchor {
  std::string kind;
  std::vector<int> owners;
};
struct EnvVariable {
  std::string identity, prefix;
  std::vector<int> indices;
  std::set<int> owners;
  std::string order_field;
};
struct EnvOutput {
  std::string name, class_key, identity;
  EnvAnchor first, second;
  int outer = -1, depth = -1;
  uint32_t literal = 0;
};
struct EnvView {
  const Instance *instance;
  std::vector<int> members;
  std::map<std::string, EnvVariable> variables;
  std::map<std::string, std::string> game_names;
  std::map<int, EnvAnchor> goals, fairness;
  std::map<int, std::string> roles;
  std::vector<EnvOutput> outputs;
  std::set<std::string> classes;
  uint32_t outer = 0;
};

std::string env_anchor_identity(const EnvAnchor &anchor) {
  std::vector<std::string> owners;
  for (int owner : anchor.owners)
    owners.push_back(field(owner));
  return key({anchor.kind, join(owners)});
}

std::set<std::string> env_axis_declarations(const Instance &i,
                                            const std::string &axis) {
  std::string axis_id;
  for (const J &value : i.data.at("source_parameters").as_array()) {
    const O &row = value.as_object();
    if (s(row, "name") == axis)
      axis_id = field(n(row, "id"));
  }
  std::set<std::string> result;
  for (const char *kind : {"inputs", "outputs"})
    for (const J &value : i.data.at(kind).as_array()) {
      const O &row = value.as_object();
      if (s(row, "index_role") != "element")
        continue;
      for (const J &id : row.at("width_parameter_ids").as_array())
        if (field(num(id)) == axis_id)
          result.insert(s(row, "declaration_id"));
    }
  return result;
}

std::vector<int> env_owners(const O &origin,
                            const std::set<std::string> &axis_declarations,
                            const std::vector<int> &members) {
  auto bound = ints(origin.at("index_tuple").as_array());
  if (bound.empty())
    return {};
  for (int owner : bound)
    if (std::find(members.begin(), members.end(), owner) == members.end())
      decline("typed_alignment", "monitor owner is outside the axis");
  std::vector<int> referenced;
  for (const J &value : origin.at("signal_refs").as_array()) {
    const O &ref = value.as_object();
    if (!axis_declarations.count(s(ref, "declaration_id")))
      continue;
    for (int owner : ints(ref.at("index_tuple").as_array()))
      if (std::find(referenced.begin(), referenced.end(), owner) ==
          referenced.end())
        referenced.push_back(owner);
  }
  if (referenced.empty())
    return {};
  if (bound.size() == 1 && referenced.size() == 2 &&
      std::find(referenced.begin(), referenced.end(), bound[0]) !=
          referenced.end())
    return referenced;
  if (bound.size() > 1)
    for (int owner : bound)
      if (std::find(referenced.begin(), referenced.end(), owner) ==
          referenced.end())
        decline("typed_alignment", "pair owner lacks typed reference");
  return bound;
}

// Python json.dumps uses a space after each separator in an order key.
std::string env_json_order(const J &value) {
  std::string compact = dump(value), result;
  bool quoted = false, escaped = false;
  for (char c : compact) {
    result.push_back(c);
    if (escaped) {
      escaped = false;
    } else if (c == '\\' && quoted) {
      escaped = true;
    } else if (c == char(34)) {
      quoted = !quoted;
    } else if (!quoted && (c == ',' || c == ':')) {
      result.push_back(' ');
    }
  }
  return result;
}

std::string env_letter_order_field(const O &row) {
  return env_json_order(
      A{"letter", s(row, "direction"), s(row, "declaration_id")});
}

std::string env_state_order_field(const O &row, const O &origin,
                                  const std::vector<const O *> &siblings,
                                  size_t state) {
  A role{s(origin, "source_formula_id"), s(row, "role"), s(row, "side"),
         s(row, "mp_class")};
  if (siblings.size() > 1) {
    std::set<std::string> templates;
    for (const O *sibling : siblings)
      templates.insert(s(*sibling, "template"));
    if (templates.size() == siblings.size()) {
      role.emplace_back(s(row, "template"));
    } else {
      A refs;
      for (const J &value : origin.at("signal_refs").as_array()) {
        const O &ref = value.as_object();
        refs.emplace_back(A{s(ref, "declaration_id"), s(ref, "index_role"),
                            ref.at("index_tuple")});
      }
      role.emplace_back(A{s(row, "template"), refs});
    }
  }
  A fields{"state"};
  for (const J &part : role)
    fields.emplace_back(part);
  fields.emplace_back(int64_t(state));
  return env_json_order(fields);
}

EnvView env_game_view(const Instance &i, const std::string &axis,
                      const std::vector<int> &members) {
  EnvView view;
  view.instance = &i;
  view.members = members;
  auto indexed = env_axis_declarations(i, axis);
  std::map<uint32_t, const O *> signals;
  std::map<uint32_t, uint32_t> latch_next;
  std::map<uint32_t, std::string> latch_names;
  for (uint32_t p = 0; p < aig_num_latches(i.r.game); p++) {
    uint32_t lit, next;
    aig_latch_at(i.r.game, p, &lit, &next, nullptr);
    const char *name = aig_latch_name(i.r.game, p);
    latch_next.emplace(lit / 2, next);
    latch_names.emplace(lit / 2, name ? name : "");
  }
  for (const char *group : {"inputs", "outputs"})
    for (const J &value : i.data.at(group).as_array()) {
      const O &row = value.as_object();
      uint32_t lit = uint32_t(n(row, "game_literal"));
      if (!signals.emplace(lit / 2, &row).second)
        decline("typed_alignment", "duplicate game signal literal");
    }
  if (signals.size() != aig_num_inputs(i.r.game))
    decline("typed_alignment", "game signal inventory differs");
  std::set<uint32_t> game_inputs;
  for (uint32_t p = 0; p < aig_num_inputs(i.r.game); p++) {
    uint32_t lit;
    const char *name = aig_input_name(i.r.game, p, &lit);
    if (!signals.count(lit / 2) || !game_inputs.insert(lit / 2).second)
      decline("typed_alignment", "game signal lacks unique provenance");
    const O &row = *signals.at(lit / 2);
    auto indices = ints(row.at("index_tuple").as_array());
    std::set<int> owners;
    if (indexed.count(s(row, "declaration_id")))
      for (int owner : indices)
        if (std::find(members.begin(), members.end(), owner) != members.end())
          owners.insert(owner);
    std::string prefix =
        key({"letter", s(row, "direction"), s(row, "declaration_id")});
    std::vector<std::string> coords;
    for (int owner : indices)
      coords.push_back(field(owner));
    std::string identity = key({prefix, join(coords)});
    if (!view.variables
             .emplace(identity, EnvVariable{identity, prefix, indices, owners,
                                            env_letter_order_field(row)})
             .second)
      decline("typed_alignment", "duplicate letter identity");
    if (!name || !view.game_names.emplace(name, identity).second)
      decline("typed_alignment", "game signal name inventory differs");
  }
  if (game_inputs != [&] {
        std::set<uint32_t> keys;
        for (const auto &[literal, _] : signals)
          keys.insert(literal);
        return keys;
      }())
    decline("typed_alignment", "game signal inventory is incomplete");
  std::map<std::string, const O *> conjuncts;
  for (const J &value : i.data.at("source_conjuncts").as_array()) {
    const O &row = value.as_object();
    if (!conjuncts
             .emplace(key({s(row, "source_formula_id"),
                           field(n(row, "generated_position"))}),
                      &row)
             .second)
      decline("typed_alignment", "duplicate source conjunct identity");
  }
  std::map<std::string, std::vector<const O *>> siblings;
  std::map<const O *, std::vector<int>> owners_by_monitor;
  std::set<uint32_t> typed_latches;
  std::set<std::string> linkage;
  int fair_index = 0;
  for (const J &value : i.data.at("monitors").as_array()) {
    const O &row = value.as_object();
    if (s(row, "provenance_source") != "frontend" ||
        s(row, "template_source") != "frontend")
      decline("typed_alignment", "monitor lacks frontend origin");
    const O &origin = row.at("source_origin").as_object();
    auto owners = env_owners(origin, indexed, members);
    owners_by_monitor.emplace(&row, owners);
    std::vector<std::string> owner_fields;
    for (int owner : owners)
      owner_fields.push_back(field(owner));
    std::string base = key({s(origin, "source_formula_id"), s(row, "role"),
                            s(row, "side"), s(row, "mp_class")});
    siblings[key({base, join(owner_fields)})].push_back(&row);
    std::string origin_key = key({s(origin, "source_formula_id"),
                                  field(n(origin, "generated_position"))});
    auto found = conjuncts.find(origin_key);
    if (found == conjuncts.end())
      decline("typed_alignment", "monitor source conjunct is missing");
    std::set<std::string> claimed_refs, actual_refs;
    for (const J &part : origin.at("signal_refs").as_array()) {
      const O &ref = part.as_object();
      claimed_refs.insert(
          key({s(ref, "declaration_id"), dump(ref.at("index_tuple"))}));
    }
    std::set<uint32_t> own_latches;
    for (const J &part : row.at("latch_literals").as_array()) {
      uint32_t lit = uint32_t(num(part));
      if (!latch_next.count(lit / 2) || !typed_latches.insert(lit / 2).second)
        decline("typed_alignment", "monitor latch inventory differs");
      own_latches.insert(lit / 2);
      auto support = env_support(i.r.game, latch_next.at(lit / 2));
      for (uint32_t signal : support)
        if (signals.count(signal)) {
          const O &ref = *signals.at(signal);
          actual_refs.insert(
              key({s(ref, "declaration_id"), dump(ref.at("index_tuple"))}));
        }
    }
    if (claimed_refs != actual_refs)
      decline("schema_abi", "monitor transition references differ");
    const O &conjunct = *found->second;
    const O &binding = row.at("source_binding").as_object();
    if (s(row, "construction_formula") != s(conjunct, "normalized_formula") ||
        s(binding, "source_formula_id") != s(origin, "source_formula_id") ||
        n(binding, "generated_position") != n(origin, "generated_position") ||
        n(binding, "source_node_id") != n(origin, "source_node_id") ||
        n(conjunct, "source_node_id") != n(origin, "source_node_id") ||
        s(conjunct, "block") != s(origin, "block") ||
        dump(conjunct.at("signal_refs")) != dump(origin.at("signal_refs")) ||
        dump(conjunct.at("bindings")) != dump(origin.at("bindings")))
      decline("typed_alignment", "monitor/source construction differs");
    std::string link =
        key({s(row, "role"), join(owner_fields), origin_key, s(row, "template"),
             dump(origin.at("signal_refs"))});
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (env_rank_fault == 7 && !linkage.empty())
      link = *linkage.begin();
#endif
    if (!linkage.insert(link).second)
      decline("typed_alignment", "ambiguous sibling linkage");
    if (s(row, "role") == "justice") {
      int index = int(n(row, "justice_index"));
      if (index < 0 || index >= int(aig_num_justice(i.r.game)) ||
          !view.goals.emplace(index, EnvAnchor{base, owners}).second)
        decline("typed_alignment", "justice ordinal inventory differs");
      const uint32_t *lits;
      uint32_t count;
      aig_justice_at(i.r.game, index, &lits, &count);
      for (uint32_t p = 0; p < count; p++) {
        auto support = env_support(i.r.game, lits[p]);
        for (uint32_t var : support)
          if (!own_latches.count(var))
            decline("typed_alignment", "justice points outside its monitor");
      }
    } else if (s(row, "role") == "fairness") {
      if (fair_index >= int(aig_num_fairness(i.r.game)))
        decline("typed_alignment", "fairness ordinal exceeds game");
      for (uint32_t var :
           env_support(i.r.game, aig_fairness_at(i.r.game, fair_index)))
        if (!own_latches.count(var))
          decline("typed_alignment", "fairness points outside its monitor");
      view.fairness.emplace(fair_index++, EnvAnchor{base, owners});
    }
  }
  if (typed_latches.size() != latch_next.size() ||
      view.goals.size() != aig_num_justice(i.r.game) ||
      fair_index != int(aig_num_fairness(i.r.game)))
    decline("typed_alignment", "monitor game inventory is incomplete");
  if (view.fairness.empty())
    view.fairness.emplace(0, EnvAnchor{"synthetic", {}});
  for (const auto &[group, rows] : siblings) {
    std::set<std::string> variants;
    for (const O *row : rows) {
      std::string variant =
          key({s(*row, "template"),
               dump(row->at("source_origin").as_object().at("signal_refs"))});
      if (!variants.insert(variant).second)
        decline("typed_alignment", "ambiguous sibling monitor roles");
      const O &origin = row->at("source_origin").as_object();
      std::string role =
          key({s(origin, "source_formula_id"), s(*row, "role"), s(*row, "side"),
               s(*row, "mp_class"), rows.size() > 1 ? variant : ""});
      auto indices = owners_by_monitor.at(row);
      std::set<int> owner_set(indices.begin(), indices.end());
      const A &lits = row->at("latch_literals").as_array();
      for (size_t state = 0; state < lits.size(); state++) {
        uint32_t lit = uint32_t(num(lits[state]));
        std::string prefix = key({"state", role, field(state)});
        std::vector<std::string> fields;
        for (int owner : indices)
          fields.push_back(field(owner));
        std::string identity = key({prefix, join(fields)});
        if (!view.variables
                 .emplace(identity,
                          EnvVariable{
                              identity, prefix, indices, owner_set,
                              env_state_order_field(*row, origin, rows, state)})
                 .second)
          decline("typed_alignment", "duplicate state identity");
        if (!view.game_names.emplace(latch_names.at(lit / 2), identity).second)
          decline("typed_alignment", "game latch name inventory differs");
      }
      if (s(*row, "role") == "justice")
        view.goals.at(int(n(*row, "justice_index"))).kind = role;
      else if (s(*row, "role") == "fairness") {
        for (auto &[_, anchor] : view.fairness)
          if (anchor.kind == key({s(origin, "source_formula_id"), "fairness",
                                  s(*row, "side"), s(*row, "mp_class")}) &&
              anchor.owners == indices) {
            anchor.kind = role;
            break;
          }
      }
    }
  }
  for (int member : members) {
    std::set<std::string> distinct;
    for (const auto &[_, variable] : view.variables)
      if (variable.owners.count(member))
        distinct.insert(variable.prefix);
    view.roles.emplace(member, join(std::vector<std::string>(distinct.begin(),
                                                             distinct.end())));
  }
  return view;
}

std::string env_output_class(const std::string &kind, int outer, int depth,
                             const EnvAnchor &first, const EnvAnchor &second) {
  return key({kind, field(outer), field(depth), first.kind, second.kind});
}

std::vector<EnvOutput> env_certificate_inventory(EnvView &view) {
  const Instance &i = *view.instance;
  const Aig *cert = i.cert.get();
  const O &counts = i.cert_meta.at("counts").as_object();
  if (n(counts, "predicates") != aig_num_outputs(cert) ||
      n(counts, "aig_inputs") != aig_num_inputs(cert) ||
      n(counts, "aig_latches") != 0 || n(counts, "sampling_latches") != 0)
    decline("typed_alignment", "certificate count inventory differs");
  view.outer = uint32_t(n(counts, "outer_levels"));
  if (!view.outer || view.outer > 256)
    decline("typed_alignment", "rank depth is unbounded");
  std::set<std::string> inputs;
  for (uint32_t p = 0; p < aig_num_inputs(cert); p++) {
    const char *name = aig_input_name(cert, p, nullptr);
    if (!name || !view.game_names.count(name) || !inputs.insert(name).second)
      decline("typed_alignment", "certificate input identity differs");
  }
  if (inputs.size() != view.game_names.size())
    decline("typed_alignment", "certificate input inventory is incomplete");
  std::set<std::string> names, identities;
  std::map<std::tuple<int, int, int>, std::set<int>> depths;
  std::vector<EnvOutput> outputs;
  const std::regex z_re("z_([0-9]+)");
  const std::regex y_re("y_([0-9]+)_([0-9]+)");
  const std::regex x_re("x_([0-9]+)_([0-9]+)_([0-9]+)_([0-9]+)");
  const std::regex goal_re("goal_([0-9]+)");
  const std::regex fair_re("fair_([0-9]+)");
  const std::regex move_re("move_([0-9]+)");
  auto decimal = [](const std::ssub_match &part) -> int {
    try {
      return std::stoi(part.str());
    } catch (const std::exception &) {
      decline("typed_alignment", "rank number is out of range");
    }
  };
  for (uint32_t p = 0; p < aig_num_outputs(cert); p++) {
    uint32_t literal;
    const char *raw = aig_output_at(cert, p, &literal);
    if (!raw || !names.insert(raw).second)
      decline("typed_alignment", "duplicate certificate output name");
    std::string name(raw), kind;
    EnvAnchor first, second;
    int outer = -1, depth = -1;
    std::smatch match;
    if (name == "inv" || name == tlsf_gr1_check_winning_output_name)
      kind = name;
    else if (std::regex_match(name, match, z_re)) {
      kind = "z";
      outer = decimal(match[1]);
    } else if (std::regex_match(name, match, y_re)) {
      kind = "y";
      outer = decimal(match[1]);
      int goal = decimal(match[2]);
      if (!view.goals.count(goal))
        decline("typed_alignment", "goal ordinal is absent");
      first = view.goals.at(goal);
    } else if (std::regex_match(name, match, x_re)) {
      kind = "x";
      outer = decimal(match[1]);
      int goal = decimal(match[2]);
      int fair = decimal(match[3]);
      depth = decimal(match[4]);
      if (!view.goals.count(goal) || !view.fairness.count(fair) || depth >= 256)
        decline("typed_alignment", "rank index is out of bounds");
      first = view.goals.at(goal);
      second = view.fairness.at(fair);
      depths[{outer, goal, fair}].insert(depth);
    } else if (std::regex_match(name, match, goal_re)) {
      kind = "goal";
      int goal = decimal(match[1]);
      if (!view.goals.count(goal))
        decline("typed_alignment", "goal ordinal is absent");
      first = view.goals.at(goal);
    } else if (std::regex_match(name, match, fair_re) ||
               std::regex_match(name, match, move_re)) {
      kind = name.substr(0, name.find('_'));
      int fair = decimal(match[1]);
      if (!view.fairness.count(fair))
        decline("typed_alignment", "fairness ordinal is absent");
      first = view.fairness.at(fair);
    } else
      decline("typed_alignment", "unexpected certificate output");
    if (outer >= int(view.outer))
      decline("typed_alignment", "outer rank is out of bounds");
    std::string class_key = env_output_class(kind, outer, depth, first, second);
    std::string identity = key(
        {class_key, env_anchor_identity(first), env_anchor_identity(second)});
    if (!identities.insert(identity).second)
      decline("typed_alignment", "duplicate predicate identity");
    view.classes.insert(class_key);
    outputs.push_back(
        {name, class_key, identity, first, second, outer, depth, literal});
  }
  std::set<std::string> expected{"inv", tlsf_gr1_check_winning_output_name};
  for (const auto &[goal, _] : view.goals)
    expected.insert("goal_" + field(goal));
  for (uint32_t fair = 0; fair < aig_num_fairness(i.r.game); fair++)
    expected.insert("fair_" + field(fair));
  for (const auto &[fair, _] : view.fairness)
    expected.insert("move_" + field(fair));
  for (uint32_t outer = 0; outer < view.outer; outer++) {
    expected.insert("z_" + field(outer));
    for (const auto &[goal, _] : view.goals) {
      expected.insert("y_" + field(outer) + "_" + field(goal));
      for (const auto &[fair, _] : view.fairness) {
        auto at = depths.find({int(outer), goal, fair});
        if (at == depths.end() || at->second.empty() || at->second.size() > 256)
          decline("typed_alignment", "rank level inventory is incomplete");
        for (size_t depth = 0; depth < at->second.size(); depth++) {
          if (!at->second.count(int(depth)))
            decline("typed_alignment", "rank levels are not consecutive");
          expected.insert("x_" + field(outer) + "_" + field(goal) + "_" +
                          field(fair) + "_" + field(depth));
        }
      }
    }
  }
  if (names != expected)
    decline("typed_alignment", "certificate output inventory differs");
  return outputs;
}

void env_policy_inventory(EnvView &view) {
  const Instance &i = *view.instance;
  auto policy = parse_aig(i.env_policy_aag.data(), i.env_policy_aag.size());
  O meta = j::parse(i.env_policy_json).as_object();
  if (s(meta, "side") != "environment" ||
      s(meta, "reduction_semantics") != "exact" ||
      n(meta.at("counts").as_object(), "aig_outputs") !=
          aig_num_outputs(policy.get()))
    decline("typed_alignment", "policy sidecar inventory differs");
  std::set<std::string> expected_inputs, actual_inputs;
  for (uint32_t p = 0; p < aig_num_latches(i.r.game); p++) {
    const char *name = aig_latch_name(i.r.game, p);
    if (!name)
      decline("typed_alignment", "game latch lacks a name");
    expected_inputs.insert(name);
  }
  for (const auto &[fair, _] : view.fairness)
    expected_inputs.insert("curr_" + field(fair));
  for (uint32_t p = 0; p < aig_num_inputs(policy.get()); p++) {
    const char *name = aig_input_name(policy.get(), p, nullptr);
    if (!name || !actual_inputs.insert(name).second)
      decline("typed_alignment", "duplicate policy input");
  }
  if (actual_inputs != expected_inputs)
    decline("typed_alignment", "policy input inventory differs");
  std::set<std::string> expected_outputs, actual_outputs;
  for (uint32_t p = 0; p < aig_num_inputs(i.r.game); p++) {
    const char *name = aig_input_name(i.r.game, p, nullptr);
    if (name && strncmp(name, "controllable_", 13))
      expected_outputs.insert(name);
  }
  for (const auto &[fair, _] : view.fairness)
    expected_outputs.insert("curr_next_" + field(fair));
  for (uint32_t p = 0; p < aig_num_outputs(policy.get()); p++) {
    const char *name = aig_output_at(policy.get(), p, nullptr);
    if (!name || !actual_outputs.insert(name).second)
      decline("typed_alignment", "duplicate policy output");
  }
  if (actual_outputs != expected_outputs)
    decline("typed_alignment", "policy output inventory differs");
  std::map<int, std::string> sidecar;
  const O &listed = meta.at("outputs").as_object();
  for (const char *group : {"uncontrollable", "counter_next"})
    for (const J &value : listed.at(group).as_array()) {
      const O &row = value.as_object();
      if (!sidecar.emplace(int(n(row, "policy_output")), s(row, "name")).second)
        decline("typed_alignment", "duplicate policy sidecar output");
    }
  if (sidecar.size() != actual_outputs.size())
    decline("typed_alignment", "policy sidecar output count differs");
  for (uint32_t p = 0; p < aig_num_outputs(policy.get()); p++)
    if (sidecar.at(int(p)) != aig_output_at(policy.get(), p, nullptr))
      decline("typed_alignment", "policy sidecar output differs");
}

std::vector<EnvView> env_preflight(const EnvWindow &window,
                                   const TrustedTarget &trusted) {
  std::vector<EnvView> views;
  for (const auto &seed : window.seeds) {
    EnvView view = env_game_view(*seed, window.axis, seed->members);
    view.outputs = env_certificate_inventory(view);
    env_policy_inventory(view);
    if (!views.empty() && view.classes != views.front().classes)
      decline("typed_alignment", "rank class inventory differs across seeds");
    views.push_back(std::move(view));
  }
  EnvView target =
      env_game_view(*trusted.instance, window.axis, window.target_members);
  if (env_typed_classes(*trusted.instance) !=
      env_typed_classes(*window.seeds.front()))
    decline("typed_alignment", "target conjunct or role class missing");
  if (target.roles.empty())
    decline("typed_alignment", "target has no typed owner roles");
  views.push_back(std::move(target));
  return views;
}

struct EnvNode {
  int label, low, high;
  bool operator==(const EnvNode &other) const = default;
};
struct EnvNodeHash {
  size_t operator()(const EnvNode &row) const {
    size_t h = std::hash<int>{}(row.label);
    h = h * 1315423911u ^ std::hash<int>{}(row.low);
    return h * 1315423911u ^ std::hash<int>{}(row.high);
  }
};
struct EnvApplyKey {
  int op, left, right;
  bool operator==(const EnvApplyKey &other) const = default;
};
struct EnvApplyHash {
  size_t operator()(const EnvApplyKey &row) const {
    size_t h = std::hash<int>{}(row.op);
    h = h * 1315423911u ^ std::hash<int>{}(row.left);
    return h * 1315423911u ^ std::hash<int>{}(row.right);
  }
};

struct EnvOrder {
  int owner_class = 0;
  std::vector<std::string> owners;
  std::string field, label;
  bool operator<(const EnvOrder &other) const {
    return std::tie(owner_class, owners, field, label) <
           std::tie(other.owner_class, other.owners, other.field, other.label);
  }
};

class EnvBdd {
  // The policy reaches the prototype's cumulative apply cap only if its
  // memo table can retain all intermediate applications. These are resource
  // guards, not substitutes for the fixed 3M-node and 12M-apply budgets.
  static constexpr uint64_t rank_memory_cap = 2ull << 30;
  static constexpr size_t rank_cache_cap = 12000000;
  const Config &cfg;
  std::vector<EnvNode> nodes{{-1, 0, 0}, {-1, 1, 1}};
  std::unordered_map<EnvNode, int, EnvNodeHash> unique;
  std::unordered_map<EnvApplyKey, int, EnvApplyHash> cache;
  std::map<std::string, int> labels;
  std::vector<std::string> names;
  std::vector<EnvOrder> orders;
  uint64_t applies = 0;
  std::string context;

public:
  explicit EnvBdd(const Config &config) : cfg(config) {}
  size_t node_count() const { return nodes.size(); }
  uint64_t apply_count() const { return applies; }
  size_t cache_count() const { return cache.size(); }
  uint64_t accounted_bytes() const {
    // Charge the node and unique tables together, plus each cache entry.
    return nodes.size() * (sizeof(EnvNode) + 64) +
           cache.size() * (sizeof(EnvApplyKey) + sizeof(int) + 64);
  }
  void set_context(std::string value) { context = std::move(value); }
  int label(const std::string &name, EnvOrder order) {
    if (auto at = labels.find(name); at != labels.end())
      return at->second;
    int id = int(names.size());
    labels.emplace(name, id);
    names.push_back(name);
    if (order.label.empty())
      order.label = name;
    orders.push_back(std::move(order));
    return id;
  }
  int label_id(const std::string &name) const {
    auto at = labels.find(name);
    if (at == labels.end())
      decline("schema_abi", "typed BDD variable is absent");
    return at->second;
  }
  const std::string &name(int label_id) const { return names.at(label_id); }
  int node(int variable, int low, int high) {
    if (low == high)
      return low;
    EnvNode key{variable, low, high};
    if (auto at = unique.find(key); at != unique.end())
      return at->second;
    if (nodes.size() >= 3000000)
      throw Failure(TLSF_GR1_LIFT_LIMIT, "schema_capacity",
                    "cumulative rank node cap exhausted at " + context);
    if (accounted_bytes() + sizeof(EnvNode) + 64 > rank_memory_cap)
      throw Failure(TLSF_GR1_LIFT_LIMIT, "schema_capacity",
                    "accounted rank memory cap exhausted at " + context);
    int id = int(nodes.size());
    nodes.push_back(key);
    unique.emplace(key, id);
    return id;
  }
  int var(int variable) { return node(variable, 0, 1); }
  int apply(int op, int left, int right) {
    applies++;
    if (applies > 12000000)
      throw Failure(TLSF_GR1_LIFT_LIMIT, "schema_capacity",
                    "cumulative rank apply cap exhausted at " + context);
    if ((applies & 1023u) == 0)
      cfg.check("schema_capacity");
    if (op == 0) {
      if (left == 0 || right == 0)
        return 0;
      if (left == 1)
        return right;
      if (right == 1 || left == right)
        return left;
    } else {
      if (left == 1 || right == 1)
        return 1;
      if (left == 0)
        return right;
      if (right == 0 || left == right)
        return left;
    }
    if (left > right)
      std::swap(left, right);
    EnvApplyKey key{op, left, right};
    if (auto at = cache.find(key); at != cache.end())
      return at->second;
    int vl = nodes[left].label, vr = nodes[right].label;
    int v = orders[vl] < orders[vr] ? vl : vr;
    int ll = vl == v ? nodes[left].low : left;
    int lh = vl == v ? nodes[left].high : left;
    int rl = vr == v ? nodes[right].low : right;
    int rh = vr == v ? nodes[right].high : right;
    int low = apply(op, ll, rl);
    int high = apply(op, lh, rh);
    int result = node(v, low, high);
    if (cache.size() >= rank_cache_cap ||
        accounted_bytes() + sizeof(EnvApplyKey) + sizeof(int) + 64 >
            rank_memory_cap)
      throw Failure(TLSF_GR1_LIFT_LIMIT, "schema_capacity",
                    "accounted rank apply cache cap exhausted at " + context);
    cache.emplace(key, result);
    return result;
  }
  int neg(int root) {
    std::unordered_map<int, int> memo{{0, 1}, {1, 0}};
    std::function<int(int)> visit = [&](int current) -> int {
      if (auto at = memo.find(current); at != memo.end())
        return at->second;
      auto row = nodes[current];
      int result = node(row.label, visit(row.low), visit(row.high));
      memo.emplace(current, result);
      return result;
    };
    return visit(root);
  }
  int ite(int condition, int high, int low) {
    return apply(1, apply(0, condition, high), apply(0, neg(condition), low));
  }
  std::set<int> support(int root) const {
    std::set<int> result;
    std::unordered_set<int> seen;
    std::vector<int> stack{root};
    while (!stack.empty()) {
      int current = stack.back();
      stack.pop_back();
      if (current < 2 || !seen.insert(current).second)
        continue;
      auto row = nodes[current];
      result.insert(row.label);
      stack.push_back(row.low);
      stack.push_back(row.high);
    }
    return result;
  }
  int quant(int root, const std::set<int> &dropped, bool existential) {
    std::unordered_map<int, int> memo{{0, 0}, {1, 1}};
    std::function<int(int)> visit = [&](int current) -> int {
      if (auto at = memo.find(current); at != memo.end())
        return at->second;
      auto row = nodes[current];
      int lo = visit(row.low), hi = visit(row.high);
      int result = dropped.count(row.label) ? apply(existential ? 1 : 0, lo, hi)
                                            : node(row.label, lo, hi);
      memo.emplace(current, result);
      return result;
    };
    return visit(root);
  }
  int restrict_to(int root, const std::map<int, bool> &assignments) {
    std::unordered_map<int, int> memo{{0, 0}, {1, 1}};
    std::function<int(int)> visit = [&](int current) -> int {
      if (auto at = memo.find(current); at != memo.end())
        return at->second;
      auto row = nodes[current];
      int result;
      if (auto at = assignments.find(row.label); at != assignments.end())
        result = visit(at->second ? row.high : row.low);
      else
        result = node(row.label, visit(row.low), visit(row.high));
      memo.emplace(current, result);
      return result;
    };
    return visit(root);
  }
  int compose(int root, const std::map<int, int> &mapping) {
    std::unordered_map<int, int> memo{{0, 0}, {1, 1}};
    std::function<int(int)> visit = [&](int current) -> int {
      if (auto at = memo.find(current); at != memo.end())
        return at->second;
      auto row = nodes[current];
      auto at = mapping.find(row.label);
      int replacement = at == mapping.end() ? var(row.label) : at->second;
      int high = visit(row.high);
      int low = visit(row.low);
      int result = ite(replacement, high, low);
      memo.emplace(current, result);
      return result;
    };
    return visit(root);
  }
  int rename(int root, const std::map<int, int> &mapping) {
    auto used = support(root);
    for (int key : used)
      if (!mapping.count(key))
        decline("schema_abi", "unmapped BDD variable");
    std::map<int, int> replacements;
    for (const auto &[from, to] : mapping)
      replacements.emplace(from, var(to));
    return compose(root, replacements);
  }
  int from_aig(const Aig *aig, uint32_t root,
               const std::map<uint32_t, int> &input_labels) {
    std::map<uint32_t, std::pair<uint32_t, uint32_t>> gates;
    for (uint32_t p = 0; p < aig_num_ands(aig); p++) {
      uint32_t lhs, left, right;
      aig_and_at(aig, p, &lhs, &left, &right);
      gates.emplace(lhs / 2, std::pair{left, right});
    }
    std::map<uint32_t, int> memo{{0, 0}};
    std::function<int(uint32_t)> visit = [&](uint32_t lit) -> int {
      uint32_t variable = lit / 2;
      auto at = memo.find(variable);
      int result;
      if (at != memo.end())
        result = at->second;
      else if (auto leaf = input_labels.find(variable);
               leaf != input_labels.end())
        result = var(leaf->second);
      else if (auto gate = gates.find(variable); gate != gates.end()) {
        int left = visit(gate->second.first);
        int right = visit(gate->second.second);
        result = apply(0, left, right);
      } else
        decline("schema_abi", "AIG leaf lacks typed provenance");
      memo.emplace(variable, result);
      return lit & 1 ? neg(result) : result;
    };
    return visit(root);
  }
  uint32_t to_aig(Aig *aig, int root,
                  const std::map<int, uint32_t> &literals) const {
    std::unordered_map<int, uint32_t> memo{{0, AIG_FALSE}, {1, AIG_TRUE}};
    std::function<uint32_t(int)> visit = [&](int current) -> uint32_t {
      if (auto at = memo.find(current); at != memo.end())
        return at->second;
      auto row = nodes[current];
      auto at = literals.find(row.label);
      if (at == literals.end())
        decline("instantiate", "rank uses an unmapped target variable");
      uint32_t variable = at->second;
      uint32_t result = aig_or(aig, aig_and(aig, variable, visit(row.high)),
                               aig_and(aig, aig_not(variable), visit(row.low)));
      memo.emplace(current, result);
      return result;
    };
    return visit(root);
  }
};

EnvOrder env_bdd_order(const EnvVariable &var, const std::map<int, int> &slots,
                       const std::map<int, int> &anchors, bool normalized) {
  EnvOrder result;
  result.owner_class = var.indices.empty() ? 0 : 1;
  result.field = var.order_field;
  A coordinates;
  for (int index : var.indices) {
    if (!normalized) {
      result.owners.push_back(field(index));
      coordinates.emplace_back(index);
    } else if (var.owners.count(index) && anchors.count(index)) {
      result.owners.push_back(env_json_order(A{"anchor", anchors.at(index)}));
      coordinates.emplace_back(A{"anchor", anchors.at(index)});
    } else if (var.owners.count(index) && slots.count(index)) {
      result.owners.push_back(env_json_order(A{"slot", slots.at(index)}));
      coordinates.emplace_back(A{"slot", slots.at(index)});
    } else {
      result.owners.push_back(env_json_order(A{"fixed", index}));
      coordinates.emplace_back(A{"fixed", index});
    }
  }
  A fields = j::parse(var.order_field).as_array();
  A label;
  bool state = !fields.empty() && fields.front().as_string() == "state";
  for (size_t position = 0; position < fields.size(); position++) {
    if (state && !normalized && position + 1 == fields.size())
      label.emplace_back(coordinates);
    label.emplace_back(fields[position]);
  }
  if (!state || normalized)
    label.emplace_back(coordinates);
  result.label = env_json_order(label);
  return result;
}

int env_variable_label(EnvBdd &bdd, const EnvVariable &var) {
  return bdd.label(var.identity, env_bdd_order(var, {}, {}, false));
}

int env_variable_label(EnvBdd &bdd, const EnvVariable &var,
                       const std::map<int, int> &slots,
                       const std::map<int, int> &anchors = {}) {
  std::vector<std::string> indices;
  for (int index : var.indices) {
    if (var.owners.count(index) && anchors.count(index))
      indices.push_back(key({"anchor", field(anchors.at(index))}));
    else if (var.owners.count(index) && slots.count(index))
      indices.push_back(key({"slot", field(slots.at(index))}));
    else
      indices.push_back(key({"fixed", field(index)}));
  }
  return bdd.label(key({var.prefix, join(indices)}),
                   env_bdd_order(var, slots, anchors, true));
}

using EnvTemplate = std::map<std::string, int>;
struct EnvObservation {
  const EnvView *view;
  int root;
  EnvAnchor first, second;
  std::string name;
};
struct EnvSummaryGroup {
  int template_root = 0;
  std::vector<int> features;
};
struct EnvLearned {
  enum Kind { Projection, Summary, Previous } kind = Projection;
  int arity = 0, mode = 0;
  bool anchor_free = false;
  EnvTemplate parts;
  std::map<std::string, EnvSummaryGroup> summaries;
  std::string predecessor;
};

std::vector<int> env_anchor_members(const EnvAnchor &first,
                                    const EnvAnchor &second) {
  std::vector<int> order;
  for (const auto *anchor : {&first, &second})
    for (int owner : anchor->owners)
      if (std::find(order.begin(), order.end(), owner) == order.end())
        order.push_back(owner);
  return order;
}

std::vector<int> env_selected(const EnvView &view,
                              const std::vector<int> &subset,
                              const EnvAnchor &first, const EnvAnchor &second) {
  auto priority = env_anchor_members(first, second);
  std::vector<int> selected = subset;
  std::sort(selected.begin(), selected.end(), [&](int a, int b) {
    auto left = std::find(priority.begin(), priority.end(), a);
    auto right = std::find(priority.begin(), priority.end(), b);
    int ia = left == priority.end() ? int(priority.size())
                                    : int(left - priority.begin());
    int ib = right == priority.end() ? int(priority.size())
                                     : int(right - priority.begin());
    return std::tie(ia, view.roles.at(a), a) <
           std::tie(ib, view.roles.at(b), b);
  });
  return selected;
}

std::string env_group(const EnvView &view, const std::vector<int> &selected,
                      const EnvAnchor &first, const EnvAnchor &second) {
  std::map<int, int> slots;
  std::vector<std::string> role_items;
  for (size_t p = 0; p < selected.size(); p++) {
    slots.emplace(selected[p], int(p));
    role_items.push_back(view.roles.at(selected[p]));
  }
  std::vector<std::string> anchors;
  for (const auto *anchor : {&first, &second}) {
    std::vector<std::string> positions;
    for (int owner : anchor->owners)
      positions.push_back(field(slots.at(owner)));
    anchors.push_back(join(positions));
  }
  return key({join(role_items), join(anchors)});
}

EnvTemplate env_project(EnvBdd &bdd, const EnvObservation &observation,
                        int arity, int mode, bool erase_anchors) {
  const EnvView &view = *observation.view;
  if (arity > int(view.members.size()))
    decline("schema", "arity exceeds seed width");
  EnvAnchor first = erase_anchors ? EnvAnchor{} : observation.first;
  EnvAnchor second = erase_anchors ? EnvAnchor{} : observation.second;
  auto required = env_anchor_members(first, second);
  std::set<int> support = bdd.support(observation.root);
  EnvTemplate result;
  int rebuilt = mode == 0 ? 1 : 0;
  subsets(view.members, arity, [&](const std::vector<int> &subset) {
    if (!std::all_of(required.begin(), required.end(), [&](int owner) {
          return std::find(subset.begin(), subset.end(), owner) != subset.end();
        }))
      return;
    auto ordered = env_selected(view, subset, first, second);
    std::map<int, int> slots;
    for (size_t p = 0; p < ordered.size(); p++)
      slots.emplace(ordered[p], int(p));
    std::set<int> subset_set(subset.begin(), subset.end());
    std::set<int> keep;
    std::map<int, int> forward;
    for (const auto &[_, variable] : view.variables)
      if (std::includes(subset_set.begin(), subset_set.end(),
                        variable.owners.begin(), variable.owners.end())) {
        int old_label = env_variable_label(bdd, variable);
        keep.insert(old_label);
        forward.emplace(old_label, env_variable_label(bdd, variable, slots));
      }
    std::set<int> dropped;
    for (int label : support)
      if (!keep.count(label))
        dropped.insert(label);
    int projected = bdd.quant(observation.root, dropped, mode == 0);
    std::map<int, int> mapping;
    for (int label : bdd.support(projected))
      mapping.emplace(label, forward.at(label));
    int normalized = bdd.rename(projected, mapping);
    std::string group = env_group(view, ordered, first, second);
    if (auto at = result.find(group);
        at != result.end() && at->second != normalized)
      decline("schema", "within-role projection disagreement");
    result[group] = normalized;
    std::map<int, int> backward;
    for (const auto &[from, to] : forward)
      if (!backward.emplace(to, from).second)
        decline("schema_abi", "normalized variable is ambiguous");
    std::map<int, int> back_support;
    for (int label : bdd.support(normalized))
      back_support.emplace(label, backward.at(label));
    rebuilt = bdd.apply(mode, rebuilt, bdd.rename(normalized, back_support));
  });
  if (result.empty() || rebuilt != observation.root)
    decline("schema", "predicate is not exactly reconstructed");
  return result;
}

int env_instantiate_projection(EnvBdd &bdd, const EnvView &view,
                               const EnvAnchor &first, const EnvAnchor &second,
                               const EnvLearned &learned) {
  auto required = env_anchor_members(first, second);
  int result = learned.mode == 0 ? 1 : 0;
  subsets(view.members, learned.arity, [&](const std::vector<int> &subset) {
    std::set<int> subset_set(subset.begin(), subset.end());
    if (!std::all_of(required.begin(), required.end(),
                     [&](int owner) { return subset_set.count(owner) != 0; }))
      return;
    auto ordered = env_selected(view, subset, first, second);
    std::map<int, int> slots;
    for (size_t p = 0; p < ordered.size(); p++)
      slots.emplace(ordered[p], int(p));
    std::string group = env_group(view, ordered, first, second);
    auto at = learned.parts.find(group);
    if (at == learned.parts.end())
      decline("instantiate", "target role template is absent");
    std::map<int, int> back;
    for (const auto &[_, variable] : view.variables)
      if (std::includes(subset_set.begin(), subset_set.end(),
                        variable.owners.begin(), variable.owners.end())) {
        int normalized = env_variable_label(bdd, variable, slots);
        int concrete = env_variable_label(bdd, variable);
        if (!back.emplace(normalized, concrete).second)
          decline("instantiate", "target typed variable is ambiguous");
      }
    std::map<int, int> mapping;
    for (int label : bdd.support(at->second)) {
      if (!back.count(label))
        decline("instantiate", "target typed variable is absent");
      mapping.emplace(label, back.at(label));
    }
    result = bdd.apply(learned.mode, result, bdd.rename(at->second, mapping));
  });
  return result;
}

EnvLearned env_learn_projection(EnvBdd &bdd,
                                const std::vector<EnvObservation> &rows) {
  std::map<const EnvView *, std::vector<const EnvObservation *>> by_view;
  for (const auto &row : rows)
    by_view[row.view].push_back(&row);
  bool anchor_free = true;
  for (const auto &[_, observations] : by_view) {
    std::set<int> functions;
    std::set<std::string> relations;
    for (const auto *row : observations) {
      functions.insert(row->root);
      relations.insert(key(
          {env_anchor_identity(row->first), env_anchor_identity(row->second)}));
    }
    anchor_free &= observations.size() >= 2 && functions.size() == 1 &&
                   relations.size() >= 2;
  }
  for (bool erase : {false, true}) {
    if (erase && !anchor_free)
      break;
    for (int arity = 0; arity <= 3; arity++)
      for (int mode : {0, 1}) {
        std::optional<EnvTemplate> common;
        try {
          for (const auto &row : rows) {
            auto templ = env_project(bdd, row, arity, mode, erase);
            if (common && *common != templ)
              decline("schema", "seed rank templates disagree");
            common = std::move(templ);
          }
          if (!common)
            decline("schema", "rank class has no seed observation");
          EnvLearned learned;
          learned.kind = EnvLearned::Projection;
          learned.arity = arity;
          learned.mode = mode;
          learned.anchor_free = erase;
          learned.parts = std::move(*common);
          return learned;
        } catch (const Failure &e) {
          if (e.stage != "schema" && e.stage != "schema_abi")
            throw;
        }
      }
  }
  decline("schema", "no exact bounded projection");
}

EnvLearned env_learn_previous(EnvBdd &bdd,
                              const std::vector<EnvObservation> &rows,
                              const std::vector<EnvObservation> &previous,
                              const std::string &previous_name) {
  std::map<const EnvView *, int> predecessor;
  for (const auto &row : previous)
    if (!predecessor.emplace(row.view, row.root).second)
      decline("schema", "previous rank has ambiguous seed identity");
  EnvLearned learned;
  learned.kind = EnvLearned::Previous;
  learned.predecessor = previous_name;
  for (const auto &row : rows) {
    auto at = predecessor.find(row.view);
    if (at == predecessor.end())
      decline("typed_alignment", "previous rank is absent in seed");
    auto selected = env_anchor_members(row.first, row.second);
    if (selected.empty() || selected.size() > 2)
      decline("schema", "selected owner term exceeds bounded arity");
    selected = env_selected(*row.view, selected, row.first, row.second);
    std::set<int> selected_set(selected.begin(), selected.end());
    std::map<int, int> slots;
    for (size_t p = 0; p < selected.size(); p++)
      slots.emplace(selected[p], int(p));
    std::set<int> keep, drop;
    for (const auto &[_, variable] : row.view->variables)
      if (std::includes(selected_set.begin(), selected_set.end(),
                        variable.owners.begin(), variable.owners.end()))
        keep.insert(env_variable_label(bdd, variable));
    for (int label : bdd.support(row.root))
      if (!keep.count(label))
        drop.insert(label);
    int local = bdd.quant(row.root, drop, false);
    if (bdd.apply(1, at->second, local) != row.root)
      decline("schema", "previous rank and owner term do not reconstruct");
    std::map<int, int> forward;
    for (int label : bdd.support(local)) {
      const auto &var = row.view->variables.at(bdd.name(label));
      forward.emplace(label, env_variable_label(bdd, var, slots));
    }
    int normalized = bdd.rename(local, forward);
    std::string group = env_group(*row.view, selected, row.first, row.second);
    if (auto found = learned.parts.find(group);
        found != learned.parts.end() && found->second != normalized)
      decline("schema", "selected owner terms disagree across seeds");
    learned.parts[group] = normalized;
  }
  return learned;
}

int env_instantiate_previous(EnvBdd &bdd, const EnvView &view,
                             const EnvAnchor &first, const EnvAnchor &second,
                             const EnvLearned &learned, int previous_root) {
  auto selected = env_anchor_members(first, second);
  if (selected.empty() || selected.size() > 2)
    decline("instantiate", "selected owner term exceeds bounded arity");
  selected = env_selected(view, selected, first, second);
  std::map<int, int> slots;
  for (size_t p = 0; p < selected.size(); p++)
    slots.emplace(selected[p], int(p));
  auto at = learned.parts.find(env_group(view, selected, first, second));
  if (at == learned.parts.end())
    decline("instantiate", "selected owner template is absent");
  std::set<int> selected_set(selected.begin(), selected.end());
  std::map<int, int> back;
  for (const auto &[_, var] : view.variables)
    if (std::includes(selected_set.begin(), selected_set.end(),
                      var.owners.begin(), var.owners.end()))
      back.emplace(env_variable_label(bdd, var, slots),
                   env_variable_label(bdd, var));
  std::map<int, int> mapping;
  for (int label : bdd.support(at->second)) {
    if (!back.count(label))
      decline("instantiate", "selected owner variable is absent");
    mapping.emplace(label, back.at(label));
  }
  return bdd.apply(1, previous_root, bdd.rename(at->second, mapping));
}

struct EnvCanonicalVariable {
  const EnvVariable *source;
  std::set<int> owners;
};
struct EnvCanonical {
  const EnvView *view;
  std::string pattern;
  std::vector<int> members;
  std::map<int, int> anchor_slots, forward, backward;
  std::map<int, EnvCanonicalVariable> variables;

  EnvCanonical(EnvBdd &bdd, const EnvView &source, const EnvAnchor &first,
               const EnvAnchor &second)
      : view(&source) {
    auto order = env_anchor_members(first, second);
    for (size_t p = 0; p < order.size(); p++)
      anchor_slots.emplace(order[p], int(p));
    std::vector<std::string> patterns;
    for (const auto *anchor : {&first, &second}) {
      std::vector<std::string> positions;
      for (int owner : anchor->owners)
        positions.push_back(field(anchor_slots.at(owner)));
      patterns.push_back(join(positions));
    }
    pattern = join(patterns);
    for (int member : source.members)
      if (!anchor_slots.count(member))
        members.push_back(member);
    for (const auto &[_, variable] : source.variables) {
      std::set<int> owners = variable.owners;
      bool anchored = false;
      for (const auto &[anchor, _] : anchor_slots)
        anchored |= owners.erase(anchor) != 0;
      int concrete = env_variable_label(bdd, variable);
      int canonical = anchored
                          ? env_variable_label(bdd, variable, {}, anchor_slots)
                          : concrete;
      if (!variables.emplace(canonical, EnvCanonicalVariable{&variable, owners})
               .second)
        decline("typed_alignment", "anchor canonicalization collision");
      forward.emplace(concrete, canonical);
      backward.emplace(canonical, concrete);
    }
  }
  int canonical_function(EnvBdd &bdd, int function) const {
    std::map<int, int> mapping;
    for (int label : bdd.support(function))
      mapping.emplace(label, forward.at(label));
    return bdd.rename(function, mapping);
  }
  int concrete_function(EnvBdd &bdd, int function) const {
    std::map<int, int> mapping;
    for (int label : bdd.support(function))
      mapping.emplace(label, backward.at(label));
    return bdd.rename(function, mapping);
  }
};

int env_canonical_normal(EnvBdd &bdd, const EnvCanonical &view,
                         const EnvCanonicalVariable &var, int member) {
  std::map<int, int> slot{{member, 0}};
  return env_variable_label(bdd, *var.source, slot, view.anchor_slots);
}

std::pair<std::set<int>, std::set<int>>
env_local_shared(EnvBdd &bdd, const EnvCanonical &view, int function,
                 int member) {
  auto support = bdd.support(function);
  std::set<int> local, shared;
  for (int label : support) {
    const auto &var = view.variables.at(label);
    if (var.owners == std::set<int>{member})
      local.insert(label);
    if (var.owners.empty())
      shared.insert(label);
  }
  return {local, shared};
}

std::optional<int> env_normalized_feature(EnvBdd &bdd, const EnvCanonical &view,
                                          int function, int member, int mode) {
  auto [local, shared] = env_local_shared(bdd, view, function, member);
  if (local.empty())
    return std::nullopt;
  std::set<int> others;
  for (int label : bdd.support(function))
    if (!local.count(label) && !shared.count(label))
      others.insert(label);
  int result = mode < 2 ? bdd.quant(function, others, mode == 0) : [&] {
    std::map<int, bool> assignments;
    for (int label : others)
      assignments.emplace(label, mode == 3);
    return bdd.restrict_to(function, assignments);
  }();
  auto remaining = bdd.support(result);
  bool has_local = false;
  for (int label : local)
    has_local |= remaining.count(label) != 0;
  if (!has_local)
    return std::nullopt;
  std::map<int, int> mapping;
  for (int label : remaining)
    mapping.emplace(label, env_canonical_normal(
                               bdd, view, view.variables.at(label), member));
  return bdd.rename(result, mapping);
}

using EnvSummaryObservation = std::pair<EnvCanonical, int>;

std::vector<int>
env_summary_features(EnvBdd &bdd,
                     const std::vector<EnvSummaryObservation> &rows) {
  std::vector<int> candidates;
  for (int mode = 0; mode < 4; mode++) {
    std::vector<std::optional<int>> roots;
    for (const auto &[view, function] : rows)
      for (int member : view.members)
        roots.push_back(
            env_normalized_feature(bdd, view, function, member, mode));
    if (!roots.empty() && roots[0] &&
        std::all_of(roots.begin(), roots.end(),
                    [&](const auto &root) { return root && root == roots[0]; }))
      candidates.push_back(*roots[0]);
  }
  std::optional<std::set<int>> common;
  for (const auto &[view, function] : rows) {
    for (int member : view.members) {
      auto [local, _] = env_local_shared(bdd, view, function, member);
      std::set<int> signatures;
      for (int label : local)
        signatures.insert(
            env_canonical_normal(bdd, view, view.variables.at(label), member));
      if (!common)
        common = std::move(signatures);
      else {
        std::set<int> both;
        std::set_intersection(common->begin(), common->end(),
                              signatures.begin(), signatures.end(),
                              std::inserter(both, both.begin()));
        common = std::move(both);
      }
    }
  }
  std::vector<int> typed_bits;
  if (common) {
    std::vector<int> labels(common->begin(), common->end());
    std::sort(labels.begin(), labels.end(),
              [&](int a, int b) { return bdd.name(a) < bdd.name(b); });
    for (int label : labels)
      typed_bits.push_back(bdd.var(label));
  }
  candidates.insert(candidates.end(), typed_bits.begin(), typed_bits.end());
  for (size_t a = 0; a < typed_bits.size(); a++)
    for (size_t b = a + 1; b < typed_bits.size(); b++)
      candidates.push_back(bdd.apply(0, typed_bits[a], typed_bits[b]));
  for (size_t a = 0; a < typed_bits.size(); a++)
    for (size_t b = a + 1; b < typed_bits.size(); b++)
      candidates.push_back(bdd.apply(1, typed_bits[a], typed_bits[b]));
  std::set<int> seen;
  std::vector<int> unique;
  for (int root : candidates)
    if (seen.insert(root).second)
      unique.push_back(root);
  return unique;
}

int env_concrete_feature(EnvBdd &bdd, const EnvCanonical &view, int member,
                         int normalized) {
  std::map<int, int> back;
  for (const auto &[label, var] : view.variables)
    if (var.owners.empty() || var.owners == std::set<int>{member}) {
      int normal = env_canonical_normal(bdd, view, var, member);
      back.emplace(normal, label);
    }
  std::map<int, int> mapping;
  for (int label : bdd.support(normalized)) {
    auto at = back.find(label);
    if (at == back.end())
      decline("typed_alignment", "summary feature lacks a lane binding");
    mapping.emplace(label, at->second);
  }
  return bdd.rename(normalized, mapping);
}

std::array<int, 4> env_summary_bits(EnvBdd &bdd, const EnvCanonical &view,
                                    int normalized) {
  std::array<int, 4> at_least{1, 0, 0, 0};
  int all = 1;
  for (int member : view.members) {
    int feature = env_concrete_feature(bdd, view, member, normalized);
    all = bdd.apply(0, all, feature);
    for (int count : {3, 2, 1})
      at_least[count] = bdd.apply(1, at_least[count],
                                  bdd.apply(0, at_least[count - 1], feature));
  }
  return {at_least[1], at_least[2], at_least[3], all};
}

std::string env_summary_name(int position, int kind) {
  return key({"summary", field(position), field(kind)});
}

std::map<int, int> env_summary_mapping(EnvBdd &bdd, const EnvCanonical &view,
                                       const std::vector<int> &features) {
  std::map<int, int> mapping;
  for (size_t position = 0; position < features.size(); position++) {
    auto bits = env_summary_bits(bdd, view, features[position]);
    for (int kind = 0; kind < 4; kind++) {
      std::string name = env_summary_name(int(position), kind);
      std::string order = env_json_order(A{"summary", int(position), kind});
      int variable = bdd.label(name, EnvOrder{0, {}, order, order});
      mapping.emplace(variable, bits[kind]);
    }
  }
  return mapping;
}

std::optional<int>
env_summary_fit(EnvBdd &bdd, const std::vector<EnvSummaryObservation> &rows,
                const std::vector<int> &features) {
  int positive = 0, negative = 0;
  std::vector<std::map<int, int>> mappings;
  for (const auto &[view, function] : rows) {
    auto mapping = env_summary_mapping(bdd, view, features);
    int relation = 1;
    for (const auto &[label, bit] : mapping) {
      int variable = bdd.var(label);
      int same = bdd.apply(1, bdd.apply(0, variable, bit),
                           bdd.apply(0, bdd.neg(variable), bdd.neg(bit)));
      relation = bdd.apply(0, relation, same);
    }
    std::set<int> lanes;
    for (const auto &[label, var] : view.variables)
      if (!var.owners.empty())
        lanes.insert(label);
    int yes = bdd.quant(bdd.apply(0, relation, function), lanes, true);
    int no = bdd.quant(bdd.apply(0, relation, bdd.neg(function)), lanes, true);
    positive = bdd.apply(1, positive, yes);
    negative = bdd.apply(1, negative, no);
    mappings.push_back(std::move(mapping));
  }
  if (bdd.apply(0, positive, negative) != 0)
    return std::nullopt;
  for (size_t p = 0; p < rows.size(); p++)
    if (bdd.compose(positive, mappings[p]) != rows[p].second)
      return std::nullopt;
  return positive;
}

EnvLearned env_learn_summary(EnvBdd &bdd,
                             const std::vector<EnvObservation> &rows) {
  std::map<std::string, std::vector<EnvSummaryObservation>> groups;
  for (const auto &row : rows) {
    EnvCanonical canonical(bdd, *row.view, row.first, row.second);
    int function = canonical.canonical_function(bdd, row.root);
    groups[canonical.pattern].emplace_back(std::move(canonical), function);
  }
  EnvLearned learned;
  learned.kind = EnvLearned::Summary;
  for (const auto &[pattern, observations] : groups) {
    auto available = env_summary_features(bdd, observations);
    if (available.size() > 16)
      available.resize(16);
    bool found = false;
    for (int width : {0, 1, 2}) {
      std::vector<int> indices(available.size());
      std::iota(indices.begin(), indices.end(), 0);
      subsets(indices, width, [&](const std::vector<int> &chosen) {
        if (found)
          return;
        std::vector<int> features;
        for (int index : chosen)
          features.push_back(available[index]);
        auto template_root = env_summary_fit(bdd, observations, features);
        if (template_root) {
          learned.summaries[pattern] =
              EnvSummaryGroup{*template_root, std::move(features)};
          found = true;
        }
      });
      if (found)
        break;
    }
    if (!found)
      decline("schema", "no exact cross-lane summary");
  }
  return learned;
}

int env_instantiate_summary(EnvBdd &bdd, const EnvView &view,
                            const EnvAnchor &first, const EnvAnchor &second,
                            const EnvLearned &learned) {
  EnvCanonical canonical(bdd, view, first, second);
  auto at = learned.summaries.find(canonical.pattern);
  if (at == learned.summaries.end())
    decline("instantiate", "anchor pattern is absent in seed summaries");
  int function =
      bdd.compose(at->second.template_root,
                  env_summary_mapping(bdd, canonical, at->second.features));
  return canonical.concrete_function(bdd, function);
}

bool env_is_rank(const EnvOutput &output) {
  return output.name[0] == 'z' || output.name[0] == 'y' ||
         output.name[0] == 'x';
}

std::map<std::string, std::vector<EnvObservation>>
env_rank_observations(EnvBdd &bdd, const std::vector<EnvView> &views,
                      std::vector<std::string> &order) {
  std::map<std::string, std::vector<EnvObservation>> classes;
  for (size_t index = 0; index + 1 < views.size(); index++) {
    const EnvView &view = views[index];
    std::map<uint32_t, int> labels;
    const Aig *cert = view.instance->cert.get();
    for (uint32_t p = 0; p < aig_num_inputs(cert); p++) {
      uint32_t lit;
      const char *name = aig_input_name(cert, p, &lit);
      const auto &identity = view.game_names.at(name);
      const auto &variable = view.variables.at(identity);
      labels.emplace(lit / 2, env_variable_label(bdd, variable));
    }
    for (const auto &output : view.outputs) {
      if (!env_is_rank(output))
        continue;
      if (!index && !classes.count(output.class_key))
        order.push_back(output.class_key);
      int root = bdd.from_aig(cert, output.literal, labels);
      classes[output.class_key].push_back(
          {&view, root, output.first, output.second, output.name});
    }
  }
  for (const auto &[_, rows] : classes) {
    std::set<const EnvView *> present;
    for (const auto &row : rows)
      present.insert(row.view);
    if (present.size() != views.size() - 1)
      decline("typed_alignment", "rank class is absent in a seed");
  }
  return classes;
}

int env_instantiate_rank(EnvBdd &bdd, const EnvView &view,
                         const EnvAnchor &first, const EnvAnchor &second,
                         const EnvLearned &learned, int predecessor = 0) {
  if (learned.kind == EnvLearned::Summary)
    return env_instantiate_summary(bdd, view, first, second, learned);
  if (learned.kind == EnvLearned::Previous)
    return env_instantiate_previous(bdd, view, first, second, learned,
                                    predecessor);
  return env_instantiate_projection(
      bdd, view, learned.anchor_free ? EnvAnchor{} : first,
      learned.anchor_free ? EnvAnchor{} : second, learned);
}

std::map<std::string, EnvLearned> env_learn_ranks(
    EnvBdd &bdd,
    const std::map<std::string, std::vector<EnvObservation>> &classes,
    const std::vector<std::string> &order, A &class_trace) {
  std::map<std::string, EnvLearned> learned;
  for (const auto &class_key : order) {
    const auto &rows = classes.at(class_key);
    bdd.set_context(rows.front().name);
    EnvLearned current;
    try {
      current = env_learn_projection(bdd, rows);
    } catch (const Failure &projection) {
      if (projection.stage != "schema")
        throw;
      try {
        current = env_learn_summary(bdd, rows);
      } catch (const Failure &summary) {
        if (summary.stage != "schema")
          throw;
        const auto &sample = rows.front();
        size_t underscore = sample.name.find('_');
        std::string kind = sample.name.substr(0, underscore);
        int outer = std::stoi(sample.name.substr(underscore + 1));
        std::string prior_class =
            env_output_class("z", outer - 1, -1, EnvAnchor{}, EnvAnchor{});
        if (outer <= 0 || (kind != "z" && kind != "y" && kind != "x") ||
            !classes.count(prior_class))
          decline("schema", "rank has no exact bounded grammar");
        current = env_learn_previous(bdd, rows, classes.at(prior_class),
                                     "z_" + field(outer - 1));
      }
    }
    // Each fitting path proves equality with every seed rank: projection
    // rebuilds its source, summary composes its abstraction, and previous-z
    // checks the predecessor union. Reinstantiating here duplicates work.
    std::set<std::string> names;
    for (const auto &row : rows)
      if (row.view == rows.front().view)
        names.insert(row.name);
    A labels;
    for (const auto &name : names)
      labels.emplace_back(name);
    const char *rule = current.kind == EnvLearned::Summary    ? "summary"
                       : current.kind == EnvLearned::Previous ? "previous-z"
                       : current.anchor_free                  ? "anchor-free"
                                                              : "projection";
    class_trace.emplace_back(O{{"names", labels},
                               {"rule", rule},
                               {"arity", current.arity},
                               {"mode", current.mode},
                               {"predecessor", current.predecessor},
                               {"nodes", uint64_t(bdd.node_count())},
                               {"applies", bdd.apply_count()}});
    learned.emplace(class_key, std::move(current));
  }
  return learned;
}

void env_emit_target_ranks(EnvBdd &bdd, const EnvView &target,
                           const EnvView &first_seed,
                           const std::map<std::string, EnvLearned> &learned,
                           const Config &cfg, TlsfGr1EnvRankResult &out,
                           std::map<std::string, int> *rank_roots) {
  std::unique_ptr<Aig, decltype(&aig_free)> aig(aig_new(), &aig_free);
  if (!aig)
    throw Failure(TLSF_GR1_LIFT_LIMIT, "instantiate", "AIG allocation failed");
  std::map<int, uint32_t> literals;
  const Aig *game = target.instance->r.game;
  for (uint32_t p = 0; p < aig_num_latches(game); p++) {
    const char *name = aig_latch_name(game, p);
    if (!name)
      decline("instantiate", "target latch is unnamed");
    const auto &var = target.variables.at(target.game_names.at(name));
    literals.emplace(env_variable_label(bdd, var), aig_input(aig.get(), name));
  }
  for (uint32_t p = 0; p < aig_num_inputs(game); p++) {
    const char *name = aig_input_name(game, p, nullptr);
    const auto &var = target.variables.at(target.game_names.at(name));
    literals.emplace(env_variable_label(bdd, var), aig_input(aig.get(), name));
  }
  std::map<std::string, int> ranks;
  auto emit = [&](const std::string &name, const std::string &kind, int outer,
                  int depth, const EnvAnchor &first, const EnvAnchor &second) {
    cfg.check("instantiate");
    std::string class_key = env_output_class(kind, outer, depth, first, second);
    auto at = learned.find(class_key);
    if (at == learned.end())
      decline("instantiate", "target rank class is absent from seeds");
    int previous = 0;
    if (at->second.kind == EnvLearned::Previous) {
      auto prior = ranks.find(at->second.predecessor);
      if (prior == ranks.end())
        decline("instantiate", "previous target rank is absent");
      previous = prior->second;
    }
    int root =
        env_instantiate_rank(bdd, target, first, second, at->second, previous);
    ranks.emplace(name, root);
    aig_set_output(aig.get(), name.c_str(),
                   bdd.to_aig(aig.get(), root, literals));
  };
  for (uint32_t outer = 0; outer < first_seed.outer; outer++) {
    emit("z_" + field(outer), "z", int(outer), -1, {}, {});
    for (const auto &[goal, goal_anchor] : target.goals) {
      emit("y_" + field(outer) + "_" + field(goal), "y", int(outer), -1,
           goal_anchor, {});
      for (const auto &[fair, fair_anchor] : target.fairness) {
        std::set<int> depths;
        for (const auto &output : first_seed.outputs)
          if (output.name[0] == 'x' && output.outer == int(outer) &&
              output.first.kind == goal_anchor.kind &&
              output.second.kind == fair_anchor.kind)
            depths.insert(output.depth);
        if (depths.empty())
          decline("instantiate", "target rank level is absent in seeds");
        for (int depth : depths)
          emit("x_" + field(outer) + "_" + field(goal) + "_" + field(fair) +
                   "_" + field(depth),
               "x", int(outer), depth, goal_anchor, fair_anchor);
      }
    }
  }
  std::string bytes = render_aig(aig.get(), cfg);
  out.rank_aag = copy_bytes(bytes);
  out.rank_size = bytes.size();
  out.rank_classes = learned.size();
  for (const auto &[name, rule] : learned) {
    (void)name;
    if (rule.kind == EnvLearned::Projection)
      out.projection_classes++;
    else if (rule.kind == EnvLearned::Summary)
      out.summary_classes++;
    else
      out.previous_classes++;
    if (rule.anchor_free)
      out.anchor_free_classes++;
  }
  out.rank_nodes = bdd.node_count();
  out.rank_applies = bdd.apply_count();
  out.rank_cache_entries = bdd.cache_count();
  out.rank_accounted_bytes = bdd.accounted_bytes();
  if (rank_roots)
    *rank_roots = std::move(ranks);
}

struct EnvLayer {
  int phase, layer, target;
};

int env_and(EnvBdd &bdd, std::initializer_list<int> terms) {
  int result = 1;
  for (int term : terms)
    result = bdd.apply(0, result, term);
  return result;
}

void env_candidate(EnvBdd &bdd, const EnvView &view, const EnvView &seed,
                   std::map<std::string, int> ranks, const Config &cfg,
                   TlsfGr1EnvLiftResult &out) {
  const Aig *game = view.instance->r.game;
  const int outer = int(seed.outer);
  const int goals_count = int(aig_num_justice(game));
  const int explicit_fairs = int(aig_num_fairness(game));
  const int fair_count = std::max(1, explicit_fairs);
  std::map<uint32_t, int> labels;
  std::vector<int> state_labels, environment, system;
  std::map<int, int> next_state;
  bdd.set_context("policy_reconstruct/target_game_roots");
  for (uint32_t p = 0; p < aig_num_latches(game); p++) {
    uint32_t current, next;
    aig_latch_at(game, p, &current, &next, nullptr);
    const char *name = aig_latch_name(game, p);
    int label =
        env_variable_label(bdd, view.variables.at(view.game_names.at(name)));
    labels.emplace(current / 2, label);
    state_labels.push_back(label);
  }
  for (uint32_t p = 0; p < aig_num_inputs(game); p++) {
    uint32_t literal;
    const char *name = aig_input_name(game, p, &literal);
    int label =
        env_variable_label(bdd, view.variables.at(view.game_names.at(name)));
    labels.emplace(literal / 2, label);
    if (!strncmp(name, "controllable_", 13))
      system.push_back(label);
    else
      environment.push_back(label);
  }
  if (labels.size() != aig_num_latches(game) + aig_num_inputs(game))
    decline("typed_alignment", "target game variable inventory differs");
  int bad = 0;
  for (uint32_t p = 0; p < aig_num_bad(game); p++) {
    uint32_t literal;
    aig_bad_at(game, p, &literal);
    bad = bdd.apply(1, bad, bdd.from_aig(game, literal, labels));
  }
  if (!aig_num_bad(game)) {
    if (aig_num_outputs(game) != 1)
      decline("policy_reconstruct", "target has no unique bad predicate");
    bad = bdd.from_aig(
        game, aig_output_lit(game, aig_output_at(game, 0, nullptr)), labels);
  }
  for (uint32_t p = 0; p < aig_num_latches(game); p++) {
    uint32_t current, next;
    aig_latch_at(game, p, &current, &next, nullptr);
    next_state.emplace(labels.at(current / 2),
                       bdd.from_aig(game, next, labels));
  }
  std::vector<int> goals, fairs;
  for (int j = 0; j < goals_count; j++) {
    const uint32_t *literals;
    uint32_t count;
    aig_justice_at(game, j, &literals, &count);
    if (count != 1)
      decline("policy_reconstruct", "justice is not a single predicate");
    goals.push_back(bdd.from_aig(game, literals[0], labels));
  }
  for (int i = 0; i < explicit_fairs; i++)
    fairs.push_back(bdd.from_aig(game, aig_fairness_at(game, i), labels));
  if (fairs.empty())
    fairs.push_back(1);
  bdd.set_context("policy_reconstruct/rank_closure");
  for (int k = 0; k < outer; k++) {
    int z = 0;
    for (int j = 0; j < goals_count; j++) {
      int y = 1;
      for (int i = 0; i < fair_count; i++) {
        int depth = 0;
        while (ranks.count("x_" + field(k) + "_" + field(j) + "_" + field(i) +
                           "_" + field(depth)))
          depth++;
        if (!depth)
          decline("instantiate", "target inner rank is missing");
        y = bdd.apply(0, y,
                      ranks.at("x_" + field(k) + "_" + field(j) + "_" +
                               field(i) + "_" + field(depth - 1)));
      }
      ranks["y_" + field(k) + "_" + field(j)] = y;
      z = bdd.apply(1, z, y);
    }
    ranks["z_" + field(k)] = z;
  }
  ranks["inv"] = ranks.at("z_" + field(outer - 1));
  ranks[tlsf_gr1_check_winning_output_name] = bdd.neg(ranks.at("inv"));
  for (int j = 0; j < goals_count; j++)
    ranks["goal_" + field(j)] = goals[j];
  for (int i = 0; i < fair_count; i++)
    ranks["fair_" + field(i)] = fairs[i];

  bdd.set_context("policy_reconstruct/rank_layers");
  std::vector<EnvLayer> layers;
  int previous_z = 0;
  for (int k = 0; k < outer; k++) {
    int z = ranks.at("z_" + field(k));
    int outer_layer = bdd.apply(0, z, bdd.neg(previous_z));
    int previous_y = 0;
    for (int j = 0; j < goals_count; j++) {
      int y = ranks.at("y_" + field(k) + "_" + field(j));
      int selected = env_and(bdd, {outer_layer, y, bdd.neg(previous_y)});
      int base = env_and(bdd, {bdd.apply(1, previous_z, bdd.neg(goals[j])), y});
      for (int i = 0; i < fair_count; i++) {
        int previous_x = 0;
        for (int level = 0;; level++) {
          std::string name = "x_" + field(k) + "_" + field(j) + "_" + field(i) +
                             "_" + field(level);
          auto at = ranks.find(name);
          if (at == ranks.end())
            break;
          int layer = env_and(bdd, {selected, at->second, bdd.neg(previous_x)});
          int progress = bdd.apply(1, previous_x, fairs[i]);
          layers.push_back({i, layer, bdd.apply(0, base, progress)});
          previous_x = at->second;
        }
      }
      previous_y = bdd.apply(1, previous_y, y);
    }
    previous_z = z;
  }

  std::map<int, int> successor_cache;
  std::vector<int> relations;
  std::vector<std::map<int, int>> choices;
  std::set<int> system_set(system.begin(), system.end());
  std::set<int> environment_set(environment.begin(), environment.end());
  std::vector<int> skolem_order = environment;
  std::sort(skolem_order.begin(), skolem_order.end(), [&](int left, int right) {
    return bdd.name(left) < bdd.name(right);
  });
  for (int current = 0; current < fair_count; current++) {
    bdd.set_context("policy_reconstruct/mode_relation mode " + field(current));
    int advanced = (current + 1) % fair_count;
    int relation = 1;
    for (const auto &row : layers) {
      if (row.phase != current && row.phase != advanced)
        continue;
      int guarded = row.layer;
      if (current != advanced) {
        int guard =
            row.phase == advanced ? fairs[current] : bdd.neg(fairs[current]);
        guarded = bdd.apply(0, row.layer, guard);
      }
      if (!successor_cache.count(row.target))
        successor_cache.emplace(row.target,
                                bdd.compose(row.target, next_state));
      int obligation = bdd.apply(1, bad, successor_cache.at(row.target));
      relation =
          bdd.apply(0, relation, bdd.apply(1, bdd.neg(guarded), obligation));
    }
    int allowed = bdd.quant(relation, system_set, false);
    for (int variable : bdd.support(allowed))
      if (system_set.count(variable))
        decline("policy_reconstruct",
                "response letter survived quantification");
    int total = bdd.quant(allowed, environment_set, true);
    if (bdd.apply(0, ranks.at("inv"), bdd.neg(total)) != 0)
      decline("policy_totality", "no common environment move");
    std::map<int, int> selected;
    int remaining = allowed;
    bdd.set_context("policy_reconstruct/skolemize mode " + field(current));
    for (int variable : skolem_order) {
      std::set<int> rest = environment_set;
      for (const auto &[chosen, _] : selected)
        rest.erase(chosen);
      int zero = bdd.apply(0, remaining, bdd.neg(bdd.var(variable)));
      int can_zero = bdd.quant(zero, rest, true);
      int choice = bdd.neg(can_zero);
      for (int support : bdd.support(choice))
        if (system_set.count(support) || environment_set.count(support))
          decline("policy_reconstruct", "Skolem output reads current letter");
      selected.emplace(variable, choice);
      remaining = bdd.compose(remaining, {{variable, choice}});
    }
    relations.push_back(relation);
    choices.push_back(std::move(selected));
    ranks["move_" + field(current)] = relation;
  }

  std::vector<int> counters;
  for (int i = 0; i < fair_count; i++) {
    const auto &anchor = view.fairness.at(i);
    std::vector<std::string> owners;
    for (int owner : anchor.owners)
      owners.push_back(field(owner));
    EnvVariable variable{key({"counter", anchor.kind, join(owners)}),
                         key({"counter", anchor.kind}),
                         anchor.owners,
                         {anchor.owners.begin(), anchor.owners.end()},
                         env_json_order(A{"counter", anchor.kind})};
    counters.push_back(env_variable_label(bdd, variable));
  }
  auto select = [&](const std::vector<int> &roots) {
    int root = roots[0];
    for (int i = 1; i < fair_count; i++)
      root = bdd.ite(bdd.var(counters[i]), roots[i], root);
    return root;
  };
  bdd.set_context("policy_reconstruct/policy_outputs");
  std::map<std::string, int> policy;
  for (uint32_t p = 0; p < aig_num_inputs(game); p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (!strncmp(name, "controllable_", 13))
      continue;
    int variable =
        env_variable_label(bdd, view.variables.at(view.game_names.at(name)));
    std::vector<int> roots;
    for (const auto &mode : choices)
      roots.push_back(mode.at(variable));
    policy.emplace(name, select(roots));
  }
  for (int q = 0; q < fair_count; q++) {
    std::vector<int> updates;
    for (int current = 0; current < fair_count; current++) {
      int advanced = (current + 1) % fair_count;
      int update = 0;
      if (current == advanced)
        update = q == current ? 1 : 0;
      else if (q == current)
        update = bdd.neg(fairs[current]);
      else if (q == advanced)
        update = fairs[current];
      updates.push_back(update);
    }
    policy.emplace("curr_next_" + field(q), select(updates));
  }
  std::set<int> permitted(state_labels.begin(), state_labels.end());
  permitted.insert(counters.begin(), counters.end());
  for (const auto &[name, root] : policy)
    for (int variable : bdd.support(root))
      if (!permitted.count(variable))
        decline("policy_reconstruct", "policy reads current letter");

#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (env_rank_fault == 8)
    ranks["z_0"] = bdd.neg(ranks.at("z_0"));
#endif
  auto cert = std::unique_ptr<Aig, decltype(&aig_free)>(aig_new(), &aig_free);
  auto machine =
      std::unique_ptr<Aig, decltype(&aig_free)>(aig_new(), &aig_free);
  if (!cert || !machine)
    throw Failure(TLSF_GR1_LIFT_LIMIT, "emit", "AIG allocation failed");
  std::map<int, uint32_t> cert_literals, policy_literals;
  A state_rows, counter_rows, uncontrollable_rows, counter_next_rows;
  for (uint32_t p = 0; p < aig_num_latches(game); p++) {
    const char *name = aig_latch_name(game, p);
    int variable = state_labels[p];
    cert_literals[variable] = aig_input(cert.get(), name);
    policy_literals[variable] = aig_input(machine.get(), name);
    state_rows.emplace_back(
        O{{"policy_input", p}, {"game_latch", p}, {"name", name}});
  }
  for (uint32_t p = 0; p < aig_num_inputs(game); p++) {
    const char *name = aig_input_name(game, p, nullptr);
    cert_literals[labels.at([&] {
      uint32_t literal;
      aig_input_name(game, p, &literal);
      return literal / 2;
    }())] = aig_input(cert.get(), name);
  }
  for (int i = 0; i < fair_count; i++) {
    std::string name = "curr_" + field(i);
    policy_literals[counters[i]] = aig_input(machine.get(), name.c_str());
    counter_rows.emplace_back(O{{"policy_input", int(state_labels.size()) + i},
                                {"fairness", i},
                                {"name", name},
                                {"reset", 0},
                                {"effective_initial", i == 0}});
  }
  auto cert_output = [&](const std::string &name) {
    auto at = ranks.find(name);
    if (at == ranks.end())
      decline("instantiate", "target output lacks construction");
    aig_set_output(cert.get(), name.c_str(),
                   bdd.to_aig(cert.get(), at->second, cert_literals));
  };
  bdd.set_context("emit/certificate");
  cert_output("inv");
  cert_output(tlsf_gr1_check_winning_output_name);
  for (int j = 0; j < goals_count; j++)
    cert_output("goal_" + field(j));
  for (int i = 0; i < explicit_fairs; i++)
    cert_output("fair_" + field(i));
  for (int k = 0; k < outer; k++) {
    cert_output("z_" + field(k));
    for (int j = 0; j < goals_count; j++) {
      cert_output("y_" + field(k) + "_" + field(j));
      for (int i = 0; i < fair_count; i++)
        for (int level = 0;; level++) {
          std::string name = "x_" + field(k) + "_" + field(j) + "_" + field(i) +
                             "_" + field(level);
          if (!ranks.count(name))
            break;
          cert_output(name);
        }
    }
  }
  for (int i = 0; i < fair_count; i++)
    cert_output("move_" + field(i));
  bdd.set_context("emit/policy");
  int policy_output = 0;
  int environment_count = 0;
  for (uint32_t p = 0; p < aig_num_inputs(game); p++) {
    const char *name = aig_input_name(game, p, nullptr);
    if (!strncmp(name, "controllable_", 13))
      continue;
    aig_set_output(machine.get(), name,
                   bdd.to_aig(machine.get(), policy.at(name), policy_literals));
    uncontrollable_rows.emplace_back(O{
        {"policy_output", policy_output++}, {"game_input", p}, {"name", name}});
    environment_count++;
  }
  for (int i = 0; i < fair_count; i++) {
    std::string name = "curr_next_" + field(i);
    aig_set_output(machine.get(), name.c_str(),
                   bdd.to_aig(machine.get(), policy.at(name), policy_literals));
    counter_next_rows.emplace_back(
        O{{"policy_output", policy_output++}, {"fairness", i}, {"name", name}});
  }
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (env_rank_fault == 9)
    aig_set_output(machine.get(), "curr_next_0", AIG_FALSE);
  if (env_rank_fault == 10 && environment_count && !system.empty()) {
    std::string system_name;
    for (uint32_t p = 0; p < aig_num_inputs(game); p++) {
      const char *name = aig_input_name(game, p, nullptr);
      if (!strncmp(name, "controllable_", 13)) {
        system_name = name;
        break;
      }
    }
    uint32_t letter = aig_input(machine.get(), system_name.c_str());
    aig_set_output(machine.get(),
                   s(uncontrollable_rows[0].as_object(), "name").c_str(),
                   letter);
  }
#endif
  O certificate_meta = seed.instance->cert_meta;
  O policy_meta = j::parse(seed.instance->env_policy_json).as_object();
  certificate_meta["circuit"].as_object()["path"] = "memory";
  O &cc = certificate_meta["counts"].as_object();
  cc["goals"] = goals_count;
  std::string fairness_count_key = "fairness_assump";
  fairness_count_key += "tions";
  cc[fairness_count_key] = explicit_fairs;
  cc["fairness_counters"] = fair_count;
  cc["state_variables"] = int(state_labels.size());
  cc["original_game_latches"] = int(state_labels.size());
  cc["sampling_latches"] = 0;
  cc["uncontrollable_inputs"] = environment_count;
  cc["controllable_inputs"] = int(system.size());
  cc["predicates"] = aig_num_outputs(cert.get());
  cc["aig_inputs"] = aig_num_inputs(cert.get());
  cc["aig_latches"] = 0;
  cc["aig_ands"] = aig_num_ands(cert.get());
  policy_meta["circuit"].as_object()["path"] = "memory";
  O &pc = policy_meta["counts"].as_object();
  pc["game_state_variables"] = int(state_labels.size());
  pc["original_game_latches"] = int(state_labels.size());
  pc["sampling_latches"] = 0;
  pc["goals"] = goals_count;
  pc["fairness_counters"] = fair_count;
  pc["controllable_inputs"] = int(system.size());
  pc["uncontrollable_outputs"] = environment_count;
  pc["aig_inputs"] = aig_num_inputs(machine.get());
  pc["aig_outputs"] = aig_num_outputs(machine.get());
  pc["aig_ands"] = aig_num_ands(machine.get());
  policy_meta["inputs"] = O{
      {"state", state_rows}, {"counter", counter_rows}, {"controllable", A{}}};
  policy_meta["outputs"] = O{{"uncontrollable", uncontrollable_rows},
                             {"counter_next", counter_next_rows}};
  std::string certificate = render_aig(cert.get(), cfg);
  std::string machine_bytes = render_aig(machine.get(), cfg);
  std::string certificate_json = dump(certificate_meta);
  std::string policy_json = dump(policy_meta);
  cfg.bytes(certificate_json.size(), "emit");
  cfg.bytes(policy_json.size(), "emit");
  out.certificate_aag = copy_bytes(certificate);
  out.certificate_size = certificate.size();
  out.certificate_json = copy_bytes(certificate_json);
  out.certificate_json_size = certificate_json.size();
  out.policy_aag = copy_bytes(machine_bytes);
  out.policy_size = machine_bytes.size();
  out.policy_json = copy_bytes(policy_json);
  out.policy_json_size = policy_json.size();
}

void env_run(const TrustedTarget &trusted, const Config &cfg,
             TlsfGr1EnvRankResult &out, TlsfGr1EnvLiftResult *candidate) {
  uint64_t seed_started = now_ns();
  cfg.check("candidate");
  if (trusted.semantics != TLSF_GR1_EXACT)
    decline("target_reduction", "exact target reduction is required");
  char source_hash[65]{}, game_hash[65]{};
  if (!tlsf_pipeline_source_sha256(
          reinterpret_cast<const uint8_t *>(trusted.snapshot.data()),
          trusted.snapshot.size(), source_hash) ||
      trusted.source_hash != source_hash)
    decline("target_binding", "source snapshot hash differs");
  sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), game_hash);
  if (trusted.game_hash != game_hash ||
      trusted.game_aag !=
          std::string(trusted.instance->r.aag, trusted.instance->r.aag_size))
    decline("target_binding", "trusted game hash differs");
  env_reduction_binding(*trusted.instance, trusted.source_hash);
  EnvWindow window = env_window(trusted, cfg, out);
  for (const auto &seed : window.seeds)
    env_reduction_binding(*seed, trusted.source_hash);
  for (const auto &seed : window.seeds)
    (void)env_game_view(*seed, window.axis, seed->members);
  (void)env_game_view(*trusted.instance, window.axis, window.target_members);
  if (env_typed_classes(*trusted.instance) !=
      env_typed_classes(*window.seeds.front()))
    decline("typed_alignment", "target conjunct or role class missing");
  for (auto &seed : window.seeds)
    env_solve_seed(*seed, cfg, out);
  if (candidate)
    candidate->seed_ns = now_ns() - seed_started;
#ifdef TLSF_GR1_LIFT_TEST_FAULT
  if (env_rank_fault) {
    Instance &seed = *window.seeds.front();
    if (env_rank_fault == 1 || env_rank_fault == 3 || env_rank_fault == 4) {
      const char *name = env_rank_fault == 1   ? "extra_predicate"
                         : env_rank_fault == 3 ? "z_999"
                                               : "z_01";
      aig_set_output(seed.cert.get(), name, AIG_FALSE);
      seed.cert_meta["counts"].as_object()["predicates"] =
          aig_num_outputs(seed.cert.get());
    } else if (env_rank_fault == 2) {
      seed.cert_meta["counts"].as_object()["predicates"] =
          aig_num_outputs(seed.cert.get()) + 1;
    } else if (env_rank_fault == 5) {
      A &monitors = trusted.instance->data.at("monitors").as_array();
      J &left = monitors.at(0)
                    .as_object()
                    .at("source_origin")
                    .as_object()
                    .at("signal_refs");
      J &right = monitors.at(1)
                     .as_object()
                     .at("source_origin")
                     .as_object()
                     .at("signal_refs");
      std::swap(left, right);
    } else if (env_rank_fault == 6) {
      std::istringstream stream(seed.cert_aag);
      std::vector<std::string> lines;
      for (std::string line; std::getline(stream, line);)
        lines.push_back(std::move(line));
      unsigned max_var, inputs, latches, outputs, ands;
      if (lines.empty() ||
          sscanf(lines[0].c_str(), "aag %u %u %u %u %u", &max_var, &inputs,
                 &latches, &outputs, &ands) != 5)
        decline("schema_abi", "invalid seed certificate encoding");
      for (unsigned position = 0; position < outputs; position++) {
        const char *name = aig_output_at(seed.cert.get(), position, nullptr);
        if (name && !strcmp(name, "z_0")) {
          size_t line = 1u + inputs + latches + position;
          lines.at(line) = field(std::stoul(lines.at(line)) ^ 1u);
          break;
        }
      }
      seed.cert_aag.clear();
      for (const auto &line : lines)
        seed.cert_aag += line + "\n";
      seed.cert = parse_aig(seed.cert_aag.data(), seed.cert_aag.size());
    }
  }
#endif
  uint64_t preflight_started = now_ns();
  auto views = env_preflight(window, trusted);
  std::set<std::string> expected_roles;
  for (const auto &[_, role] : views.front().roles)
    expected_roles.insert(role);
  for (const auto &view : views) {
    std::set<std::string> roles;
    for (const auto &[_, role] : view.roles)
      roles.insert(role);
    if (roles != expected_roles)
      decline("typed_alignment", "distinct owner role inventory differs");
  }
  if (candidate)
    candidate->preflight_ns = now_ns() - preflight_started;
  cfg.check("schema");
  EnvBdd bdd(cfg);
  uint64_t rank_started = now_ns();
  uint64_t policy_started = 0;
  try {
    std::vector<std::string> order;
    auto classes = env_rank_observations(bdd, views, order);
    A class_trace;
    auto learned = env_learn_ranks(bdd, classes, order, class_trace);
    std::string trace = dump(class_trace);
    cfg.bytes(trace.size(), "schema");
    out.class_trace_json = copy_bytes(trace);
    out.class_trace_size = trace.size();
    std::map<std::string, int> roots;
    env_emit_target_ranks(bdd, views.back(), views.front(), learned, cfg, out,
                          candidate ? &roots : nullptr);
    cfg.check("instantiate");
    if (candidate) {
      candidate->rank_ns = now_ns() - rank_started;
      policy_started = now_ns();
      candidate->policy_nodes = bdd.node_count();
      candidate->policy_applies = bdd.apply_count();
      env_candidate(bdd, views.back(), views.front(), std::move(roots), cfg,
                    *candidate);
      cfg.check("policy_reconstruct");
      candidate->policy_nodes = bdd.node_count();
      candidate->policy_applies = bdd.apply_count();
      candidate->policy_cache_entries = bdd.cache_count();
      candidate->policy_accounted_bytes = bdd.accounted_bytes();
      candidate->policy_ns = now_ns() - policy_started;
    }
  } catch (...) {
    out.rank_nodes = bdd.node_count();
    out.rank_applies = bdd.apply_count();
    out.rank_cache_entries = bdd.cache_count();
    out.rank_accounted_bytes = bdd.accounted_bytes();
    if (candidate) {
      if (policy_started)
        candidate->policy_ns = now_ns() - policy_started;
      else
        candidate->rank_ns = now_ns() - rank_started;
      candidate->policy_nodes = bdd.node_count();
      candidate->policy_applies = bdd.apply_count();
      candidate->policy_cache_entries = bdd.cache_count();
      candidate->policy_accounted_bytes = bdd.accounted_bytes();
    }
    throw;
  }
}

void env_check(const TrustedTarget &trusted, const Config &cfg,
               TlsfGr1EnvLiftResult &candidate) {
  uint64_t check_started = now_ns();
  cfg.check("target_check");
  char hash[65]{};
  sha256_hex(trusted.game_aag.data(), trusted.game_aag.size(), hash);
  if (trusted.game_hash != hash ||
      trusted.game_aag !=
          std::string(trusted.instance->r.aag, trusted.instance->r.aag_size))
    decline("target_binding", "prepared game changed before verification");
  TlsfGr1CheckInput input{};
  input.game_aag = {(const uint8_t *)trusted.game_aag.data(),
                    trusted.game_aag.size()};
  input.certificate_aag = {(const uint8_t *)candidate.certificate_aag,
                           candidate.certificate_size};
  input.certificate_json = {(const uint8_t *)candidate.certificate_json,
                            candidate.certificate_json_size};
  input.policy_aag = {(const uint8_t *)candidate.policy_aag,
                      candidate.policy_size};
  input.policy_json = {(const uint8_t *)candidate.policy_json,
                       candidate.policy_json_size};
  TlsfGr1CheckOptions options{};
  options.method = TLSF_GR1_CHECK_CERTIFICATE;
  options.node_cap = cfg.o.checker_nodes;
  options.cache_cap = cfg.o.checker_cache;
  options.max_artifact_bytes = cfg.o.max_artifact_bytes;
  options.deadline_mono_ns = cfg.o.deadline_mono_ns;
  options.cancelled = cfg.o.cancelled;
  options.cancel_ctx = cfg.o.cancel_ctx;
  TlsfGr1CheckResult checked{};
  TlsfGr1CheckStatus status = tlsf_gr1_check(&input, &options, &checked);
  candidate.check_ns = now_ns() - check_started;
  candidate.target_checks++;
  if (cfg.stats) {
    cfg.stats->internal_checks++;
    cfg.stats->internal_check_peak_nodes = std::max<uint64_t>(
        cfg.stats->internal_check_peak_nodes, checked.peak_nodes);
  }
  bool verified =
      status == TLSF_GR1_CHECK_OK && checked.verdict == TLSF_GR1_CHECK_VERIFIED;
  candidate.verdict = TLSF_GR1_CHECK_UNKNOWN;
  if (verified) {
    std::string report(checked.json, checked.json_size);
    cfg.bytes(report.size(), "target_check");
    candidate.check_json = copy_bytes(report);
    candidate.check_json_size = report.size();
    candidate.verdict = TLSF_GR1_CHECK_VERIFIED;
  }
  std::string detail = checked.message;
  tlsf_gr1_check_result_clear(&checked);
  if (status == TLSF_GR1_CHECK_DEADLINE)
    throw Failure(TLSF_GR1_LIFT_DEADLINE, "target_check", "checker deadline");
  if (status == TLSF_GR1_CHECK_CANCELLED)
    throw Failure(TLSF_GR1_LIFT_CANCELLED, "target_check", "checker cancelled");
  if (status == TLSF_GR1_CHECK_LIMIT)
    throw Failure(TLSF_GR1_LIFT_LIMIT, "target_check", "checker capacity");
  if (!verified)
    decline("checker_rejected",
            detail.empty() ? "independent target certificate check failed"
                           : detail.c_str());
}
} // namespace gr1_lift_internal

using namespace gr1_lift_internal;

#ifdef TLSF_GR1_LIFT_TEST_FAULT
extern "C" int tlsf_gr1_env_rank_test_alignment() {
  auto owners = [](std::string_view json) {
    O origin = j::parse(json).as_object();
    return env_owners(origin, {"d"}, {0, 1, 2});
  };
  const auto shared = owners(
      R"({"index_tuple":[],"signal_refs":[{"declaration_id":"d","index_tuple":[0]}]})");
  const auto one = owners(
      R"({"index_tuple":[1],"signal_refs":[{"declaration_id":"d","index_tuple":[1]}]})");
  const auto pair = owners(
      R"({"index_tuple":[0,1],"signal_refs":[{"declaration_id":"d","index_tuple":[0,1]}]})");
  const auto equal = owners(
      R"({"index_tuple":[0,0],"signal_refs":[{"declaration_id":"d","index_tuple":[0]}]})");
  const auto linked = owners(
      R"({"index_tuple":[1],"signal_refs":[{"declaration_id":"d","index_tuple":[1,0]}]})");
  EnvView view;
  view.roles.emplace(0, "role");
  view.roles.emplace(1, "role");
  const std::string different = env_group(
      view, {0, 1}, EnvAnchor{"goal", {0, 1}}, EnvAnchor{"fair", {0, 1}});
  const std::string same = env_group(view, {0, 1}, EnvAnchor{"goal", {0, 0}},
                                     EnvAnchor{"fair", {0, 1}});
  return shared.empty() && one == std::vector<int>{1} &&
         pair == std::vector<int>({0, 1}) &&
         equal == std::vector<int>({0, 0}) &&
         linked == std::vector<int>({1, 0}) && different != same;
}
extern "C" void tlsf_gr1_env_rank_test_set_fault(int fault) {
  env_rank_fault = fault;
}
#endif
