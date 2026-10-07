#include "gr1_shared.hh"

namespace gr1_lift_internal {
#ifdef TLSF_GR1_LIFT_TEST_FAULT
thread_local bool typed_test_ambiguous_linkage = false;
#endif
std::pair<std::set<std::string>, std::set<std::string>>
typed_classes(const Instance &i) {
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

void typed_axis(const Instance &i, const std::string &axis) {
  std::string axis_id;
  std::set<std::string> parameter_ids;
  for (const J &value : i.data.at("source_parameters").as_array()) {
    const O &row = value.as_object();
    auto id = field(n(row, "id"));
    if (!parameter_ids.insert(id).second)
      decline(FailureCause::error, "typed_alignment",
              "duplicate parameter identity");
    if (s(row, "name") == axis)
      axis_id = id;
  }
  if (axis_id.empty())
    decline(FailureCause::error, "typed_alignment",
            "selected parameter identity is absent");
  std::map<std::string, std::pair<std::string, std::set<std::string>>> declared;
  bool indexed = false;
  for (const char *group : {"inputs", "outputs"})
    for (const J &value : i.data.at(group).as_array()) {
      const O &row = value.as_object();
      std::string role = s(row, "index_role");
      if (role != "scalar" && role != "element" && role != "representation-bit")
        decline(FailureCause::applicability, "typed_alignment",
                "undetermined signal index role");
      std::set<std::string> ids;
      if (role == "element") {
        if (!row.at("width_binding_complete").as_bool() ||
            !row.at("width_parameter_ids").is_array())
          decline(FailureCause::applicability, "typed_alignment",
                  "incomplete element width identity");
        for (const J &part : row.at("width_parameter_ids").as_array()) {
          std::string id = field(num(part));
          if (!parameter_ids.count(id) || !ids.insert(id).second)
            decline(FailureCause::error, "typed_alignment",
                    "invalid width parameter identity");
        }
        indexed |= ids.count(axis_id) != 0;
      }
      auto pair = std::pair{role, ids};
      auto [at, fresh] = declared.emplace(s(row, "declaration_id"), pair);
      if (!fresh && at->second != pair)
        decline(FailureCause::error, "typed_alignment",
                "inconsistent declaration binding");
    }
  if (!indexed)
    decline(FailureCause::applicability, "typed_alignment",
            "axis has no typed element declaration");
}

std::set<uint32_t> typed_support(const Aig *aig, uint32_t root) {
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

std::string typed_anchor_identity(const TypedAnchor &anchor) {
  std::vector<std::string> owners;
  for (int owner : anchor.owners)
    owners.push_back(field(owner));
  return key({anchor.kind, join(owners)});
}

std::set<std::string> typed_axis_declarations(const Instance &i,
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

std::vector<int> typed_owners(const O &origin,
                              const std::set<std::string> &axis_declarations,
                              const std::vector<int> &members) {
  auto bound = ints(origin.at("index_tuple").as_array());
  if (bound.empty())
    return {};
  for (int owner : bound)
    if (std::find(members.begin(), members.end(), owner) == members.end())
      decline(FailureCause::applicability, "typed_alignment",
              "monitor owner is outside the axis");
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
        decline(FailureCause::applicability, "typed_alignment",
                "pair owner lacks typed reference");
  return bound;
}

// Python json.dumps uses a space after each separator in an order key.
std::string typed_json_order(const J &value) {
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

std::string typed_letter_order_field(const O &row) {
  return typed_json_order(
      A{"letter", s(row, "direction"), s(row, "declaration_id")});
}

std::string typed_state_order_field(const O &row, const O &origin,
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
  return typed_json_order(fields);
}

TypedView typed_game_view(const Instance &i, const std::string &axis,
                          const std::vector<int> &members) {
  TypedView view;
  view.instance = &i;
  view.members = members;
  auto indexed = typed_axis_declarations(i, axis);
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
        decline(FailureCause::error, "typed_alignment",
                "duplicate game signal literal");
    }
  if (signals.size() != aig_num_inputs(i.r.game))
    decline(FailureCause::error, "typed_alignment",
            "game signal inventory differs");
  std::set<uint32_t> game_inputs;
  for (uint32_t p = 0; p < aig_num_inputs(i.r.game); p++) {
    uint32_t lit;
    const char *name = aig_input_name(i.r.game, p, &lit);
    if (!signals.count(lit / 2) || !game_inputs.insert(lit / 2).second)
      decline(FailureCause::error, "typed_alignment",
              "game signal lacks unique provenance");
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
             .emplace(identity, TypedVariable{identity, prefix, indices, owners,
                                              typed_letter_order_field(row)})
             .second)
      decline(FailureCause::error, "typed_alignment",
              "duplicate letter identity");
    if (!name || !view.game_names.emplace(name, identity).second)
      decline(FailureCause::error, "typed_alignment",
              "game signal name inventory differs");
  }
  if (game_inputs != [&] {
        std::set<uint32_t> keys;
        for (const auto &[literal, _] : signals)
          keys.insert(literal);
        return keys;
      }())
    decline(FailureCause::error, "typed_alignment",
            "game signal inventory is incomplete");
  std::map<std::string, const O *> conjuncts;
  for (const J &value : i.data.at("source_conjuncts").as_array()) {
    const O &row = value.as_object();
    if (!conjuncts
             .emplace(key({s(row, "source_formula_id"),
                           field(n(row, "generated_position"))}),
                      &row)
             .second)
      decline(FailureCause::error, "typed_alignment",
              "duplicate source conjunct identity");
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
      decline(FailureCause::applicability, "typed_alignment",
              "monitor lacks frontend origin");
    const O &origin = row.at("source_origin").as_object();
    auto owners = typed_owners(origin, indexed, members);
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
      decline(FailureCause::error, "typed_alignment",
              "monitor source conjunct is missing");
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
        decline(FailureCause::error, "typed_alignment",
                "monitor latch inventory differs");
      own_latches.insert(lit / 2);
      auto support = typed_support(i.r.game, latch_next.at(lit / 2));
      for (uint32_t signal : support)
        if (signals.count(signal)) {
          const O &ref = *signals.at(signal);
          actual_refs.insert(
              key({s(ref, "declaration_id"), dump(ref.at("index_tuple"))}));
        }
    }
    if (claimed_refs != actual_refs)
      decline(FailureCause::error, "schema_abi",
              "monitor transition references differ");
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
      decline(FailureCause::error, "typed_alignment",
              "monitor/source construction differs");
    std::string link =
        key({s(row, "role"), join(owner_fields), origin_key, s(row, "template"),
             dump(origin.at("signal_refs"))});
#ifdef TLSF_GR1_LIFT_TEST_FAULT
    if (typed_test_ambiguous_linkage && !linkage.empty())
      link = *linkage.begin();
#endif
    if (!linkage.insert(link).second)
      decline(FailureCause::error, "typed_alignment",
              "ambiguous sibling linkage");
    if (s(row, "role") == "justice") {
      int index = int(n(row, "justice_index"));
      if (index < 0 || index >= int(aig_num_justice(i.r.game)) ||
          !view.goals.emplace(index, TypedAnchor{base, owners}).second)
        decline(FailureCause::error, "typed_alignment",
                "justice ordinal inventory differs");
      const uint32_t *lits;
      uint32_t count;
      aig_justice_at(i.r.game, index, &lits, &count);
      for (uint32_t p = 0; p < count; p++) {
        auto support = typed_support(i.r.game, lits[p]);
        for (uint32_t var : support)
          if (!own_latches.count(var))
            decline(FailureCause::error, "typed_alignment",
                    "justice points outside its monitor");
      }
    } else if (s(row, "role") == "fairness") {
      if (fair_index >= int(aig_num_fairness(i.r.game)))
        decline(FailureCause::error, "typed_alignment",
                "fairness ordinal exceeds game");
      for (uint32_t var :
           typed_support(i.r.game, aig_fairness_at(i.r.game, fair_index)))
        if (!own_latches.count(var))
          decline(FailureCause::error, "typed_alignment",
                  "fairness points outside its monitor");
      view.fairness.emplace(fair_index++, TypedAnchor{base, owners});
    }
  }
  if (typed_latches.size() != latch_next.size() ||
      view.goals.size() != aig_num_justice(i.r.game) ||
      fair_index != int(aig_num_fairness(i.r.game)))
    decline(FailureCause::error, "typed_alignment",
            "monitor game inventory is incomplete");
  if (view.fairness.empty())
    view.fairness.emplace(0, TypedAnchor{"synthetic", {}});
  for (const auto &[group, rows] : siblings) {
    std::set<std::string> variants;
    for (const O *row : rows) {
      std::string variant =
          key({s(*row, "template"),
               dump(row->at("source_origin").as_object().at("signal_refs"))});
      if (!variants.insert(variant).second)
        decline(FailureCause::applicability, "typed_alignment",
                "ambiguous sibling monitor roles");
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
                          TypedVariable{identity, prefix, indices, owner_set,
                                        typed_state_order_field(*row, origin,
                                                                rows, state)})
                 .second)
          decline(FailureCause::error, "typed_alignment",
                  "duplicate state identity");
        if (!view.game_names.emplace(latch_names.at(lit / 2), identity).second)
          decline(FailureCause::error, "typed_alignment",
                  "game latch name inventory differs");
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

std::vector<int> typed_anchor_members(const TypedAnchor &first,
                                      const TypedAnchor &second) {
  std::vector<int> order;
  for (const auto *anchor : {&first, &second})
    for (int owner : anchor->owners)
      if (std::find(order.begin(), order.end(), owner) == order.end())
        order.push_back(owner);
  return order;
}

std::vector<int> typed_selected(const std::map<int, std::string> &roles,
                                const std::vector<int> &subset,
                                const TypedAnchor &first,
                                const TypedAnchor &second) {
  auto priority = typed_anchor_members(first, second);
  std::vector<int> selected = subset;
  std::sort(selected.begin(), selected.end(), [&](int a, int b) {
    auto left = std::find(priority.begin(), priority.end(), a);
    auto right = std::find(priority.begin(), priority.end(), b);
    int ia = left == priority.end() ? int(priority.size())
                                    : int(left - priority.begin());
    int ib = right == priority.end() ? int(priority.size())
                                     : int(right - priority.begin());
    return std::tie(ia, roles.at(a), a) < std::tie(ib, roles.at(b), b);
  });
  return selected;
}

std::string typed_anchor_class(const std::map<int, std::string> &roles,
                               const TypedAnchor &first,
                               const TypedAnchor &second) {
  std::map<int, int> slots;
  std::vector<std::string> anchors;
  for (const auto *anchor : {&first, &second}) {
    std::vector<std::string> owners;
    for (int owner : anchor->owners) {
      auto [at, fresh] = slots.emplace(owner, int(slots.size()));
      owners.push_back(key({roles.at(owner), field(at->second)}));
    }
    anchors.push_back(key({anchor->kind, join(owners)}));
  }
  return join(anchors);
}

std::string typed_group(const std::map<int, std::string> &roles,
                        const std::vector<int> &selected,
                        const TypedAnchor &first, const TypedAnchor &second) {
  std::map<int, int> slots;
  std::vector<std::string> role_items;
  for (size_t p = 0; p < selected.size(); p++) {
    slots.emplace(selected[p], int(p));
    role_items.push_back(roles.at(selected[p]));
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

std::string typed_variable_key(const std::string &prefix,
                               const std::vector<int> &indices,
                               const std::set<int> &owners,
                               const std::map<int, int> &slots,
                               const std::map<int, int> &anchors) {
  std::vector<std::string> fields;
  for (int index : indices) {
    if (owners.count(index) && anchors.count(index))
      fields.push_back(key({"anchor", field(anchors.at(index))}));
    else if (owners.count(index) && slots.count(index))
      fields.push_back(key({"slot", field(slots.at(index))}));
    else
      fields.push_back(key({"fixed", field(index)}));
  }
  return key({prefix, join(fields)});
}

std::string typed_shape(const Instance &i, const std::string &axis,
                        const std::vector<int> &members) {
  typed_axis(i, axis);
  if (s(i.data, "semantics") != "exact")
    decline(FailureCause::unsupported, "typed_alignment",
            "typed R requires exact semantics");
  auto view = typed_game_view(i, axis, members);
  std::set<std::string> roles, variables, anchors;
  for (const auto &[_, role] : view.roles)
    roles.insert(role);
  for (const auto &[_, variable] : view.variables) {
    std::map<int, int> slots;
    for (int index : variable.indices)
      if (variable.owners.count(index))
        slots.emplace(index, int(slots.size()));
    variables.insert(typed_variable_key(variable.prefix, variable.indices,
                                        variable.owners, slots));
  }
  for (const auto *inventory : {&view.goals, &view.fairness})
    for (const auto &[_, anchor] : *inventory)
      anchors.insert(typed_anchor_class(view.roles, anchor, {}));
  for (const auto &[goal_number, goal] : view.goals)
    for (const auto &[fair_number, fair] : view.fairness)
      anchors.insert(typed_anchor_class(view.roles, goal, fair));
  auto classes = typed_classes(i);
  return key({join({classes.first.begin(), classes.first.end()}),
              join({classes.second.begin(), classes.second.end()}),
              join({roles.begin(), roles.end()}),
              join({variables.begin(), variables.end()}),
              join({anchors.begin(), anchors.end()}),
              s(i.data, "latch_encoding")});
}
} // namespace gr1_lift_internal
