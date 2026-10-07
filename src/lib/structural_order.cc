#include "tlsf/structural_order.h"
#include "tlsf/pipeline.h"
#include "yyjson_cpp.hh"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <numeric>
#include <set>
#include <string>
#include <tuple>
#include <vector>

namespace {
namespace j = tlsf_json;
using O = j::object;
using A = j::array;
using Coordinates = std::vector<int64_t>;

int64_t number(const j::value &v) {
  return v.is_int64() ? v.as_int64() : int64_t(v.as_uint64());
}
Coordinates numbers(const A &array) {
  Coordinates result;
  for (const auto &v : array)
    result.push_back(number(v));
  return result;
}
std::string text(const O &row, const char *key) {
  return std::string(row.at(key).as_string());
}
struct Variable {
  uint32_t id = 0;
  int role = 0;
  uint32_t declaration = 0;
  Coordinates axes, owners, local;
  std::string name;
};
uint32_t declaration(const O &row) {
  // declaration_id is the frontend schema's direction:ordinal, not an AP.
  const auto id = text(row, "declaration_id");
  const auto at = id.find(':');
  if (at == std::string::npos)
    throw std::runtime_error("invalid declaration ID");
  size_t used = 0;
  unsigned long value = std::stoul(id.substr(at + 1), &used);
  if (used != id.size() - at - 1 || value > UINT32_MAX)
    throw std::runtime_error("invalid declaration ordinal");
  return uint32_t(value);
}
Variable signal(const O &row, uint32_t id, int role) {
  Variable v;
  v.id = id;
  v.role = role;
  v.declaration = declaration(row);
  v.name = text(row, "name");
  const auto coords = numbers(row.at("index_tuple").as_array());
  const auto kind = text(row, "index_role");
  if (kind == "element" && row.at("width_binding_complete") == true) {
    v.axes = numbers(row.at("width_parameter_ids").as_array());
    // A concrete axis is required; fixed-width and undetermined buses retain
    // local coordinates, without inventing client ownership.
    if (!v.axes.empty())
      v.owners = coords;
  }
  if (v.owners.empty()) {
    v.axes.clear();
    v.local = coords;
  }
  return v;
}
bool less(const Variable &a, const Variable &b, TlsfStructuralOrder order) {
  if (order == TLSF_ORDER_ROLE_GROUPED)
    return std::tie(a.role, a.declaration, a.axes, a.owners, a.local, a.id) <
           std::tie(b.role, b.declaration, b.axes, b.owners, b.local, b.id);
  return std::tie(a.axes, a.owners, a.role, a.declaration, a.local, a.id) <
         std::tie(b.axes, b.owners, b.role, b.declaration, b.local, b.id);
}
bool valid_order(TlsfStructuralOrder order) {
  return order >= TLSF_ORDER_INCUMBENT && order <= TLSF_ORDER_ROLE_GROUPED;
}
} // namespace

extern "C" int tlsf_structural_ap_order_v1(const uint8_t *source, size_t size,
                                           TlsfStructuralOrder order,
                                           int lowercase, char ***names,
                                           size_t *count) {
  if (!names || !count)
    return 0;
  *names = nullptr;
  *count = 0;
  if (!valid_order(order))
    return 0;
  if (order == TLSF_ORDER_INCUMBENT)
    return 1;
  try {
    char hash[65]{};
    if (!tlsf_pipeline_source_sha256(source, size, hash))
      return 0;
    TlsfPipelineOptions opts{};
    opts.source_sha256 = hash;
    std::unique_ptr<TlsfPipeline, decltype(&tlsf_pipeline_free)> pipeline(
        tlsf_pipeline_load_bytes(source, size, &opts), tlsf_pipeline_free);
    if (!pipeline)
      return 0;
    if (!pipeline->frontend_provenance_json)
      return 1;
    const auto data = j::parse(pipeline->frontend_provenance_json).as_object();
    if (data.at("schema") != "tlsf-tools.frontend-provenance.v1" ||
        number(data.at("format_version")) != 1 ||
        data.at("source_sha256") != hash)
      return 0;
    if (data.at("ambiguous") != false)
      return 1;
    std::vector<Variable> variables;
    std::set<std::string> inventory;
    for (const auto &value : data.at("signals").as_array()) {
      const auto &row = value.as_object();
      const auto direction = text(row, "direction");
      if (direction != "input" && direction != "output")
        return 0;
      auto v = signal(row, uint32_t(variables.size()), direction == "output");
      if (lowercase)
        for (char &c : v.name)
          c = char(std::tolower(static_cast<unsigned char>(c)));
      if (!inventory.insert(v.name).second)
        return 0;
      variables.push_back(std::move(v));
    }
    std::stable_sort(
        variables.begin(), variables.end(), [&](const auto &a, const auto &b) {
          // MONA's supported registration hook requires input/output blocks.
          return a.role != b.role ? a.role < b.role : less(a, b, order);
        });
    auto result =
        static_cast<char **>(calloc(variables.size(), sizeof(char *)));
    if (!result && !variables.empty())
      return 0;
    for (size_t i = 0; i < variables.size(); i++) {
      result[i] = strdup(variables[i].name.c_str());
      if (!result[i]) {
        for (size_t k = 0; k < i; k++)
          free(result[k]);
        free(result);
        return 0;
      }
    }
    *names = result;
    *count = variables.size();
    return 1;
  } catch (...) {
    return 0;
  }
}

extern "C" int
tlsf_structural_game_order_v1(const Aig *game, const char *provenance,
                              TlsfStructuralOrder order, uint32_t auxiliary,
                              uint32_t **variables, size_t *count) {
  if (!game || !variables || !count)
    return 0;
  *variables = nullptr;
  *count = 0;
  if (!valid_order(order))
    return 0;
  try {
    const uint32_t ni = aig_num_inputs(game), nl = aig_num_latches(game);
    const size_t total = size_t(ni) + nl + auxiliary;
    if (total > UINT32_MAX)
      return 0;
    std::vector<Variable> rows(total);
    for (uint32_t i = 0; i < total; i++)
      rows[i].id = i;
    bool typed = false;
    O data;
    if (provenance && order != TLSF_ORDER_INCUMBENT) {
      data = j::parse(provenance).as_object();
      typed =
          data.at("schema") == "tlsf-tools.gr1-monitor-game.provenance.v3" &&
          data.at("provenance_source") == "frontend" &&
          data.at("source_origin_metadata").as_object().at("available") == true;
    }
    if (typed) {
      std::map<uint32_t, uint32_t> input_ids, latch_ids;
      for (uint32_t i = 0; i < ni; i++) {
        uint32_t lit;
        aig_input_name(game, i, &lit);
        input_ids.emplace(lit, i);
      }
      for (uint32_t i = 0; i < nl; i++) {
        uint32_t lit;
        aig_latch_at(game, i, &lit, nullptr, nullptr);
        latch_ids.emplace(lit, ni + i);
      }
      std::set<uint32_t> seen;
      std::map<std::string, Variable> declarations;
      for (int role = 0; role < 2; role++)
        for (const auto &value :
             data.at(role ? "outputs" : "inputs").as_array()) {
          const auto &row = value.as_object();
          if (row.at("provenance_source") != "frontend")
            return 0;
          uint32_t lit = uint32_t(number(row.at("game_literal")));
          auto found = input_ids.find(lit);
          if (found == input_ids.end() || !seen.insert(found->second).second)
            return 0;
          rows[found->second] = signal(row, found->second, role);
          declarations.emplace(text(row, "declaration_id"),
                               rows[found->second]);
        }
      uint32_t monitor_id = 0;
      for (const auto &value : data.at("monitors").as_array()) {
        const auto &row = value.as_object();
        if (row.at("provenance_source") != "frontend")
          return 0;
        const auto &origin = row.at("source_origin").as_object();
        Variable v;
        const auto role = text(row, "role");
        v.role = role == "bad"        ? 2
                 : role == "violated" ? 3
                 : role == "fairness" ? 4
                                      : 5;
        v.declaration = monitor_id++;
        // Generator bindings supply ordered owners. References supply typed
        // axes. Shared monitors have no element references and remain unowned;
        // representation bits never create owners.
        for (const auto &binding : origin.at("bindings").as_array()) {
          int64_t owner = number(binding.as_object().at("value"));
          Coordinates axes;
          for (const auto &ref_value : origin.at("signal_refs").as_array()) {
            const auto &ref = ref_value.as_object();
            if (ref.at("index_role") != "element")
              continue;
            const auto &decl = declarations.at(text(ref, "declaration_id"));
            if (numbers(ref.at("index_tuple").as_array()) ==
                    Coordinates{owner} &&
                !decl.axes.empty()) {
              if (!axes.empty() && axes != decl.axes)
                return 0;
              axes = decl.axes;
            }
          }
          if (!axes.empty()) {
            v.axes.insert(v.axes.end(), axes.begin(), axes.end());
            v.owners.push_back(owner);
          }
        }
        uint32_t local = 0;
        for (const auto &lit_value : row.at("latch_literals").as_array()) {
          auto found = latch_ids.find(uint32_t(number(lit_value)));
          if (found == latch_ids.end() || !seen.insert(found->second).second)
            return 0;
          v.id = found->second;
          v.local = {local++};
          rows[v.id] = v;
        }
      }
      if (seen.size() != size_t(ni) + nl)
        return 0;
      for (uint32_t i = ni + nl; i < total; i++) {
        rows[i].role = 6;
        rows[i].declaration = i - ni - nl;
      }
      std::stable_sort(
          rows.begin(), rows.end(),
          [&](const auto &a, const auto &b) { return less(a, b, order); });
    }
    auto result = static_cast<uint32_t *>(malloc(total * sizeof(uint32_t)));
    if (!result && total)
      return 0;
    for (size_t i = 0; i < total; i++)
      result[i] = rows[i].id;
    *variables = result;
    *count = total;
    return 1;
  } catch (...) {
    return 0;
  }
}
