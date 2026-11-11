#include "tlsf/symmetry.h"

#include <algorithm>
#include <map>
#include <memory>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace {

using Id = size_t;

struct Node {
  TlsfAstKind kind;
  Id ap = 0;
  std::vector<Id> children;
  bool operator==(const Node &) const = default;
};

struct Hash {
  size_t operator()(const Node &n) const {
    size_t h = static_cast<size_t>(n.kind) * 31 + n.ap;
    for (Id child : n.children)
      h = h * 31 + child;
    return h;
  }
};

// Hash collisions use full key equality. IDs are shared between the original
// and renamed formulas. Only AND/OR associativity and commutativity, and EQUIV
// commutativity, identify different syntax; all preserve infinite-word meaning.
// The TLSF AST has no XOR kind (negated EQUIV already benefits from sorting).
struct Dag {
  std::vector<Node> nodes;
  std::unordered_map<Node, Id, Hash> ids;

  Id intern(Node n) {
    if (n.kind == TLSF_AST_AND || n.kind == TLSF_AST_OR ||
        n.kind == TLSF_AST_EQUIV)
      std::sort(n.children.begin(), n.children.end());
    auto [it, inserted] = ids.emplace(n, nodes.size());
    if (inserted)
      nodes.push_back(std::move(n));
    return it->second;
  }

  Id from_ast(const TlsfAstNode *root,
              const std::unordered_map<std::string, Id> &aps,
              unsigned depth = 0) {
    if (!root || depth > 1024)
      throw std::runtime_error(
          "missing objective or syntax depth exceeds 1024");
    Node n{tlsf_ast_node_kind(root), 0, {}};
    if (n.kind == TLSF_AST_KIND_COUNT || n.kind == TLSF_AST_X_STRONG)
      throw std::runtime_error("unsupported objective node kind " +
                               std::to_string(n.kind));
    if (n.kind == TLSF_AST_AP) {
      const char *name = tlsf_ast_node_ap_name(root);
      auto it = aps.find(name ? name : "");
      if (it == aps.end())
        throw std::runtime_error("objective AP missing from partition");
      n.ap = it->second;
    } else if (n.kind == TLSF_AST_AND || n.kind == TLSF_AST_OR) {
      // Collect the whole associative spine before interning, avoiding the
      // quadratic intermediate vectors of a left-nested conjunction.
      std::vector<std::pair<const TlsfAstNode *, unsigned>> pending{
          {root, depth}};
      while (!pending.empty()) {
        auto [child, level] = pending.back();
        pending.pop_back();
        if (level > 1024)
          throw std::runtime_error("syntax depth exceeds 1024");
        if (tlsf_ast_node_kind(child) == n.kind) {
          for (uint32_t i = 0; i < 2; ++i)
            pending.emplace_back(tlsf_ast_node_child(child, i), level + 1);
        } else {
          n.children.push_back(from_ast(child, aps, level));
        }
      }
    } else {
      for (uint32_t i = 0; i < tlsf_ast_node_child_count(root); ++i)
        n.children.push_back(
            from_ast(tlsf_ast_node_child(root, i), aps, depth + 1));
    }
    return intern(std::move(n));
  }

  bool invariant(Id root, const std::vector<Id> &permutation) const {
    // Each candidate gets the same original IDs, without retaining scratch
    // nodes from earlier candidates. Renaming preserves flattened spines.
    Dag renamed = *this;
    std::vector<Id> image(nodes.size());
    for (Id i = 0; i < nodes.size(); ++i) {
      Node n = nodes[i];
      if (n.kind == TLSF_AST_AP)
        n.ap = permutation.at(n.ap);
      for (Id &child : n.children)
        child = image.at(child);
      image[i] = renamed.intern(std::move(n));
    }
    return image.at(root) == root;
  }
};

// C views borrow storage from this one owner. Moving inner vectors preserves
// their buffers; views of the outer vectors are published only at the end.
struct Result : TlsfSymmetryResult {
  struct Range {
    std::vector<uint32_t> families;
    std::vector<std::vector<uint16_t>> images;
    std::vector<TlsfSymmetryCandidate> candidates;
  };
  std::string objective_reason;
  std::vector<Range> storage;
  std::vector<TlsfSymmetryRange> range_views;
  std::vector<std::vector<Id>> permutations;
  std::vector<TlsfSymmetryGenerator> generator_views;

  Result() : TlsfSymmetryResult{} {}
};

TlsfSymmetryStatus detect(const TlsfConversionResult *c,
                          TlsfSymmetryResult **out) {
  if (!c || !c->ast || (c->n_inputs && !c->inputs) ||
      (c->n_outputs && !c->outputs) ||
      (c->n_indexed_families && !c->indexed_families))
    return TLSF_SYMMETRY_INVALID;
  auto result = std::make_unique<Result>();
  std::unordered_map<std::string, Id> aps;
  auto add_aps = [&](char **names, uint32_t count) {
    for (uint32_t i = 0; i < count; ++i)
      if (!names[i] || !aps.emplace(names[i], aps.size()).second)
        return false;
    return true;
  };
  if (!add_aps(c->inputs, c->n_inputs) || !add_aps(c->outputs, c->n_outputs))
    return TLSF_SYMMETRY_INVALID;
  result->n_aps = aps.size();

  std::map<std::pair<uint16_t, uint16_t>, std::vector<uint32_t>> groups;
  for (uint32_t i = 0; i < c->n_indexed_families; ++i) {
    const auto &f = c->indexed_families[i];
    if (f.lo > f.hi || (f.n_members && !f.members))
      return TLSF_SYMMETRY_INVALID;
    groups[{f.lo, f.hi}].push_back(i);
  }

  Dag dag;
  Id root = 0;
  try {
    root = dag.from_ast(tlsf_ast_root(c->ast), aps);
  } catch (const std::runtime_error &e) {
    result->objective_reason = e.what();
    result->reason = result->objective_reason.c_str();
  }

  for (const auto &[bounds, indices] : groups) {
    const auto [lo, hi] = bounds;
    size_t size = static_cast<size_t>(hi) - lo + 1;
    result->storage.emplace_back();
    auto &storage = result->storage.back();
    storage.families = indices;
    TlsfSymmetryRange range{};
    range.lo = lo;
    range.hi = hi;
    range.families = storage.families.data();
    range.n_families = indices.size();

    std::vector<std::vector<Id>> members;
    for (uint32_t index : indices) {
      const auto &f = c->indexed_families[index];
      members.emplace_back();
      if (f.n_members != size)
        range.reason = "unresolved indexed family";
      for (uint32_t k = 0; k < f.n_members; ++k) {
        auto it = aps.find(f.members[k] ? f.members[k] : "");
        if (it == aps.end() || (it->second >= c->n_inputs) != f.is_output)
          range.reason = "family does not preserve the input/output partition";
        else
          members.back().push_back(it->second);
      }
    }
    bool adjacent = size >= 2 && !result->reason && !range.reason;
    bool rotation = false;
    if (size >= 2 && !range.reason)
      for (size_t k = 0; k < size; ++k) {
        bool rotate = k == size - 1;
        std::vector<Id> permutation(aps.size());
        std::iota(permutation.begin(), permutation.end(), 0);
        std::vector<uint16_t> image;
        for (size_t i = 0; i < size; ++i) {
          size_t to = rotate       ? (i + 1) % size
                      : i == k     ? k + 1
                      : i == k + 1 ? k
                                   : i;
          image.push_back(static_cast<uint16_t>(lo + to));
          for (const auto &family : members)
            permutation[family[i]] = family[to];
        }
        // Check the complete AP permutation, including fixed scalar signals.
        std::vector<bool> seen(aps.size());
        bool valid = true;
        bool identity = true;
        for (Id i = 0; i < permutation.size(); ++i) {
          Id to = permutation[i];
          valid &= !seen[to] && (i < c->n_inputs) == (to < c->n_inputs);
          identity &= to == i;
          seen[to] = true;
        }
        if (!valid) {
          range.reason = "index map is not a partition-preserving permutation";
          adjacent = false;
          continue; // An invalid AP map is not a candidate.
        }
        bool verified =
            !identity && !result->reason && dag.invariant(root, permutation);
        TlsfSymmetryCandidate candidate{};
        candidate.kind =
            rotate ? TLSF_SYMMETRY_ROTATION : TLSF_SYMMETRY_ADJACENT;
        candidate.generator = SIZE_MAX;
        if (verified) {
          candidate.generator = result->generator_views.size();
          result->permutations.push_back(std::move(permutation));
          result->generator_views.push_back(
              {result->range_views.size(), candidate.kind,
               result->permutations.back().data()});
        } else {
          candidate.reason = result->reason ? result->reason
                             : identity     ? "identity AP permutation"
                                            : "canonical forms differ";
        }
        storage.images.push_back(std::move(image));
        candidate.image = storage.images.back().data();
        storage.candidates.push_back(candidate);
        if (rotate)
          rotation = verified;
        else
          adjacent &= verified;
      }
    range.candidates = storage.candidates.data();
    range.n_candidates = storage.candidates.size();
    range.verdict = adjacent   ? TLSF_SYMMETRY_SYMMETRIC
                    : rotation ? TLSF_SYMMETRY_CYCLIC
                               : TLSF_SYMMETRY_NONE;
    result->range_views.push_back(range);
  }
  result->ranges = result->range_views.data();
  result->n_ranges = result->range_views.size();
  result->generators = result->generator_views.data();
  result->n_generators = result->generator_views.size();
  *out = result.release();
  return TLSF_SYMMETRY_OK;
}
} // namespace

TlsfSymmetryStatus tlsf_symmetry_detect(const TlsfConversionResult *conversion,
                                        TlsfSymmetryResult **result) {
  if (!result)
    return TLSF_SYMMETRY_INVALID;
  *result = nullptr;
  try {
    return detect(conversion, result);
  } catch (const std::bad_alloc &) {
    return TLSF_SYMMETRY_NO_MEMORY;
  } catch (...) {
    return TLSF_SYMMETRY_ERROR;
  }
}

void tlsf_symmetry_result_free(TlsfSymmetryResult *result) {
  delete static_cast<Result *>(result);
}
