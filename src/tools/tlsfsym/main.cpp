#include "tlsf/convert.h"
#include "tlsf/version.h"
extern "C" {
#include "diagnostic.h"
}
#include <yyjson.h>

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <map>
#include <memory>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using Id = size_t;
using Clock = std::chrono::steady_clock;

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

// yyjson is already a library dependency; keep all escaping and serialization
// there. Fail rather than emitting an incomplete census on allocation failure.
template <class T> static T checked(T value) {
  if (!value)
    throw std::bad_alloc();
  return value;
}

struct Json {
  std::unique_ptr<yyjson_mut_doc, decltype(&yyjson_mut_doc_free)> doc{
      checked(yyjson_mut_doc_new(nullptr)), yyjson_mut_doc_free};

  yyjson_mut_val *object() { return checked(yyjson_mut_obj(doc.get())); }
  yyjson_mut_val *array() { return checked(yyjson_mut_arr(doc.get())); }
  void add(yyjson_mut_val *o, const char *key, yyjson_mut_val *v) {
    checked(yyjson_mut_obj_add_val(doc.get(), o, key, v));
  }
  void str(yyjson_mut_val *o, const char *key, const char *v) {
    add(o, key, checked(yyjson_mut_strcpy(doc.get(), v)));
  }
  void num(yyjson_mut_val *o, const char *key, size_t v) {
    add(o, key, checked(yyjson_mut_uint(doc.get(), v)));
  }
  void boolean(yyjson_mut_val *o, const char *key, bool v) {
    add(o, key, checked(yyjson_mut_bool(doc.get(), v)));
  }
  void push(yyjson_mut_val *a, yyjson_mut_val *v) {
    checked(yyjson_mut_arr_append(a, v));
  }
  yyjson_mut_val *names(char **items, uint32_t count) {
    auto *a = array();
    for (uint32_t i = 0; i < count; ++i)
      push(a, checked(yyjson_mut_strcpy(doc.get(), items[i])));
    return a;
  }
  void print(yyjson_mut_val *root, Clock::time_point start) {
    double seconds =
        std::chrono::duration<double>(Clock::now() - start).count();
    add(root, "wall_seconds", checked(yyjson_mut_real(doc.get(), seconds)));
    yyjson_mut_doc_set_root(doc.get(), root);
    size_t len;
    std::unique_ptr<char, decltype(&free)> text{
        checked(yyjson_mut_write(doc.get(), 0, &len)), free};
    if (fwrite(text.get(), 1, len, stdout) != len || putchar('\n') == EOF ||
        fflush(stdout) != 0)
      throw std::runtime_error("cannot write census");
  }
};

static int census(const std::string &text, Clock::time_point start) {
  // Keep the library's actual diagnostic for unresolved parameters, finite
  // semantics, etc. A failed conversion never produces a verified generator.
  char *diagnostic = nullptr;
  size_t diagnostic_size = 0;
  FILE *stream = checked(open_memstream(&diagnostic, &diagnostic_size));
  FILE *previous = tlsf_diagnostic_swap(stream);
  std::unique_ptr<TlsfConversionResult, decltype(&tlsf_conversion_result_free)>
      c{tlsf_convert(text.c_str(), "Mealy"), tlsf_conversion_result_free};
  tlsf_diagnostic_swap(previous);
  int closed = fclose(stream);
  std::unique_ptr<char, decltype(&free)> message{diagnostic, free};
  if (closed != 0)
    throw std::runtime_error("cannot capture conversion diagnostic");

  Json j;
  auto *result = j.object();
  j.str(
      result, "limitations",
      "The census is a lower bound: different concrete bounds are not coupled, "
      "families on the same range are only permuted together, enum families "
      "permute encoding bits, and canonical inequality is inconclusive.");
  auto *families = j.array();
  auto *ranges = j.array();
  j.add(result, "families", families);
  j.add(result, "ranges", ranges);
  if (!c) {
    j.str(result, "status", "unverified");
    j.str(result, "reason",
          diagnostic_size ? message.get() : "conversion failed");
    j.add(result, "summary", checked(yyjson_mut_null(j.doc.get())));
    j.print(result, start);
    return 1;
  }
  j.str(result, "semantics", c->semantics);
  j.str(result, "original_target", c->original_target);
  j.str(result, "effective_target", c->effective_target);
  j.add(result, "inputs", j.names(c->inputs, c->n_inputs));
  j.add(result, "outputs", j.names(c->outputs, c->n_outputs));

  std::unordered_map<std::string, Id> aps;
  auto add_aps = [&](char **names, uint32_t count) {
    for (uint32_t i = 0; i < count; ++i)
      if (!aps.emplace(names[i], aps.size()).second)
        throw std::runtime_error("duplicate AP in partition");
  };
  add_aps(c->inputs, c->n_inputs);
  add_aps(c->outputs, c->n_outputs);

  std::map<std::pair<uint16_t, uint16_t>, std::vector<uint32_t>> groups;
  for (uint32_t i = 0; i < c->n_indexed_families; ++i) {
    const auto &f = c->indexed_families[i];
    auto *family = j.object();
    j.str(family, "origin_name", f.origin_name);
    j.add(family, "members", j.names(f.members, f.n_members));
    j.num(family, "lo", f.lo);
    j.num(family, "hi", f.hi);
    j.num(family, "size", f.n_members);
    j.boolean(family, "is_output", f.is_output);
    j.boolean(family, "is_enum", f.is_enum);
    j.push(families, family);
    groups[{f.lo, f.hi}].push_back(i);
  }

  Dag dag;
  Id root = 0;
  std::string reason;
  try {
    root = dag.from_ast(tlsf_ast_root(c->ast), aps);
  } catch (const std::runtime_error &e) {
    reason = e.what();
  }
  j.str(result, "status", reason.empty() ? "ok" : "unverified");
  if (!reason.empty())
    j.str(result, "reason", reason.c_str());

  auto *sizes = j.array();
  for (const auto &[bounds, indices] : groups) {
    const auto [lo, hi] = bounds;
    size_t size = static_cast<size_t>(hi) - lo + 1;
    auto *range = j.object();
    auto *candidates = j.array();
    auto *family_ids = j.array();
    j.num(range, "lo", lo);
    j.num(range, "hi", hi);
    j.num(range, "size", size);
    j.num(range, "n_families", indices.size());
    j.add(range, "families", family_ids);
    j.add(range, "candidates", candidates);
    j.push(ranges, range);
    j.push(sizes, checked(yyjson_mut_uint(j.doc.get(), size)));

    std::vector<std::vector<Id>> members;
    std::string range_reason;
    for (uint32_t index : indices) {
      j.push(family_ids, checked(yyjson_mut_uint(j.doc.get(), index)));
      const auto &f = c->indexed_families[index];
      members.emplace_back();
      if (f.n_members != size)
        range_reason = "unresolved indexed family";
      for (uint32_t k = 0; k < f.n_members; ++k) {
        auto it = aps.find(f.members[k]);
        if (it == aps.end() || (it->second >= c->n_inputs) != f.is_output)
          range_reason = "family does not preserve the input/output partition";
        else
          members.back().push_back(it->second);
      }
    }
    bool adjacent = reason.empty() && range_reason.empty();
    bool rotation = false;
    // A singleton has an identity rotation and no adjacent transpositions.
    if (range_reason.empty())
      for (size_t k = 0; k < size; ++k) {
        bool rotate = k == size - 1;
        std::vector<Id> permutation(aps.size());
        std::iota(permutation.begin(), permutation.end(), 0);
        auto *image = j.array();
        for (size_t i = 0; i < size; ++i) {
          size_t to = rotate       ? (i + 1) % size
                      : i == k     ? k + 1
                      : i == k + 1 ? k
                                   : i;
          j.push(image, checked(yyjson_mut_uint(j.doc.get(), lo + to)));
          for (const auto &family : members)
            permutation[family[i]] = family[to];
        }
        // Check the complete AP permutation, including fixed scalar signals.
        std::vector<bool> seen(aps.size());
        bool valid = true;
        for (Id i = 0; i < permutation.size(); ++i) {
          Id to = permutation[i];
          valid &= !seen[to] && (i < c->n_inputs) == (to < c->n_inputs);
          seen[to] = true;
        }
        if (!valid) {
          range_reason = "index map is not a partition-preserving permutation";
          adjacent = false;
          continue; // An invalid AP map is not a candidate.
        }
        bool verified = reason.empty() && dag.invariant(root, permutation);
        auto *candidate = j.object();
        j.str(candidate, "kind", rotate ? "rotation" : "adjacent");
        j.add(candidate, "image", image); // Position i is the image of lo+i.
        j.boolean(candidate, "verified", verified);
        if (!verified)
          j.str(candidate, "reason",
                reason.empty() ? "canonical forms differ" : reason.c_str());
        j.push(candidates, candidate);
        if (rotate)
          rotation = verified;
        else
          adjacent &= verified;
      }
    if (!range_reason.empty())
      j.str(range, "reason", range_reason.c_str());
    j.str(range, "verified_group",
          adjacent   ? "symmetric"
          : rotation ? "cyclic"
                     : "none");
  }
  auto *summary = j.object();
  j.num(summary, "n_families", c->n_indexed_families);
  j.num(summary, "n_ranges", groups.size());
  j.add(summary, "range_sizes", sizes);
  j.add(result, "summary", summary);
  j.print(result, start);
  return 0;
}

int main(int argc, char **argv) {
  auto start = Clock::now();
  if (argc == 2 && std::string(argv[1]) == "--version") {
    printf("tlsfsym %s\n", TLSF_PROJECT_VERSION);
    return 0;
  }
  if (argc != 2 || std::string(argv[1]) == "--help") {
    fputs("Usage: tlsfsym FILE\n"
          "Census of declared index permutations of the native Mealy "
          "objective.\n",
          argc == 2 ? stdout : stderr);
    return argc == 2 ? 0 : 1;
  }
  try {
    std::ifstream input(argv[1]);
    if (!input)
      throw std::runtime_error("cannot open input file");
    std::string text{std::istreambuf_iterator<char>(input), {}};
    if (input.bad())
      throw std::runtime_error("cannot read input file");
    return census(text, start);
  } catch (const std::exception &e) {
    fprintf(stderr, "tlsfsym: %s\n", e.what());
    return 1;
  }
}
