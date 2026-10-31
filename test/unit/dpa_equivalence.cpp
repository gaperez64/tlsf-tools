#include "tlsf/dpa.h"
extern "C" {
#include "tlsf/ast.h"
#include "tlsf/intern.h"
}
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <algorithm>
#include <utility>
#include <sstream>
#include <vector>

// Keep the gate active in release builds too.
#define CHECK(condition)                                                       \
  do {                                                                         \
    if (!(condition)) {                                                        \
      std::cerr << __FILE__ << ':' << __LINE__ << ": " << #condition << '\n';  \
      std::abort();                                                            \
    }                                                                          \
  } while (0)

struct Reference {
  std::string tree, membership;
};
static std::map<std::string, Reference> references;
static std::vector<std::pair<std::vector<unsigned>, std::vector<unsigned>>>
    words;

static Node *ground(Arena *a, InternTable *atoms, std::istream &in) {
  std::string token;
  CHECK(bool(in >> token));
  if (token == "1")
    return node_true(a);
  if (token == "0")
    return node_false(a);
  if (token.starts_with('$'))
    return node_ap(a, intern(atoms, token.c_str() + 1));
  Node *left = ground(a, atoms, in);
  if (token == "!")
    return node_not(a, left);
  if (token == "X")
    return node_x(a, left);
  if (token == "F")
    return node_f(a, left);
  if (token == "G")
    return node_g(a, left);
  Node *right = ground(a, atoms, in);
  if (token == "&")
    return node_and(a, left, right);
  if (token == "|")
    return node_or(a, left, right);
  if (token == "i")
    return node_impl(a, left, right);
  if (token == "e")
    return node_equiv(a, left, right);
  if (token == "^")
    return node_not(a, node_equiv(a, left, right));
  if (token == "U")
    return node_u(a, left, right);
  if (token == "R")
    return node_r(a, left, right);
  if (token == "W")
    return node_w(a, left, right);
  if (token == "M")
    return node_m(a, left, right);
  CHECK(false);
  return nullptr;
}

static void load_goldens() {
  std::ifstream data(std::string(DPA_GOLDEN_DIR) + "/membership.tsv");
  CHECK(data);
  std::string line;
  while (std::getline(data, line)) {
    auto first = line.find('\t'), second = line.find('\t', first + 1);
    CHECK(first != std::string::npos && second != std::string::npos);
    CHECK(references
              .emplace(line.substr(0, first),
                       Reference{line.substr(first + 1, second - first - 1),
                                 line.substr(second + 1)})
              .second);
  }
  std::ifstream samples(std::string(DPA_GOLDEN_DIR) + "/words.txt");
  CHECK(samples);
  while (std::getline(samples, line)) {
    auto separator = line.find(';');
    CHECK(separator != std::string::npos);
    auto masks = [](const std::string &text) {
      std::istringstream in(text);
      std::vector<unsigned> values;
      unsigned value;
      while (in >> value)
        values.push_back(value);
      return values;
    };
    words.emplace_back(masks(line.substr(0, separator)),
                       masks(line.substr(separator + 1)));
    CHECK(!words.back().second.empty());
  }
  CHECK(words.size() == 512 && !references.empty());
}

static bool holds(TlsfDpa *dpa, uint32_t id, unsigned letter) {
  const auto *node = tlsf_dpa_label_node(dpa, id);
  CHECK(node);
  if (node->kind != TLSF_DPA_DECISION)
    return node->kind == TLSF_DPA_TRUE;
  CHECK(node->ap < 7);
  return holds(dpa, letter & (1u << node->ap) ? node->high : node->low, letter);
}

static TlsfDpaEdge step(TlsfDpa *dpa, uint32_t state, unsigned letter) {
  const TlsfDpaEdge *edges;
  size_t count;
  CHECK(tlsf_dpa_successors(dpa, state, &edges, &count).code == TLSF_DPA_OK);
  TlsfDpaEdge result{};
  unsigned matches = 0;
  for (size_t i = 0; i < count; ++i)
    if (holds(dpa, edges[i].label, letter)) {
      result = edges[i];
      ++matches;
    }
  CHECK(matches == 1); // independent completeness and determinism check
  return result;
}

static bool accepts(TlsfDpa *dpa, const std::vector<unsigned> &prefix,
                    const std::vector<unsigned> &loop) {
  uint32_t state = tlsf_dpa_initial(dpa);
  for (auto letter : prefix)
    state = step(dpa, state, letter).successor;
  std::map<std::pair<uint32_t, size_t>, size_t> seen;
  std::vector<uint32_t> priorities;
  size_t position = 0;
  while (!seen.count({state, position})) {
    seen[{state, position}] = priorities.size();
    auto edge = step(dpa, state, loop[position]);
    priorities.push_back(edge.priority);
    state = edge.successor;
    position = (position + 1) % loop.size();
  }
  auto first = priorities.begin() +
               static_cast<std::ptrdiff_t>(seen.at({state, position}));
  return *std::max_element(first, priorities.end()) % 2 == 1;
}

static std::string label(TlsfDpa *c, uint32_t id,
                         std::map<uint32_t, std::string> &memo) {
  if (memo.count(id))
    return memo.at(id);
  const auto *n = tlsf_dpa_label_node(c, id);
  CHECK(n);
  std::string result;
  if (n->kind != TLSF_DPA_DECISION)
    result = n->kind == TLSF_DPA_TRUE ? "t" : "f";
  else
    result = "((" + std::to_string(n->ap) + " & " + label(c, n->high, memo) +
             ") | (!" + std::to_string(n->ap) + " & " + label(c, n->low, memo) +
             "))";
  return memo[id] = result;
}

// Deliberately test-only: production exports a label DAG, never serialized HOA.
static std::string hoa(TlsfDpa *c, uint32_t n_inputs) {
  std::ostringstream out;
  out << "HOA: v1\nStates: " << tlsf_dpa_state_count(c)
      << "\nStart: " << tlsf_dpa_initial(c) << "\nAP: " << tlsf_dpa_ap_count(c);
  for (uint32_t i = 0; i < tlsf_dpa_ap_count(c); ++i)
    out << " \"" << tlsf_dpa_ap_name(c, i) << "\"";
  out << "\ncontrollable-AP:";
  for (uint32_t i = n_inputs; i < tlsf_dpa_ap_count(c); ++i)
    out << ' ' << i;
  uint32_t priorities = tlsf_dpa_max_priority(c) + 1;
  out << "\nacc-name: parity max odd " << priorities
      << "\nAcceptance: " << priorities << ' ';
  for (uint32_t odd = 1; odd < priorities; odd += 2) {
    if (odd > 1)
      out << " | ";
    out << "(Inf(" << odd << ')';
    for (uint32_t higher = odd + 1; higher < priorities; ++higher)
      out << " & Fin(" << higher << ')';
    out << ')';
  }
  out << "\nproperties: trans-labels explicit-labels trans-acc deterministic "
         "complete\n--BODY--\n";
  std::map<uint32_t, std::string> memo;
  for (uint32_t i = 0; i < tlsf_dpa_state_count(c); ++i) {
    const TlsfDpaEdge *edges, *again;
    size_t n, m;
    auto status = tlsf_dpa_successors(c, i, &edges, &n);
    CHECK(status.code == TLSF_DPA_OK);
    status = tlsf_dpa_successors(c, i, &again, &m);
    CHECK(status.code == TLSF_DPA_OK);
    CHECK(again == edges && m == n && n);
    out << "State: " << i << '\n';
    for (size_t j = 0; j < n; ++j) {
      CHECK(edges[j].successor < tlsf_dpa_state_count(c));
      CHECK(edges[j].priority <= tlsf_dpa_max_priority(c));
      out << '[' << label(c, edges[j].label, memo) << "] " << edges[j].successor
          << " {" << edges[j].priority << "}\n";
    }
  }
  return out.str() + "--END--\n";
}

static void check(const std::string &text, bool allow_unproved = false,
                  bool expect_bdd_limit = false,
                  bool expect_unsupported = false) {
  Reference reference;
  if (expect_bdd_limit) {
    // TLSF parses the limits corpus through the in-house parser below.
    std::ifstream limits(std::string(DPA_GOLDEN_DIR) + "/limits.tsv");
    CHECK(limits);
    std::string line;
    while (std::getline(limits, line)) {
      auto tab = line.find('\t');
      if (line.substr(0, tab) == text)
        reference.tree = line.substr(tab + 1);
    }
    CHECK(!reference.tree.empty());
  } else {
    CHECK(references.count(text));
    reference = references.at(text);
  }
  Arena *a = arena_new(4096);
  std::istringstream tree(reference.tree);
  InternTable *atoms = intern_table_new(a);
  CHECK(atoms);
  Node *root = ground(a, atoms, tree);
  intern_table_free(atoms);
  std::string remaining;
  CHECK(!(tree >> remaining));
  // Inputs first, outputs second; retain unused declarations on both sides.
  constexpr std::array names = {"unused_in", "req",   "a", "unused_out",
                                "c",         "grant", "b"};
  constexpr uint32_t n_inputs = 3;
  TlsfDpa *c = nullptr;
  TlsfDpaBudget budget{};
  budget.allow_unproved = allow_unproved;
  budget.max_states = 10000;
  budget.max_host_bytes = 64u << 20;
  if (expect_bdd_limit) {
    budget.bdd_nodes = 1u << 12;
    budget.bdd_cache = 1u << 10;
  }
  auto status = tlsf_dpa_create(reinterpret_cast<const TlsfAstNode *>(root),
                                names.data(), n_inputs, names.data() + n_inputs,
                                names.size() - n_inputs, &budget, &c);
  arena_free(a); // construction must copy everything it needs
  if (expect_unsupported) {
    CHECK(status.code == TLSF_DPA_DECLINED &&
          status.reason == TLSF_DPA_UNSUPPORTED && !c);
    std::cout << "unsupported as expected: " << text << '\n';
    return;
  }
  if (status.code != TLSF_DPA_OK) {
    std::cerr << "declined " << text << " reason " << status.reason << '\n';
    tlsf_dpa_free(c);
    exit(status.code == TLSF_DPA_DECLINED ? 77 : 1);
  }
  CHECK(tlsf_dpa_ap_count(c) == names.size());
  for (uint32_t i = 0; i < names.size(); ++i)
    CHECK(std::string(tlsf_dpa_ap_name(c, i)) == names[i]);
  CHECK(tlsf_dpa_state_count(c) == 1); // no eager expansion in create
  status = tlsf_dpa_expand(c);
  if (expect_bdd_limit) {
    CHECK(status.code == TLSF_DPA_DECLINED &&
          status.reason == TLSF_DPA_BDD_LIMIT);
    CHECK(tlsf_dpa_expand(c).reason == TLSF_DPA_BDD_LIMIT);
    const TlsfDpaEdge *edges = reinterpret_cast<const TlsfDpaEdge *>(1);
    size_t count = 1;
    CHECK(tlsf_dpa_successors(c, 0, &edges, &count).reason ==
          TLSF_DPA_BDD_LIMIT);
    CHECK(!edges && !count);
    std::cout << "bounded expansion declined: " << text << '\n';
    tlsf_dpa_free(c);
    return;
  }
  if (status.code != TLSF_DPA_OK) {
    std::cerr << "expansion status " << status.code << " reason "
              << status.reason << " states " << tlsf_dpa_state_count(c) << ": "
              << text << '\n';
    tlsf_dpa_free(c);
    exit(status.code == TLSF_DPA_DECLINED ? 77 : 1);
  }
  std::string serialized = hoa(c, n_inputs);
  CHECK(serialized.find("controllable-AP: 3 4 5 6\n") != std::string::npos);
  CHECK(serialized.find("AP: 7 \"unused_in\" \"req\" \"a\" \"unused_out\" "
                        "\"c\" \"grant\" \"b\"\n") != std::string::npos);
  for (uint32_t state = 0; state < tlsf_dpa_state_count(c); ++state)
    for (unsigned letter = 0; letter < 128; ++letter)
      (void)step(c, state, letter);
  CHECK(reference.membership.size() == words.size());
  for (size_t i = 0; i < words.size(); ++i) {
    bool expected = reference.membership[i] == '1';
    bool actual = accepts(c, words[i].first, words[i].second);
    if (actual != expected) {
      std::ofstream("dpa-mismatch.hoa") << serialized;
      std::cerr << "language mismatch: " << text << " lasso " << i << '\n';
      std::abort();
    }
  }
  std::cout << "golden language: " << text << " (" << tlsf_dpa_state_count(c)
            << " states)\n";
  tlsf_dpa_free(c);
}

int main(int argc, char **argv) {
  load_goldens();
  bool research = argc == 2 && std::string(argv[1]) == "--allow-unproved";
  if (argc >= 2 && !research) {
    std::ifstream formulas(argv[1]);
    CHECK(formulas);
    std::string line;
    while (std::getline(formulas, line))
      if (!line.empty())
        check(line, argc >= 3 && std::string(argv[2]) == "--allow-unproved",
              argc == 4 && std::string(argv[3]) == "--expect-bdd-limit");
    return 0;
  }
  for (auto text : {"G(req -> X grant)", "F grant", "true", "false",
                    "G F (a & X b)", "F G (!a | X !b)", "!(G(req -> X grant))",
                    "!(F grant)", "G F (a & X X b)", "!(G F (a & X X b))",
                    "G F (X a & X X X b)", "!(G F (X a & X X X b))",
                    "G F (a & X !a)", "!(G F (a & X !a))", "G (a W (b R X c))",
                    "F (a M (b U X c))", "G ((a <-> X b) & (a -> X c))"})
    check(text, research);
  for (auto text : {
           "G F a & F G b",
           "G F a | F G b",
           "(G F a) <-> (F G b)",
           "!((G F a) <-> (F G b))",
           "(G F a & F G b) | (G F a & G F c)",
           "G F a | !(G F a)",
           "G F a & !(G F a)",
           "(G F a -> F G b) & (F G b -> G F a)",
       })
    check(text, research);
  for (auto text : {
           "G(a -> F b)",
           "!(G(a -> F b))",
           "G(F(a | (a & X X b)) | X X b)",
           "!(G(F(a | (a & X X b)) | X X b))",
           "G(F a | F (X b & X X c))",
           "F(G a & G (X b | X X c))",
           "G(a | F (b & X X c))",
           "F(a & G (b | X X c))",
           "G((a | F (X b)) & (F c | (X a & F (b | X X c))))",
           "F((a & G (X b)) | (G c & (X a | G (b & X X c))))",
           "!(G((a | F (X b)) & (F c | (X a & F (b | X X c)))))",
           "!(F((a & G (X b)) | (G c & (X a | G (b & X X c)))))",
           "G(a | F (b & X c)) <-> F(c & G (a | X b))",
       })
    check(text, research);
  for (auto text : {
           // Safety/co-safety siblings and finite initial conditions, both
           // Boolean operations, with a separate recurrence component.
           "G(a -> X b) & G(b -> X X c) & G F req",
           "F(a & X b) | F(b & X X c) | F G req",
           "!a & b & X c & F(a & X b) & F(!b | X X c) & G F req",
           "a | !b | X !c | G(!a | X !b) | G(b & X X !c) | F G req",
           "a & X b & G(a -> X c) & G F req",
           // Unsupported syntax absorbed by the original canonical support.
           "(a & G F b) | (a & G F b & X G F b)",
           // G over conjunction and its F/disjunction dual, also nested.
           "G((a -> X b) & (b -> F c) & (c -> F req))",
           "F((a & X !b) | (b & G !c) | (c & G !req))",
           "G(F((a & X b) | (c & X req)) & F grant)",
           // A terminal residual decides the entire product; complementary
           // acceptance literals must substitute with the right polarity.
           "G a & G F b",
           "F a | F G b",
           "G a | G F b",
           "F a & F G b",
           "(G a & G F b) | (F c & F G req)",
           // Current AP care reaches modal bodies but never crosses X.
           "a & F(!a & X b)",
           "a & X !a & F(!a & X b)",
           "a & X F !a",
           "a & ((a & X b) U (!a & X c))",
           "a & ((a & X b) M (!a & X c))",
           "a & ((a | X b) R (!a | X c))",
           "a & ((a | X b) W (!a | X c))",
           // Small chain shape: recurrence implications, a finite initial
           // cube, and several transition obligations under that cube.
           "(G F a -> G F (b | req)) & (G F b -> G F (a | c)) & "
           "((!a & !b & req) -> (G(a -> X b) & G(b -> X c) & G(req -> X a)))",
           // Small AMBA shape: fairness plus initial grants, a bundled G
           // of finite consistency, next-step stability and response clauses.
           "(req & G F req) -> (a & !b & G((a | b) & !(a & b) & "
           "(!req -> ((X a <-> a) & (X b <-> b))) & "
           "(c -> F(!c | a)) & (grant -> F(!grant | b))))",
           // Small SPI shape: many safety clauses beside recurrence.
           "G(a -> X b) & G(b -> X X c) & G(c -> X req) & "
           "G(req -> X grant) & G F !grant",
       }) {
    check(text, research);
    check("!(" + std::string(text) + ")", research);
  }
  for (auto text : {"(G F a & F G b) | (G F a & F G b & G F G F b)",
                    "!((G F a & F G b) | (G F a & F G b & G F G F b))"})
    check(text, true);
  // Canonical operand refinement remains in the default fragment. Research
  // admission must decline syntax outside HasTag Pi2 and its Sigma2 dual.
  for (auto text : {"X G(a | (a & F G b))", "G(F a | (F a & F(G b)))",
                    "!(G(F a | (F a & F(G b))))"})
    check(text, research, false, research);
  for (auto text : {
           "G(a -> F(b U c))",
           "G F(a U b)",
           "X ((G F a & F G b) | G F c)",
           "G (a -> F b)",
           "!(G (a -> F b))",
           "G (a U (b & X c))",
           "!(G (a U (b & X c)))",
           "(a U b) R (c U X a)",
           "!((a U b) R (c U X a))",
           "(a M b) W (c M X a)",
           "!((a M b) W (c M X a))",
           "G ((a & X F b) | F (c & X X a))",
           "!(G ((a & X F b) | F (c & X X a)))",
           "G ((X X a & F b) | X F c)",
           "!(G ((X X a & F b) | X F c))",
           "G (F (a & X b) & X X F (b & X c))",
           "!(G (F (a & X b) & X X F (b & X c)))",
           // Syntactic protection survives absorption inside the F operand.
           "G(F(a | (a & X F b)) | X F b)",
           "!(G(F(a | (a & X F b)) | X F b))",
           "G F (a & X X b) & F G (b | X c)",
           "((G F a & F G b) | (G F c & F G a)) <-> (G F b)",
       })
    check(text, true);
}
