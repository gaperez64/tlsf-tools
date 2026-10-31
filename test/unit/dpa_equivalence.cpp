#include "tlsf/dpa.h"
extern "C" {
#include "tlsf/ast.h"
}
#include <spot/parseaut/public.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/word.hh>
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
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

static Node *ground(Arena *a, spot::formula f) {
  using spot::op;
  switch (f.kind()) {
  case op::tt:
    return node_true(a);
  case op::ff:
    return node_false(a);
  case op::ap:
    return node_ap(a, f.ap_name().c_str());
  case op::Not:
    return node_not(a, ground(a, f[0]));
  case op::X:
    return node_x(a, ground(a, f[0]));
  case op::F:
    return node_f(a, ground(a, f[0]));
  case op::G:
    return node_g(a, ground(a, f[0]));
  case op::U:
    return node_u(a, ground(a, f[0]), ground(a, f[1]));
  case op::R:
    return node_r(a, ground(a, f[0]), ground(a, f[1]));
  case op::W:
    return node_w(a, ground(a, f[0]), ground(a, f[1]));
  case op::M:
    return node_m(a, ground(a, f[0]), ground(a, f[1]));
  case op::Implies:
    return node_impl(a, ground(a, f[0]), ground(a, f[1]));
  case op::Equiv:
    return node_equiv(a, ground(a, f[0]), ground(a, f[1]));
  case op::Xor:
    return node_not(a, node_equiv(a, ground(a, f[0]), ground(a, f[1])));
  case op::And:
  case op::Or: {
    Node *result = ground(a, f[0]);
    for (unsigned i = 1; i < f.size(); ++i)
      result = f.is(op::And) ? node_and(a, result, ground(a, f[i]))
                             : node_or(a, result, ground(a, f[i]));
    return result;
  }
  default:
    abort();
  }
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
  auto parsed = spot::parse_infix_psl(text);
  CHECK(!parsed.format_errors(std::cerr));
  auto f = parsed.f;
  Arena *a = arena_new(4096);
  Node *root = ground(a, f);
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
  auto dict = spot::make_bdd_dict();
  auto aut = spot::automaton_stream_parser(serialized.c_str(), "generated")
                 .parse(dict);
  CHECK(aut && !aut->format_errors(std::cerr) && aut->aut);
  CHECK(aut->aut->ap().size() == names.size());
  for (uint32_t i = 0; i < names.size(); ++i)
    CHECK(aut->aut->ap()[i].ap_name() == names[i]);
  auto outputs = aut->aut->get_named_prop<bdd>("synthesis-outputs");
  CHECK(outputs);
  bdd expected_outputs = bddtrue;
  for (uint32_t i = n_inputs; i < names.size(); ++i)
    expected_outputs &= bdd_ithvar(dict->varnum(spot::formula::ap(names[i])));
  CHECK(*outputs == expected_outputs);
  // Clear the HOA's asserted properties before independently checking them.
  aut->aut->prop_universal(spot::trival::maybe());
  aut->aut->prop_complete(spot::trival::maybe());
  CHECK(spot::is_deterministic(aut->aut) && spot::is_complete(aut->aut));
  spot::translator translate(dict);
  auto reference = translate.run(f);
  if (!spot::are_equivalent(aut->aut, reference)) {
    std::ofstream("dpa-mismatch.hoa") << serialized;
    std::ofstream("dpa-mismatch.ltl") << text << '\n';
    auto witness = aut->aut->exclusive_word(reference);
    if (witness)
      std::cerr << *witness << '\n';
    std::cerr << "language mismatch: " << text << '\n';
    abort();
  }
  std::cout << "equivalent: " << text << " (" << tlsf_dpa_state_count(c)
            << " states)\n";
  tlsf_dpa_free(c);
}

int main(int argc, char **argv) {
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
