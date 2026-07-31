#include "tlsf/ast_api.hpp"

#include <spot/tl/formula.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/contains.hh>

#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string>

class SpotBuilder : public tlsf::ast::Visitor<spot::formula> {
protected:
  spot::formula visitTrue() override { return spot::formula::tt(); }
  spot::formula visitFalse() override { return spot::formula::ff(); }
  spot::formula visitAp(const std::string &name) override {
    return spot::formula::ap(name);
  }
  spot::formula visitNot(spot::formula arg) override {
    return spot::formula::Not(std::move(arg));
  }
  spot::formula visitX(spot::formula arg) override {
    return spot::formula::X(std::move(arg));
  }
  spot::formula visitStrongX(spot::formula arg) override {
    return spot::formula::strong_X(std::move(arg));
  }
  spot::formula visitF(spot::formula arg) override {
    return spot::formula::F(std::move(arg));
  }
  spot::formula visitG(spot::formula arg) override {
    return spot::formula::G(std::move(arg));
  }
  spot::formula visitAnd(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::And({std::move(lhs), std::move(rhs)});
  }
  spot::formula visitOr(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::Or({std::move(lhs), std::move(rhs)});
  }
  spot::formula visitImplies(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::Implies(std::move(lhs), std::move(rhs));
  }
  spot::formula visitEquiv(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::Equiv(std::move(lhs), std::move(rhs));
  }
  spot::formula visitU(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::U(std::move(lhs), std::move(rhs));
  }
  spot::formula visitR(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::R(std::move(lhs), std::move(rhs));
  }
  spot::formula visitW(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::W(std::move(lhs), std::move(rhs));
  }
  spot::formula visitM(spot::formula lhs, spot::formula rhs) override {
    return spot::formula::M(std::move(lhs), std::move(rhs));
  }
};

static void print_names(const char *label,
                        const std::vector<std::string> &names) {
  std::cout << label << ":";
  for (const std::string &name : names)
    std::cout << ' ' << name;
  std::cout << '\n';
}

int main(int argc, char **argv) {
  if (argc != 2) {
    std::cerr << "usage: tlsf2spot FILE\n";
    return 2;
  }
  std::ifstream input(argv[1]);
  if (!input) {
    std::cerr << "tlsf2spot: cannot open " << argv[1] << '\n';
    return 2;
  }
  std::string text((std::istreambuf_iterator<char>(input)),
                   std::istreambuf_iterator<char>());

  try {
    tlsf::Options options;
    options.split = true;
    tlsf::ast::Ast ast(text, options);
    SpotBuilder builder;
    tlsf::Result result = ast.result();

    spot::formula root = builder.visit(ast.root());
    if (!spot::are_equivalent(root,
                              spot::parse_formula(result.preprocessed_ltl))) {
      std::cerr << "tlsf2spot: root differs from the string API\n";
      return 1;
    }
    std::cout << "formula: " << spot::str_psl(root) << '\n';
    print_names("inputs", result.inputs);
    print_names("outputs", result.outputs);

    std::vector<tlsf::ast::Tree> clusters = ast.clusters();
    for (std::size_t i = 0; i < clusters.size(); ++i) {
      spot::formula formula = builder.visit(clusters[i]);
      if (!spot::are_equivalent(formula,
                                spot::parse_formula(result.clusters[i].ltl))) {
        std::cerr << "tlsf2spot: cluster " << i
                  << " differs from the string API\n";
        return 1;
      }
      std::cout << "cluster " << i << ": " << spot::str_psl(formula) << '\n';
      print_names("  inputs", result.clusters[i].inputs);
      print_names("  outputs", result.clusters[i].outputs);
    }
  } catch (const std::exception &error) {
    std::cerr << "tlsf2spot: " << error.what() << '\n';
    return 1;
  }
  return 0;
}
