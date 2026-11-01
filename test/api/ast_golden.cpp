#include "tlsf/ast_api.hpp"

#include <fstream>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string>

class StringVisitor : public tlsf::ast::Visitor<std::string> {
protected:
  std::string visitTrue() override { return "true"; }
  std::string visitFalse() override { return "false"; }
  std::string visitAp(const std::string &name) override { return name; }
  std::string visitNot(std::string arg) override { return "!(" + arg + ")"; }
  std::string visitX(std::string arg) override { return "X(" + arg + ")"; }
  std::string visitStrongX(std::string arg) override {
    return "X[!](" + arg + ")";
  }
  std::string visitF(std::string arg) override { return "F(" + arg + ")"; }
  std::string visitG(std::string arg) override { return "G(" + arg + ")"; }
  std::string visitAnd(std::string lhs, std::string rhs) override {
    return "(" + lhs + " && " + rhs + ")";
  }
  std::string visitOr(std::string lhs, std::string rhs) override {
    return "(" + lhs + " || " + rhs + ")";
  }
  std::string visitImplies(std::string lhs, std::string rhs) override {
    return "(" + lhs + " -> " + rhs + ")";
  }
  std::string visitEquiv(std::string lhs, std::string rhs) override {
    return "(" + lhs + " <-> " + rhs + ")";
  }
  std::string visitU(std::string lhs, std::string rhs) override {
    return "(" + lhs + " U " + rhs + ")";
  }
  std::string visitR(std::string lhs, std::string rhs) override {
    return "(" + lhs + " R " + rhs + ")";
  }
  std::string visitW(std::string lhs, std::string rhs) override {
    return "(" + lhs + " W " + rhs + ")";
  }
  std::string visitM(std::string lhs, std::string rhs) override {
    return "(" + lhs + " M " + rhs + ")";
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
    std::cerr << "usage: ast_golden FILE\n";
    return 2;
  }
  std::ifstream input(argv[1]);
  if (!input) {
    std::cerr << "ast_golden: cannot open " << argv[1] << '\n';
    return 2;
  }
  std::string text((std::istreambuf_iterator<char>(input)),
                   std::istreambuf_iterator<char>());

  try {
    tlsf::Options options;
    options.split = true;
    tlsf::ast::Ast ast(text, options);
    StringVisitor builder;
    tlsf::Result result = ast.result();

    std::string root = builder.visit(ast.root());
    std::cout << "formula: " << root << '\n';
    std::cout << "string: " << result.preprocessed_ltl << '\n';
    print_names("inputs", result.inputs);
    print_names("outputs", result.outputs);

    std::vector<tlsf::ast::Tree> clusters = ast.clusters();
    for (std::size_t i = 0; i < clusters.size(); ++i) {
      std::string formula = builder.visit(clusters[i]);
      std::cout << "cluster " << i << ": " << formula << '\n';
      std::cout << "string: " << result.clusters[i].ltl << '\n';
      print_names("  inputs", result.clusters[i].inputs);
      print_names("  outputs", result.clusters[i].outputs);
    }
  } catch (const std::exception &error) {
    std::cerr << "ast_golden: " << error.what() << '\n';
    return 1;
  }
  return 0;
}
