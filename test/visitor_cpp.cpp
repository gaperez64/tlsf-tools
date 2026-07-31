#include "tlsf/ast_api.hpp"

#include <cassert>
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

int main() {
  const std::string text = R"TLSF(
INFO { TITLE: "visitor_cpp" SEMANTICS: Mealy TARGET: Mealy }
MAIN {
  INPUTS { a; b; }
  OUTPUTS { x; y; }
  GUARANTEE { G (x <-> X a); F (y || (a U b)); }
}
)TLSF";
  tlsf::Options options;
  options.split = true;
  tlsf::ast::Ast ast(text, options);
  assert(ast.root());
  assert(ast.inputs().size() == 2);
  assert(ast.outputs().size() == 2);
  assert(ast.clusters().size() == ast.result().clusters.size());

  StringVisitor visitor;
  std::string built = visitor.visit(ast.root());
  assert(!built.empty());
  assert(built.find("x") != std::string::npos);
  assert(built.find("y") != std::string::npos);
  for (tlsf::ast::Tree cluster : ast.clusters())
    assert(!visitor.visit(cluster).empty());
  return 0;
}
