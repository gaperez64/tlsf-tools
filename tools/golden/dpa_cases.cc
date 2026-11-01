// Tools-only corpus enumerator. The reference oracle requires Spot 2.16.
#include <fstream>
#include <iostream>
#include <string>
#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x))                                                                  \
      return 2;                                                                \
  } while (0)
static void check(const std::string &text, bool = false, bool = false,
                  bool = false) {
  std::cout << text << '\n';
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
