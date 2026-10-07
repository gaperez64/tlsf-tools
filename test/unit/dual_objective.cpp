#include "gr1_dual.hh"
#include <spot/tl/parse.hh>
#include <cassert>

int main() {
  for (const char *text :
       {"1", "0", "G(o <-> i)", "(GF i) -> (GF o)", "(i & X o) | F(i & !o)"})
    for (bool moore : {false, true}) {
      tlsf::gr1::Objective source{spot::parse_formula(text),
                                  {"i", "unused_i"},
                                  {"o", "unused_o"},
                                  moore};
      auto other = tlsf::gr1::dual(source);
      assert(other.moore != source.moore);
      assert(other.inputs == source.outputs && other.outputs == source.inputs);
      auto again = tlsf::gr1::dual(other);
      assert(again.formula == source.formula);
      assert(again.inputs == source.inputs && again.outputs == source.outputs);
      assert(again.moore == source.moore);
    }
  const tlsf::gr1::Objective singleton{spot::formula::ap("o"), {"o"}, {}, true};
  assert(tlsf::gr1::input_first_formula(singleton) ==
         spot::formula::X(spot::formula::ap("o")));
  // Root APs, nested X and constants must also be transformed exactly once.
  auto nested = singleton;
  nested.formula = spot::parse_formula("X o");
  assert(tlsf::gr1::input_first_formula(nested) == spot::parse_formula("XX o"));
}
