#pragma once

#include <spot/tl/formula.hh>
#include <spot/tl/simplify.hh>
#include <algorithm>
#include <string>
#include <vector>

namespace tlsf::gr1 {
// This is an objective/game dual, before compiling either timing convention
// into an input-first monitor game. Applying it twice restores the game.
struct Objective {
  spot::formula formula;
  std::vector<std::string> inputs, outputs;
  bool moore;
};
inline Objective dual(const Objective &source) {
  return {spot::formula::Not(source.formula), source.outputs, source.inputs,
          !source.moore};
}
inline spot::formula input_first_formula(const Objective &game) {
  auto push = [&](auto &&self, spot::formula f) -> spot::formula {
    if (f.is(spot::op::ap) && std::find(game.inputs.begin(), game.inputs.end(),
                                        f.ap_name()) != game.inputs.end())
      return spot::formula::X(f);
    return f.map([&](spot::formula child) { return self(self, child); });
  };
  // Same input-push as Acacia's UNREAL_X_FORMULA route. In a Moore game
  // output[t] precedes input[t]; compiled input[t+1] supplies that response.
  // The unused input[0] is universal and conveys no source-game information.
  auto formula = game.moore ? push(push, game.formula) : game.formula;
  spot::tl_simplifier simplifier;
  return simplifier.negative_normal_form(formula);
}
} // namespace tlsf::gr1
