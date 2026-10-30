#pragma GCC diagnostic push
// The C AST ABI uses anonymous structs, accepted by the C++ compiler too.
#pragma GCC diagnostic ignored "-Wpedantic"
extern "C" {
#include "residual_sat.h"
}
#pragma GCC diagnostic pop

#if __has_include(<spot/twaalgos/ltl2tgba_fm.hh>)
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <chrono>
#include <stdexcept>

namespace {
using F = spot::formula;

// Bound syntax before invoking Spot, as well as the generated automaton.
F formula(const Node *n, unsigned &fuel) {
  if (!n || fuel == 0)
    throw std::runtime_error("pruning syntax budget");
  --fuel;
  switch (n->kind) {
  case NODE_TRUE:
    return F::tt();
  case NODE_FALSE:
    return F::ff();
  case NODE_AP:
    return F::ap(n->name);
  case NODE_NOT:
    return F::Not(formula(n->arg, fuel));
  case NODE_X:
  case NODE_X_STRONG:
    return F::X(formula(n->arg, fuel));
  case NODE_F:
    return F::F(formula(n->arg, fuel));
  case NODE_G:
    return F::G(formula(n->arg, fuel));
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    break;
  default:
    throw std::runtime_error("unsupported pruning formula");
  }
  // Sequence fuel updates explicitly (argument evaluation order is
  // unspecified).
  auto lhs = formula(n->lhs, fuel);
  auto rhs = formula(n->rhs, fuel);
  switch (n->kind) {
  case NODE_AND:
    return F::And({lhs, rhs});
  case NODE_OR:
    return F::Or({lhs, rhs});
  case NODE_IMPL:
    return F::Implies(lhs, rhs);
  case NODE_EQUIV:
    return F::Equiv(lhs, rhs);
  case NODE_U:
    return F::U(lhs, rhs);
  case NODE_R:
    return F::R(lhs, rhs);
  case NODE_W:
    return F::W(lhs, rhs);
  case NODE_M:
    return F::M(lhs, rhs);
  default:
    throw std::runtime_error("unsupported pruning formula");
  }
}
} // namespace
#endif

extern "C" bool residual_env_satisfiable(const SectionPatternView *dropped) {
#if __has_include(<spot/twaalgos/ltl2tgba_fm.hh>)
  try {
    const auto deadline =
        std::chrono::steady_clock::now() + std::chrono::milliseconds(50);
    unsigned fuel = 128;
    auto env = F::tt();
    for (uint32_t i = 0; i < dropped->count; ++i) {
      const auto &e = dropped->entries[i];
      auto f = formula(e.formula, fuel);
      switch (e.role) {
      case TLSF_ROLE_REQUIRE:
        f = F::G(f);
        break;
      case TLSF_ROLE_INITIALLY:
      case TLSF_ROLE_ASSUME:
        break;
      default:
        return false;
      }
      env = F::And({env, f});
    }
    const spot::output_aborter budget(256, 1024);
    auto aut =
        spot::ltl_to_tgba_fm(env, spot::make_bdd_dict(), false, true, false,
                             false, nullptr, nullptr, false, &budget);
    if (!aut || std::chrono::steady_clock::now() >= deadline)
      return false;
    const bool sat = !aut->is_empty();
    // Spot calls are synchronous; an overrun is discarded, never trusted.
    return sat && std::chrono::steady_clock::now() < deadline;
  } catch (...) {
    return false;
  }
#else
  (void)dropped;
  return false;
#endif
}
