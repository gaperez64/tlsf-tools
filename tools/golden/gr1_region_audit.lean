import TlsfProofs.Gr1.Examples
import Lean.Elab.Command
import Lean.Util.CollectAxioms

set_option warningAsError true

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tlsf.Gr1.region_conditions_sound, ``Tlsf.Gr1.strategy_invariant,
      ``Tlsf.Gr1.Examples.alternating_conditions, ``Tlsf.Gr1.Examples.alternating_wins,
      ``Tlsf.Gr1.Examples.sampled_conditions, ``Tlsf.Gr1.Examples.sampled_wins,
      ``Tlsf.Gr1.Examples.ranked_conditions, ``Tlsf.Gr1.Examples.ranked_wins] do
    let axioms ← liftCoreM (collectAxioms name)
    let unexpected := axioms.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "{name}: forbidden axioms {unexpected}"
    logInfo m!"{name}: permitted axioms {axioms}"
