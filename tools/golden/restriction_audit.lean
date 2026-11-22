import TlsfProofs.Restriction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

set_option warningAsError true

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tlsf.Restriction.substAll_sat,
      ``Tlsf.Restriction.replay_decode_history, ``Tlsf.Restriction.play_input_decoder,
      ``Tlsf.Restriction.realizable_input_restriction,
      ``Tlsf.Restriction.unrealizable_input_restriction,
      ``Tlsf.Restriction.realizable_output_restriction,
      ``Tlsf.Restriction.input_decoder, ``Tlsf.Restriction.identify_boolean,
      ``Tlsf.Restriction.identify_ownership,
      ``Tlsf.Restriction.input_identification_decoder,
      ``Tlsf.Restriction.output_identification_decoder,
      ``Tlsf.Restriction.constants_boolean, ``Tlsf.Restriction.constants_ownership,
      ``Tlsf.Restriction.constant_input_decoder, ``Tlsf.Restriction.constant_output_decoder,
      ``Tlsf.Restriction.substAll_objective_sat,
      ``Tlsf.Restriction.objective_input_restriction,
      ``Tlsf.Restriction.objective_output_restriction,
      ``Tlsf.Restriction.input_identification_polarity,
      ``Tlsf.Restriction.output_constant_polarity] do
    let axioms ← liftCoreM (collectAxioms name)
    let unexpected := axioms.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwError "{name}: forbidden axioms {unexpected}"
    logInfo m!"{name}: permitted axioms {axioms}"
