import TlsfProofs.Dpa.Impl.Main

/-! Offline Task T dependency audit. From proofs/, run lake env lean with this
file inside the documented 5 GiB systemd scope. This is not registered in CI.
Every reported dependency set must be contained in
{propext, Classical.choice, Quot.sound}. -/
#print axioms Tlsf.Dpa.Impl.table_exact
#print axioms Tlsf.Dpa.Impl.equivalent_exact
#print axioms Tlsf.Dpa.Impl.uses_exact
#print axioms Tlsf.Dpa.Impl.hasTag_exact
#print axioms Tlsf.Dpa.Impl.syntaxTag_exact
#print axioms Tlsf.Dpa.Impl.classTag_exact
#print axioms Tlsf.Dpa.Impl.researchAdmitted_exact
#print axioms Tlsf.Dpa.Impl.protected_exact
#print axioms Tlsf.Dpa.Impl.reduce_exact
#print axioms Tlsf.Dpa.Impl.dropX_exact
#print axioms Tlsf.Dpa.Impl.elide_exact
#print axioms Tlsf.Dpa.Impl.extractPass_exact
#print axioms Tlsf.Dpa.Impl.rho_exact
#print axioms Tlsf.Dpa.Impl.initial_exact
#print axioms Tlsf.Dpa.Impl.transition_exact
#print axioms Tlsf.Dpa.Impl.run_exact
#print axioms Tlsf.Dpa.Impl.marks_exact
#print axioms Tlsf.Dpa.Impl.pi2_language
#print axioms Tlsf.Dpa.Impl.pi2_complement
#print axioms Tlsf.Dpa.Impl.pi2_parity
#print axioms Tlsf.Dpa.Impl.pi2_complement_parity
#print axioms Tlsf.Dpa.Impl.dual_class_congr
#print axioms Tlsf.Dpa.Impl.class_sigma2_dual_pi2
#print axioms Tlsf.Dpa.Impl.classTag_sigma2_dual_pi2
#print axioms Tlsf.Dpa.Impl.sigma2_language
#print axioms Tlsf.Dpa.Impl.sigma2_parity
#print axioms Tlsf.Dpa.Impl.research_component_language
#print axioms Tlsf.Dpa.Impl.canonicalResearchCheck_exact
#print axioms Tlsf.Dpa.Impl.canonicalResearchCheck_shannon
#print axioms Tlsf.Dpa.Impl.compatibleGroups_exact
#print axioms Tlsf.Dpa.Impl.compatibleGroups_language
#print axioms class_checks
#print axioms component_checks
#print axioms dual_admission_checks
