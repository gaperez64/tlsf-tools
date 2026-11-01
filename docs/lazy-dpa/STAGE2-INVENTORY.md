# Stage 2 admission inventory

Historical `dpa_admission` accepted 45/69 default and 69/69 `allow_unproved`
objectives through the conversion API, without successor expansion. All 24
default declines were `TLSF_DPA_UNSUPPORTED`. Raw results/list are absent; these
are not fresh runs ([scope](DEFAULT-PROTECTION.md#inventory-limits-and-reproduction)).
Syntactic protection at `ea89484` preserves admission, but may change automata/budgets.
Stored Owl trees cover 46/69: `amba_case_study_unreal_pb_3_pe_.ltl` distributes G,
where API NNF/Boolean-X-only transport retains `G(s ∧ q)` with W in s/F in q
and declines it ([grammar](STAGE2-PROOF.md#admitted-grammar)). This is a syntax
difference, without a language-disagreement claim. All declines follow; b is finite:

| Objective | Blocking component |
| --- | --- |
| `amba_case_study_unreal_pb_3_pe_.ltl` | `G(s ∧ q)` with W in s and F in q (merged outer G) |
| `collector_v1_pb_11_pe_.ltl` | `G(F b ∨ G b ∨ …)` (also conjoined safety inside the outer G) |
| `collector_v1_pb_12_pe_.ltl` | `G(F b ∨ G b ∨ …)` (also conjoined safety inside the outer G) |
| `collector_v1_pb_13_pe_.ltl` | `G(F b ∨ G b ∨ …)` (also conjoined safety inside the outer G) |
| `collector_v3_pb_11_pe_.ltl` | `G(G b ∨ (F b ∧ …))` (also conjoined safety inside the outer G) |
| `collector_v3_pb_12_pe_.ltl` | `G(G b ∨ (F b ∧ …))` (also conjoined safety inside the outer G) |
| `collector_v3_pb_13_pe_.ltl` | `G(G b ∨ (F b ∧ …))` (also conjoined safety inside the outer G) |
| `load_balancer_unreal1_pb_4_10_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal1_pb_4_11_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal1_pb_4_12_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal1_pb_4_9_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal1_pb_5_6_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal1_pb_5_7_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal1_pb_6_5_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal2_pb_7_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `load_balancer_unreal2_pb_8_pe_.ltl` | `F(X grant_0 ∧ X((idle ∨ request_0) R (¬idle ∨ request_0)))` |
| `robot-to-target-charging-unreal1.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal2.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal3.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal4.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal5.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal6.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal7.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |
| `robot-to-target-charging-unreal8.ltl` | `(bin_st_0 ∨ ¬bin_st_1) U (bin_st_1 ∧ ¬bin_st_0 ∧ G b ∧ G b ∧ F ¬bin_cdist0)` |

## Stored-tree catalogue

Counts use exact `product_proved_fragment` trees of the external 69-input
SYNTCOMP 2026 SemML-only inventory; abbreviated labels are insufficient:

| Objective / tree path | Exact component |
|---|---|
| `amba_case_study_unreal_pb_3_pe_.ltl`, `root/12/16` | `G(OR(NOT(p4),F(NOT(p4)),F(AND(NOT(p17),NOT(p18)))))` |
| `load_balancer_unreal2_pb_7_pe_.ltl`, `root/3/21` | `G(OR(NOT(p1),X(NOT(p2)),F(AND(p8,p9))))` |
| `load_balancer_unreal1_pb_4_10_pe_.ltl`, `root/3/8` | `G(OR(F(NOT(p1)),F(X(p5))))` |
| `chain-5-real.ltl`, `root/54` | `F(AND(G(NOT(p4)),G(NOT(p9)),G(NOT(p13)),G(NOT(p26))))` |

The [flat converse](STAGE2-PROOF.md#flat-converse) proves all four families:

| Exact-tree family (inventory label) | Inputs / 69 | Components | Result |
| --- | ---: | ---: | --- |
| `G((F(b) ∨ b))` | 31 | 313 | flat converse |
| `F((G(b) ∧ ...))` | 28 | 199 | flat converse, dual |
| `G((F(b) ∨ ...))` | 14 | 67 | flat converse |
| `F((G(b) ∧ b))` | 7 | 8 | flat converse, dual |

X depths are 1, 0, 1, 0; any finite depth is proved. Counts overlap. Together
with Stage 1/product, coverage is 46/69 (32/43 FULL), leaving 23 (11 FULL).
This is syntax classification, not equivalence or a build.

Remaining flat-grammar blockers are `F((X((b R b))∧b))` (9 inputs),
`b U (F(b)∧G(b)∧b)` (8), `G(((F(b)∧...)∨G(b)))` (3), and
`G((F(b)∨G(b)))` (3). R/U or inner G exceeds the flat body proved here;
no counterexample/disagreement is claimed for them. The later general Π₂ proof
and validation are documented in [proofs/README.md](../../proofs/README.md#automaton-translation-validation).
`G(a → F(Xb ∧ XXc))` is already in the flat grammar after NNF because its
eventuality body is finite-window.

The inspected SemML revision was `20ad6ec7916d204b45106d224bf1c761c337eae8`.
Owl paths relative to `src/main/java/owl` are
`ltl/SyntacticFragments.java:42–95,162–255` (classification),
`translations/canonical/DeterministicConstructions.java:655–779` (component),
`translations/ltl2dela/NormalformDELAConstruction.java:175–208,851–864` (skeleton),
and `automaton/acceptance/transformer/ZielonkaTreeTransformations.java:772–843`
(maximal models). Its `:314–385` path has extra processing; this proof uses
[the ordinary design update](DESIGN.md#c-implementation-and-contract).
These are algorithm references, not component proofs. Support blocking
[#81](https://github.com/gaperez64/tlsf-tools/issues/81), suspension/round robin
[#82](https://github.com/gaperez64/tlsf-tools/issues/82), and stuttering/tree resets
[#83](https://github.com/gaperez64/tlsf-tools/issues/83) remain unused/outside scope.
