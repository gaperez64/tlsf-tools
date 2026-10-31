# Stage 2 admission inventory

The API admits **45/69 objectives by default** and **69/69 with `allow_unproved`**. This runs `dpa_admission` on the inventory TLSF sources through the existing conversion API, without successor expansion. All 24 default declines return `TLSF_DPA_UNSUPPORTED`.

The default admission predicate is unchanged by `ea89484`'s syntactic X
protection, but default automata and budget outcomes can differ. The
[extractor audit](DEFAULT-PROTECTION.md) explains why the default Lean theorems
use that syntactic protection too and records the paired default-suite checks.
Those checks are separate from this historical admission-only inventory.

The stored Owl component-tree catalogue below counts 46/69. The difference is `amba_case_study_unreal_pb_3_pe_.ltl`: the converted AST retains one `G(s ∧ q)` whose safety conjunct contains W, whereas the stored trees distribute G over its conjunction. The API performs NNF and Boolean X distribution only, as specified in STAGE2-PROOF §8; it declines that combined G component. This is a syntax/transport difference, not a language disagreement.

Raw per-objective results were kept with the sprint's working files, not in this repository. The following table lists every default decline; `b` denotes a finite window.

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

This catalogue was moved from the proof. Its counts concern the stored normalized trees, not the API admission results above.

The inspected inventory is
the sprint's fragment inventory of the 69 SYNTCOMP 2026 inputs that only SemML decides (not in this repository).
Classification below uses the exact `product_proved_fragment` component trees,
not just their abbreviated shape labels. For example:

```text
amba_case_study_unreal_pb_3_pe_.ltl, root/12/16:
  G(OR(NOT(p4),F(NOT(p4)),F(AND(NOT(p17),NOT(p18)))))
load_balancer_unreal2_pb_7_pe_.ltl, root/3/21:
  G(OR(NOT(p1),X(NOT(p2)),F(AND(p8,p9))))
load_balancer_unreal1_pb_4_10_pe_.ltl, root/3/8:
  G(OR(F(NOT(p1)),F(X(p5))))
chain-5-real.ltl, root/54:
  F(AND(G(NOT(p4)),G(NOT(p9)),G(NOT(p13)),G(NOT(p26))))
```

All three requested shapes are now proved, including their bounded-X instances:

| Exact-tree family (inventory label) | Inputs / 69 | Components | Result |
| --- | ---: | ---: | --- |
| `G((F(b) ∨ b))` | 31 | 313 | §6 |
| `F((G(b) ∧ ...))` | 28 | 199 | §6, dual |
| `G((F(b) ∨ ...))` | 14 | 67 | §6 |
| `F((G(b) ∧ b))` | 7 | 8 | §6, dual |

The maximum X depths in these four groups are respectively 1, 0, 1, 0; the
theorem permits any finite depth. Counts overlap across inputs. With the
existing Stage 1 components and Boolean product, the extended grammar covers
46/69 complete objectives (32/43 FULL), leaving 23 (11 FULL) outside. This is
a syntax check on the stored trees, not an automata-equivalence test or a build.

The remaining inventory blockers are `F((X((b R b))∧b))` (9 inputs),
`b U (F(b)∧G(b)∧b)` (8), `G(((F(b)∧...)∨G(b)))` (3), and
`G((F(b)∨G(b)))` (3). Their R/U operators or inner G atoms lie outside the
flat co-safety body proved here. They and the general Π₂ converse remain
unproved; this document makes no disagreement claim or counterexample for those
other shapes.
No requested shape remains unproved, so there is no candidate counterexample
within the requested family. In particular `G(a → F(Xb ∧ XXc))`, previously
excluded here, is covered after NNF: its eventuality body is finite-window.


The inspected reference is SemML revision
`20ad6ec7916d204b45106d224bf1c761c337eae8`, in its vendored Owl sources:
(paths relative to `src/main/java/owl`) `ltl/SyntacticFragments.java:42–95,162–255`
(tests/classification), `translations/canonical/DeterministicConstructions.java:655–779`
(initialization, stepping, extraction), `translations/ltl2dela/NormalformDELAConstruction.java:175–208,851–864`
(components/global skeleton), and
`automaton/acceptance/transformer/ZielonkaTreeTransformations.java:772–843`
(maximal-model tree). Its path routine at `:314–385` has additional processing;
the ordinary update proved here is the exact DESIGN.md §2 variant. These are
algorithm references, not proofs of the general component theorem. Support-based
blocking [#81](https://github.com/gaperez64/tlsf-tools/issues/81), DELA
suspension/round robin [#82](https://github.com/gaperez64/tlsf-tools/issues/82),
and stuttering/local-tree resets [#83](https://github.com/gaperez64/tlsf-tools/issues/83)
remain unused and outside this document.

