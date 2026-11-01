# GR(1) environment certificates and counter-strategies

On GR(1) UNREAL, `tlsfsolve` can export an environment certificate
(`tlsf-gr1-certificate-v1`) and policy (`tlsf-gr1-policy-v1`), both with
`side: "environment"`. `tlsfcertcheck` independently checks them against the
supplied game. The [region method](gr1-region-method.md) covers system-side
certificates only.

Exporter code is `src/lib/gr1_oxidd.c`; checker code/API are
`src/lib/gr1_check.c` and `include/tlsf/gr1_check.h`, with ownership conventions
in `src/lib/oxidd_common.h`. Source locations below record the audit of
`unreal-lift` at `5dc93b2` plus its then-uncommitted changes; they are audit
references rather than current line anchors.

## Arena, timing, and reset

Use the region method's finite arena: state `s`, uncontrollable letter `u`,
controllable letter `c`, successor `T(s,u,c)`, and `Bad(s,u,c)`. Safety-objective
selection is specified below. `is_controllable` (`src/lib/oxidd_common.h:124`, prefixes
at 34–35) assigns system ownership exactly to names starting `controllable_`.
There is no family-specific naming logic. Artifact vocabulary reserves
`curr_%u`, `goal_%u`, `fair_%u`, `y_%u_*`, `x_%u_*`, `z_%u`, `move_%u`, `inv`,
and `system_winning`; `validate_game_names` (`gr1_check.c:739–800`) rejects
collisions with game inputs/latches.

The primal Mealy predecessor is `∀u ∃c [¬bad ∧ T(next)]` (`cpre_full`,
`gr1_oxidd.c:1236–1246`). Its Moore environment dual is
`∃u ∀c [bad ∨ T(next)]` (`dpre_full`/`dpre_unquantified`, 1248–1274).
Environment choices precede current system controls and depend only on state
and private memory. Both JSON sidecars declare:

```json
"system_strategy_semantics": "mealy",
"strategy_semantics": "moore",
"duality_delay_steps": 1
```

See `write_environment_policy_json` (879–881) and
`write_environment_certificate_json` (1071–1073).

Every game/artifact latch reset must be constant 0/1; self-literals or other
nonconstant resets yield `INVALID`. Reads use `aig_latch_at(...,&reset)`
(`gr1_oxidd.c:2060–2069`); the checker independently uses `reset_in_predicate`
(`gr1_check.c:2390–2406`) and `initial_cube` (3363–3378).
`solve_gr1_oxidd_impl` sets `*unreal = 1` when the concrete reset is outside
primal `W*` (2055–2086), then computes dual L and requires reset membership
before export (2088–2113). A disagreement records `OXIDD_FAILURE_INVALID` /
`"reset_not_environment_winning"` and exports nothing.

The checker derives one reset cube from game latches, never JSON. Certificate
checking requires `reset ∈ cert_inv` (`check_environment_certificate_mode`,
2543–2551; `"reset state is outside environment inv"`); closed-loop reachability
starts from that cube (`check_environment_closed_loop_mode`, 3500).
This proves the one concrete initial state, not an existential starting set.

## Policy interface

`export_environment_policy` (`gr1_oxidd.c:963–1010`) declares only `nstate`
game-latch and `ncounter = nfair_disj` counter inputs. Outputs are uncontrollable
game inputs and next counters. `var2lit` binds no original game inputs of either
player; any such BDD dependence fails `bdd2aig` with
`"BDD-to-AIG environment policy failed"` before writing.

`validate_policy_interface` (`gr1_check.c:663–737`) requires
`expected_inputs = nstate + ncounter + (environment ? 0 : nu)` (674–675),
mandatory state/counter names, and no controllable input names (716–722;
`"Moore environment policy reads current controllable '%s'"`). Arity/name
violations are `INVALID` before BDD work. `fill_policy_inputs` (1315 onward)
and `compile_policy_roots` (1585–1673) bind only state/counters; this is the
same interface exclusion, not an independently failing second defense.

The specific controllable-read diagnostic is not externally reached by current
mutations: extra inputs fail arity first; same-arity additions displace a
mandatory name. Game-name validation prevents aliases. The dependence test in
`test/oracle/test_gr1_environment_replay.py` wires an output to a smuggled
controllable input and pins `policy arity mismatch (inputs N+1/N, outputs M/M)`.
The mutated AAG passes parsing/structural validation first. This matters if
future interfaces permit optional/variable input counts.

Names are mandatory for game inputs and artifact inputs/outputs.
`aig_read_aag` permits missing symbols, but `validate_game_names` reports
`unnamed game input <i>`; `duplicate_inputs_or_outputs`, run first in artifact
interface checks, reports `unnamed input`/`unnamed output`. Unnamed game latches
use `l<j>` (`latch_name`). Handwritten tests pin the formerly crashing null-name
cases as `INVALID`.

## Universal response and progress

After substituting the environment choice, certificate checking leaves `c`
free and checks:

```text
allowed = successor(progress_target, next_state_after_env_choice) | bad
```

`checked_satisfiable` tests the negation in each relevant rank layer
(`gr1_check.c:2664–2672,2692`). Unsatisfiability means every system response
is unsafe or makes required progress at every covered state.

Closed-loop checking (`gr1_check.c:3462–3635`) searches the full product with
environment choice substituted and system controls free. `pre_exists_safe`
(3444–3460) existentially searches system escape choices. After reachability,
it rejects either an infinite safe play violating some environment fairness
infinitely-often requirement (3514–3544), or one visiting all environment
fairness and system justice sets infinitely often (3546–3597, nested μ/ν
 generalized-Büchi emptiness). No escape gives `CHECK_VERIFIED`; an escape gives
`CHECK_REFUTED` and `print_counterexample`.

The dual fixpoint (`write_environment_certificate_json`,
`gr1_oxidd.c:1082–1084`) mirrors primal `Z = nu Z. AND_j mu Y. OR_i nu X. cpre(...)`:

```text
L = mu Z. OR_j nu Y. AND_i mu X. dpre((Z | !goal_j) & Y & (X | fair_i))
```

It exports `z_k`, `y_{k,j}`, and inner chains `x_{k,j,i,l}`.
`validate_environment_certificate_predicates` (`gr1_check.c:2418–2516`) checks:

- All predicates are state-only, independent of `u`/`c`.
- Inner sets grow with l: `x_{l-1} ⊆ x_l` (2454–2467;
  `"dual inner rank is not monotone"`). This matches μX starting false
  (`gr1_oxidd.c:1300–1360`). A play's least occupied l must decrease until
  `fair_i`, as `rank_semantics` states (1096–1101); smaller l permits fewer
  non-fair rounds before X₀. Decreasing predicate sets would break this measure.
- `y_{k,j}` equals the intersection of final inner x sets over i (2470–2482).
- `z_k` equals the union of y over j (2484–2492), grows with k (2493–2504),
  and its last level equals `cert_inv` (2506–2514).

Each fairness mode `0..nfair_disj-1` and synthetic reset mode `-1` (treated as 0)
has separate rank and deterministic counter-update checks (2553,2601–2618).
At current-state `fair_i`, advance `i -> i+1 mod nfair_disj`; otherwise stay.
Counters are strategy memory, analogous to the region scheduler.
With no explicit fairness, one synthetic true disjunct remains. Its `curr_0`
updates to `curr_next_0 = 1` inside inv, and obligations use `fair = true`.
A handwritten `granted`-latch fixture (justice requires it, safety forbids it;
`z_0 = granted`, `z_1 = true`) passes certificate, closed-loop, and both methods.
This is the only zero-fairness fixture; its single logical counter never
advances to another mode, and both parametric generators use explicit fairness.

Every `(k,j)` participates: different reachable branches can violate different
justice goals. The multi-goal co-Büchi argument does not require one fixed culprit.

Required output `system_winning` is exported as NOT inv (`gr1_oxidd.c:1147–1150`)
and structurally checked (`gr1_check.c:902–906,959`), but certificate obligations
never evaluate its value. `test_gr1_unreal_certificate.py:262–300` enlarges it
with an unrelated well-formed AND cone without changing verdict/statistics;
an invalid AIG reference still yields `INVALID`. It is downstream duality
bookkeeping, omitted from selected roots like region `move_*`. Equivalent
unused-cone confirmation is absent for closed-loop/both.

## Safety objectives and deadlocks

| Mode | Selected bad predicate |
|---|---|
| `OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR` (`include/tlsf/oxidd_options.h:27`) | OR of all bad/b records (`build_gr1_roots`, `gr1_oxidd.c:175–205`, typed branch). |
| `OXIDD_SAFETY_OBJECTIVE_OUTPUT` | One ordinary output at `safety_output_index` (default 0). This is the raw C API default, including `solve_gr1_oxidd` with null `Gr1SolveOptions` (`oxidd_solve_options_default`, `src/lib/oxidd_common.c:18–39`). With no bad records or ordinary outputs, root construction fails; b-only games need explicit typed mode. |

The CLI selects typed mode for `multi-safety`, or `gr1` with bad records or an
ordinary-output count other than one; otherwise it selects ordinary output
(`src/tools/tlsfsolve/main.c:608–615`). The checker independently auto-detects
the same way (`gr1_check.c:1817–1838,1879–1898`), without a coordinating flag.
Raw C callers must set `Gr1SolveOptions.oxidd.safety_objective` to match;
`test/api/gr1_environment_replay.c` explicitly uses typed mode for its b fixture.

An already-bad response needs no rank progress (`allowed = successor(...) | bad`);
coverage solely by bad must hold for every system response. AIGER latch updates
are total Boolean functions, so the checker has no separate no-successor or
deadlock predicate/JSON field. Whether every upstream frontend needs no separate
deadlock notion has not been confirmed by this checker audit.

## Sidecars and trusted boundary

Policy fields (`write_environment_policy_json`, `gr1_oxidd.c:860–961`):

| field | meaning |
|---|---|
| `side` | `"environment"` |
| `reduction_semantics` | always `"exact"` (see strict-refusal note below) |
| `system_strategy_semantics` / `strategy_semantics` / `duality_delay_steps` | `"mealy"` / `"moore"` / `1`; see arena above |
| `counts.*` | `game_state_variables`, `original_game_latches`, `sampling_latches`, `goals`, `fairness_counters`, `controllable_inputs`, `uncontrollable_outputs`, plus the exported AIG's own `aig_inputs`/`aig_outputs`/`aig_ands` |
| `inputs.state[]` | `{policy_input, game_latch, name}` — game-latch binding, by index, not by name |
| `inputs.counter[]` | `{policy_input, fairness, name="curr_%u", reset:0, effective_initial}` — memory bits, `effective_initial` marks which one the all-zero encoding means |
| `inputs.controllable` | always `[]` for the environment side (no current-letter inputs) |
| `outputs.uncontrollable[]` | `{policy_output, game_input, name}` — the environment's own choices |
| `outputs.counter_next[]` | `{policy_output, fairness, name="curr_next_%u"}` — the memory update |
| `counter_semantics` | prose: all-zero means counter 0; advances `i -> i+1 mod fairness_count` when `fair_i` holds; "the uncontrollable outputs do not read the current controllable letter" |

The certificate (`write_environment_certificate_json`, 1053–1109) shares the
`format`, side, reduction/strategy semantics, and delay headers, and adds
`status: "unrealizable"`, `environment_counter_strategy_exported: true`,
`witness_condition`, `fixpoint`, `counts.*` with `outer_levels`, `rank_semantics`,
and `move_semantics`. `move_i` is the pre-Skolem relation `bad | target(next)`;
Skolemization follows universal quantification of all current controllable
inputs (1105–1108). Expected output names derive exactly from `goals`,
`fairness_assumptions`, `fairness_counters = nfair_disj`, and `outer_levels`;
unexpected names are `INVALID` before BDD compilation
(`output_is_expected_environment_certificate`, `gr1_check.c:828–869`;
`validate_environment_certificate_interface`, 871–975).

`validate_sidecars` (`gr1_check.c:548–626`) derives `ck->environment` from policy
`side` (562–563/579). Certificate side/status must agree (`"unrealizable"` iff
environment; side comparison around 609). Both sidecars' `game_state_variables`
and `goals` must match recomputed game counts; the environment certificate also
needs matching `fairness_assumptions`. `json_parse_object` (410–434) runs
`json_unique` (356–408) over the whole tree. Duplicate decoded keys at any depth
make `result.doc = nullptr` and yield `INVALID` via cannot-read/game-mismatch
checks; the duplicate-key discrimination test covers this.

The exporter refuses UNREAL artifacts for
`Gr1CertificateOptions.semantics == GR1_CERTIFICATE_SEMANTICS_STRICT`
(`gr1_oxidd.c:2074–2085`, `"refusing UNREAL certificate/policy from strict semantics"`).
Strict reduction is REAL-sound only (`include/tlsf/gr1_oxidd.h:37–39`);
this polarity safeguard precedes checking.

Sidecars contain no source/game hash. The checker does not independently derive
and compare `circuit.path`, `duality_delay_steps`, or most descriptive
`*_semantics`/prose fields. It proves obligations against supplied game content,
without binding that game to a claimed byte identity. A different game satisfying
the same obligations can also verify. Justice/fairness equality, rank progress,
and reset checks can reject a wrong same-shape game, as the discrimination test
does; that test is not identity binding.

Acacia's direct `run_native_gr1_arm` (`src/native_gr1_arm.cc:55–125`) checks
`args.tlsf_sha256 == pipeline->source_sha256` and reduced `game_sha256`
(72–113), then passes those exact bytes as `input.game_aag` to `tlsf_gr1_check`
(160–242), for both `real:gr1:oxidd` and the existing unselected
`unreal:gr1:oxidd`. REAL lifting additionally re-reduces and byte-compares the
returned candidate against a fresh target (`native_param_lift_arm.cc:164–192`).
Direct solving's candidate already is the target; lifting needs the additional
comparison because separate machinery builds its candidate. The audited code
has no `unreal:param-lift:oxidd` arm; one would need the REAL-lift binding pattern.
These Acacia checks were neither changed nor tested by this tlsf-tools audit.

`auto`/`both` side selection is policy-driven. Mismatched sidecars are checked,
but there is no dedicated regression pairing a REAL certificate and UNREAL
policy from different solves of the same game. Other explicit coverage limits
are the single zero-fairness fixture, certificate-only unused-cone confirmation,
and upstream deadlock semantics described above.
