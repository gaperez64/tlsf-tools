# GR(1) environment certificate and counter-strategy policy

This document describes, from the code as it stands, the artifact pair that
`tlsfsolve` exports when a GR(1) game is **UNREAL** and that `tlsfcertcheck`
independently verifies: the `side: "environment"` certificate
(`tlsf-gr1-certificate-v1`) and the `side: "environment"` policy
(`tlsf-gr1-policy-v1`). It exists because no prior document covers this half
of the format: `docs/gr1-region-method.md` documents only the `side:
"system"` region method. Every claim below cites the function and, where
useful, the line range it was read from in the `unreal-lift` worktree
(tlsf-tools `5dc93b2` plus this branch's uncommitted changes). Gaps between
what the checker actually enforces and what the semantics require are called
out explicitly in their own subsections rather than smoothed over.

Exporter: `src/lib/gr1_oxidd.c`. Checker: `src/lib/gr1_check.c`, public API
`include/tlsf/gr1_check.h`. Shared ownership convention:
`src/lib/oxidd_common.h`.

## 1. Arena, players, and the Mealy/Moore duality

The underlying game is the same finite AIGER arena used by the `side:
"system"` region method (see `docs/gr1-region-method.md`, "Arena and
timing"): state `s`, uncontrollable letter `u`, controllable letter `c`,
deterministic successor `T(s,u,c)`, unsafe predicate `Bad(s,u,c)`. Which
literals fold into `Bad` depends on a solver-selected safety-objective mode,
not unconditionally on "every typed bad record" — see §7 for the two modes
and where each side selects between them. A signal is
system-owned iff its name has the `controllable_` prefix
(`is_controllable`, `src/lib/oxidd_common.h:124`, prefix constants at
lines 34–35); everything else is environment-owned. This is a **name-based
protocol convention** fixed by the AbsSynthe/SYNTCOMP AIGER format, not a
benchmark- or family-specific hardcoding — `tlsfsolve`/`tlsfcertcheck` never
special-case a signal's literal name beyond this one reserved prefix (and the
generated `curr_%u`/`goal_%u`/`fair_%u`/`y_%u_*`/`x_%u_*`/`z_%u`/`move_%u`/
`inv`/`system_winning` output names on certificate/policy artifacts
themselves, which are the format's own reserved vocabulary, checked for
collisions against game input/latch names in `validate_game_names`,
`gr1_check.c:739–800`).

The solver's own convention is a **Mealy** round: the environment supplies
`u`, then the system picks `c` as a function of the state and `u`
(`cpre_full`, `gr1_oxidd.c:1236–1246`: `∃c` is applied after `∀u`... more
precisely the CPRE used to build the system's winning region is `∀u ∃c
[¬bad ∧ T(next)]`, i.e. the system's choice may depend on `u`). The
environment counter-strategy exported on an UNREAL verdict is the **Moore
dual of that same round**: both the certificate and the policy JSON declare
this explicitly —

```json
"system_strategy_semantics": "mealy",
"strategy_semantics": "moore",
"duality_delay_steps": 1
```

(`write_environment_policy_json`, `gr1_oxidd.c:879–881`;
`write_environment_certificate_json`, `gr1_oxidd.c:1071–1073`). Concretely,
the environment's choice of `u` at round `t` is available before the
system's `c` at round `t` in the original game, so the environment's *own*
strategy cannot look at that same-round `c` — it can only depend on game
state and its own private memory. `dpre_full`/`dpre_unquantified`
(`gr1_oxidd.c:1257–1274`, `~1248` region) compute the dual predecessor as
`∃u ∀c [bad ∨ T(next)]`, the literal De Morgan dual of `cpre_full`.

## 2. Initialization and initial-state quantification

Every latch reset in the game, and in every exported certificate/policy, must
be a constant `0` or `1`; a self-literal or otherwise non-constant reset is
unsupported and yields `INVALID` (same rule as the region method,
`docs/gr1-region-method.md` "Validated certificate shape"; enforced on read
via `aig_latch_at(...,&reset)` checks throughout, e.g.
`gr1_oxidd.c:2060–2069`, and independently re-derived by the checker's own
`reset_in_predicate`, `gr1_check.c:2390–2406`, and `initial_cube`,
`gr1_check.c:3363–3378`).

The solver computes the system's primal winning region `W*` and, if the
concrete reset assignment (from the game's own latch resets) does **not**
satisfy `W*`, sets `*unreal = 1` (`solve_gr1_oxidd_impl`,
`gr1_oxidd.c:2055–2086`). Before ever exporting an environment
certificate/policy, it goes further and computes the **dual** fixpoint `L`
(the environment's own winning region) and asserts that the reset state
*is* in `L` (`gr1_oxidd.c:2088–2113`); if that internal cross-check fails, it
records `OXIDD_FAILURE_INVALID`/`"reset_not_environment_winning"` and the
export does not happen. So a REAL/UNREAL disagreement between the primal and
dual fixpoints at the reset state is caught before any artifact leaves the
solver, not left for the checker to discover.

The checker re-derives the reset cube itself from the **game's** own latch
resets — never from anything in the JSON — and checks membership two
independent ways: the `certificate` method checks `reset ∈ cert_inv`
directly (`check_environment_certificate_mode`, `gr1_check.c:2543–2551`,
message `"reset state is outside environment inv"`); the `closed-loop`
method seeds its forward-reachability fixpoint from the same cube
(`check_environment_closed_loop_mode`, `gr1_check.c:3500`). There is exactly
one initial state per game; the certificate is a proof about that one state,
not an existential claim over a set of possible starting states.

## 3. Legal environment actions and what the policy may depend on

The exported **policy** AIG's declared inputs are *only* the `nstate` game
latches plus `ncounter` (= `nfair_disj`, the number of fairness-disjunction
counters) memory bits; its outputs are the environment's own uncontrollable
game inputs plus the `ncounter` next-counter bits
(`export_environment_policy`, `gr1_oxidd.c:963–1010`: `var2lit` is populated
only for latches and counter inputs — the original game's controllable *and*
uncontrollable input variables are never wired as policy inputs at all, so a
malformed BDD referencing either would fail `bdd2aig` conversion with a
`"BDD-to-AIG environment policy failed"` error before the artifact is even
written).

This is enforced independently, twice, on the checker side:

- **Interface (structural) check.** `validate_policy_interface`
  (`gr1_check.c:663–737`) computes
  `expected_inputs = nstate + ncounter + (environment ? 0 : nu)`
  (line ~674–675) — for an environment policy this explicitly *excludes* the
  environment's own uncontrollable inputs `nu` from the expected input set —
  and, for every controllable game-input name, asserts
  `!has_input(policy, name)` (lines ~716–722, message `"Moore environment
  policy reads current controllable '%s'"`). Any policy whose declared input
  count doesn't match, or that lists a controllable name among its inputs,
  is rejected as `INVALID` before any BDD work happens.
- **Substitution has no binding for a controllable variable at all.**
  `fill_policy_inputs` (`gr1_check.c:1315` onward) and `compile_policy_roots`
  (`gr1_check.c:1585–1673`) only ever bind the state and counter variables
  when recompiling the policy's own AIG into BDD roots; there is no code
  path anywhere in this binding step that supplies a value for a
  controllable game signal. This is not best understood as an independent
  *second enforcement layer* on top of the interface check — it is more
  that, given the interface check already guarantees the arity/name set
  excludes any controllable input, there is no representation left in which
  a controllable-dependent policy could even be expressed; the two facts
  are two views of the same exclusion, not two separately-failing defenses.

**Finding.** Tracing the interface check carefully: the count check
(`aig_num_inputs != expected_inputs`) and the per-name presence checks for
the mandatory state/counter inputs run *before* the specific "reads current
controllable" line (`gr1_check.c:717–722`), and `validate_game_names`
(`gr1_check.c:739–800`) additionally prevents a game input from aliasing a
state input. For a same-arity artifact, adding a controllable-named input
necessarily displaces a mandatory state/counter name, which the earlier
presence check catches first with a different message; for a larger-arity
artifact, the count check catches it first. I did not find an externally
constructed malformed artifact that reaches the "reads current controllable"
line specifically rather than one of those two earlier ones — the interface
rules already structurally exclude such an input regardless of which
specific check reports it. U0's Mealy-dependence discrimination test
(`test/oracle/test_gr1_environment_replay.py`) makes an environment output's
cone depend on a smuggled controllable-named input (not merely add a
dangling, unread one) and pins the complete diagnostic it reaches,
`policy arity mismatch (inputs N+1/N, outputs M/M)`: the arity check fires
first, as traced above. Reaching that check also shows that `aig_read_aag`
and `validate_aig_structure` accepted the mutated circuit. The observation
is recorded here so a future change to the interface (e.g. an
optional/variadic input) does not accidentally reopen a real gap while the
"reads current controllable" line keeps suggesting it is independently
exercised.

**Names are mandatory.** `aig_read_aag` accepts an AIGER file whose symbol
table omits an input or output, leaving that name null. Because the checker
binds every artifact by name, it rejects such files as `INVALID` before any
name comparison: a game input without a name gives `unnamed game input <i>`
(`validate_game_names`, which runs first in the interface phase), and a
policy or certificate input or output without a name gives `unnamed input` or
`unnamed output` (`duplicate_inputs_or_outputs`, which runs first in
`validate_policy_interface` and in both certificate interface checks). Game
latches may be unnamed; they are bound by the fallback name `l<j>`
(`latch_name`). Before this change the unnamed-output and unnamed-game-input
cases reached `strcmp` with a null pointer and crashed the checker; U0's
hand-written fixtures pin both diagnostics.

## 4. The universal system-response obligation

Once the environment's choice is fixed by substitution, the residual
predicate over `c` is required to be valid for **every** controllable
assignment — this is the concrete meaning of "duality_delay_steps: 1". The
`certificate` method computes

```text
allowed = successor(progress_target, next_state_after_env_choice) | bad
```

(`gr1_check.c:2664–2672`) leaving `c` a free variable, and asks whether
`allowed`'s negation is satisfiable anywhere in the relevant rank layer
(`checked_satisfiable`, same block, `~2692`); UNSAT of the negation is
exactly "for all `c`, `allowed` holds" — the standard way to check a
universal without quantifier elimination. At every state the certificate
claims to cover, for every value the system could pick, the play must either
already be unsafe or make measurable rank progress.

The `closed-loop` method makes the same obligation concrete by explicit game
search instead: it builds the full product with the environment's choice
substituted in and `c` left as part of the state space
(`check_environment_closed_loop_mode`, `gr1_check.c:3462–3635`), computes
forward reachability, and then asks — by existentially quantifying over `c`
in `pre_exists_safe` (`gr1_check.c:3444–3460`) while searching for a system
escape — whether the **system**, left completely free to choose `c` at every
step, has *any* infinite safe play that either (a) stays safe while some
environment fairness assumption is satisfied only finitely often (a
"vacuous assumption" escape, `gr1_check.c:3514–3544`), or (b) stays safe and
visits every environment fairness set *and* every system justice goal
infinitely often (`gr1_check.c:3546–3597`, generalized-Büchi emptiness via
nested `μ`/`ν` computation). If no such play exists, `CHECK_VERIFIED`; if one
does, `CHECK_REFUTED` with a concrete counterexample
(`print_counterexample`, invoked at the `refuted:` labels).

## 5. Ranks, progress, and the assumption/justice obligations the environment must keep

The exported dual fixpoint is the literal De Morgan dual of the system's own
region-method fixpoint (compare `docs/gr1-region-method.md`'s
`Z = nu Z. AND_j mu Y. OR_i nu X. cpre(...)`):

```text
L = mu Z. OR_j nu Y. AND_i mu X. dpre((Z | !goal_j) & Y & (X | fair_i))
```

(`write_environment_certificate_json`, `gr1_oxidd.c:1082–1084`). Per outer
level `k` there is one state predicate `z_k`; per `(k, goal j)` there is
`y_{k,j}`; per `(k, j, fairness-disjunct i)` there is a monotone chain of
inner ranks `x_{k,j,i,l}`. `validate_environment_certificate_predicates`
(`gr1_check.c:2418–2516`) checks, semantically (not just structurally):

- every `z_k`, `y_{k,j}`, `x_{k,j,i,l}` is state-only (no `u`/`c` dependence);
- each inner `x` chain is monotone **increasing** as `l` increases: the
  checker rejects `x_{l-1} & !x_l`, i.e. requires `x_{l-1} ⊆ x_l`
  (`"dual inner rank is not monotone"`, ~2454–2467), matching the `AND_i mu
  X` fixpoint directly — `mu` is a least fixpoint seeded at `false`
  (`gr1_oxidd.c:1300–1360`'s `Bdd x = oxidd_bdd_false(manager)` growing every
  iteration), so the **sets indexed by rank grow** with `l`. What actually
  *decreases* is a play's own **selected** rank — the least `l` such that
  the current state lies in `x_{k,j,i,l}` — as the play makes progress
  without yet satisfying `fair_i` (exactly as the exporter's own
  `rank_semantics` prose says: "the least inner X level must decrease until
  fair_i holds", `gr1_oxidd.c:1096–1101`). A smaller `l` means *fewer*
  additional non-`fair_i` rounds are tolerated before the argument requires
  reaching `X_0`; nesting the sets the other way (decreasing) would make
  that measure ill-founded. Do not conflate the two: the *predicate family*
  is monotone increasing in `l`; the *witness a single play occupies* is
  what must strictly decrease while stuck off `fair_i`;
- `y_{k,j}` equals the intersection (not union) of the final `x_{k,j,i,·}`
  over `i` (~2470–2482) — the dual conjoins over fairness disjuncts where the
  primal disjoins, again the De Morgan mirror;
- `z_k` equals the union of `y_{k,j}` over `j` (~2484–2492);
- `z_k` is monotone increasing in `k` (~2493–2504);
- `cert_inv` equals `z` at the last computed level (~2506–2514).

The environment's own fairness assumptions are the thing whose eventual
violation this rank argument tracks. `check_environment_certificate_mode`
iterates every fairness-counter **mode** — the current counter value
`0..nfair_disj-1`, plus a synthetic `mode = -1` treated identically to mode
`0` so the all-zero reset encoding is covered the same way the region
method's scheduler does (`gr1_check.c:2553`, mirroring
`docs/gr1-region-method.md`'s "the all-zero reset encoding, interpreted as
goal 0") — and for each mode checks both that the counter's own next-value
update follows the documented deterministic schedule (advance `i -> i+1 mod
nfair_disj` iff `fair_i` holds at the *current* state, else stay;
`gr1_check.c:2601–2618`) and that the one-step rank obligation from §4 holds.
The counter is strategy **memory**, exactly as on the system side
(`docs/gr1-region-method.md`: "The counter is strategy memory, not part of
the certificate's move relation" — the same statement applies symmetrically
here, just keyed to fairness-assumption satisfaction instead of
justice-goal satisfaction).

When the source game declares zero explicit fairness assumptions,
`nfair_disj` still defaults to (at least) one synthetic always-true disjunct,
mirroring the system side's documented convention ("the single synthetic
disjunct behaves as `F_0 = true`, so rank stuttering is unavailable",
`docs/gr1-region-method.md`). The environment policy then carries one
counter, `curr_0`, whose update is always `curr_next_0 = 1` inside `inv`,
and every rank obligation uses `fair = true`. U0's hand-written zero-fairness
witness in `test/oracle/test_gr1_environment_replay.py` (one `granted`
latch that justice demands and safety forbids; outer levels `z_0 = granted`
and `z_1 = true`) is verified by the `certificate`, `closed-loop` and `both`
methods, which exercises this convention on the environment side.

## 6. Which guarantee must be violated, and whether it may vary by branch

The rank argument is keyed by `(outer level k, goal j)` pairs and the
per-mode obligation loop covers **every** justice goal `j` across every
level, not a single fixed one (`OR_j` in the fixpoint, §5). Different
reachable branches of the same certified play can therefore be attributed to
different violated goals — this format is a genuine multi-goal co-Büchi
argument, and does **not** impose "one fixed guarantee is always the
culprit" as plan §8.1 explicitly warns against assuming.

`system_winning` is exported as an additional required certificate output,
defined structurally as `NOT inv` (`gr1_oxidd.c:1147–1150`) and required to
be *present and well-formed* by `validate_environment_certificate_interface`
(`gr1_check.c:902–906, 959`), but its Boolean **value** is not evaluated by
the `certificate` method's checked obligations — confirmed by
`test_gr1_unreal_certificate.py`'s own differential (lines 262–300): its cone
can be enlarged (a longer chain of AND gates computing an unrelated
function) without changing the certificate verdict or the reported
statistics, and it is only if that enlarged cone is *additionally made
structurally invalid* (a bad AIG reference) that the checker reports
`INVALID` — meaning `system_winning`'s *AIG structure* is still validated
unconditionally (the interface check above runs regardless), but the
*specific Boolean function it computes* is never consulted by the checked
obligations. Distinguish these: an unevaluated cone (any well-formed
function accepted, verdict unaffected) is not the same claim as an
unvalidated one (a malformed AIG reference is still rejected). As long as
the cone is present, well-formed, and excluded from the selected-root set
(the same
"irrelevant exclusive cones are not evaluated" discipline documented for
`move_*` on the region method, `docs/gr1-region-method.md`). This is
intentional, documented behavior, not a gap — `system_winning` is a
structural REAL/UNREAL duality bookkeeping field for downstream tooling. I
did not find (or add) an equivalent unused-cone confirmation for the
`closed-loop` method; see Gaps §8.

## 7. Deadlocks and safety violations

Which literals fold into `bad(s, u, c)` depends on a safety-objective mode,
selected the same way on both sides of the duality — this section documents
that condition precisely, since an earlier draft of this document
overstated it as unconditional.

- `OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR` (`include/tlsf/oxidd_options.h:27`):
  `bad` is the disjunction of every AIGER `bad`-output/`b`-record
  (`docs/gr1-region-method.md`'s `Bad(s,u,c)`; `gr1_oxidd.c`'s
  `build_gr1_roots`, ~175–205, when `typed` is true).
- `OXIDD_SAFETY_OBJECTIVE_OUTPUT` (the solver C API's own default:
  `oxidd_solve_options_default`, `src/lib/oxidd_common.c:18–39`, which is
  also what `solve_gr1_oxidd` uses for a null `Gr1SolveOptions`): `bad` is
  one selected *ordinary* AIGER output (`safety_output_index`, default 0).
  With zero AIGER bad-records and zero ordinary outputs this mode has
  nothing to select and root construction fails outright — a game encoded
  purely via `b`-records (as this document's own fixtures are) requires the
  typed-bad mode explicitly when driven through the raw C API; a caller that
  leaves the default in place gets no game at all, not a wrong one.

The **CLI** (`tlsfsolve`) never leaves this to the C API's default: it
resolves the mode itself from the game's own structure before solving
(`src/tools/tlsfsolve/main.c:608–615`): typed-bad whenever the resolved
profile is `multi-safety`, or is `gr1` with either `aig_num_bad(game) > 0`
or `aig_num_outputs(game) != 1`; otherwise the single-ordinary-output mode.
The **checker** does not take this as an option at all — `gr1_check.c`'s own
game-compilation step (~1817–1838, 1879–1898) auto-detects the same way the
CLI does, directly from `aig_num_bad`/`aig_num_outputs`, so a game encoded
consistently with either convention is read the same way by both solver and
checker without any coordinating flag between them. A **raw C API** caller
(as opposed to the CLI) must set `Gr1SolveOptions.oxidd.safety_objective`
itself, matching the game it is about to solve;
`test/api/gr1_environment_replay.c` is one such caller and selects
`OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR` for its `b`-record fixture.

`bad(s, u, c)`, once selected, appears as one disjunct of the one-step
obligation (`allowed = successor(...) | bad`, §4): the environment's
argument is happy to let a state count as "covered" purely because it is
already unsafe for
*every* system response, with no rank progress required there at all.

The AIGER game encoding has a **total** next-state function per latch (every
latch's `next` literal is defined as a Boolean function over the current
state and inputs), so there is no distinct notion of "no successor" in this
format — safety violations are the only "stuck" outcome the checker
recognizes, encoded via `bad`, not via a separate deadlock predicate. I
looked for a dedicated deadlock output or JSON field and found none; noting
this as an open question rather than a gap, since totality of AIGER latches
may simply make a separate deadlock concept inapplicable here.

## 8. Memory updates and the JSON sidecar fields

**`side: "environment"` policy** (`tlsf-gr1-policy-v1`,
`write_environment_policy_json`, `gr1_oxidd.c:860–961`):

| field | meaning |
|---|---|
| `side` | `"environment"` |
| `reduction_semantics` | always `"exact"` (see strict-refusal note below) |
| `system_strategy_semantics` / `strategy_semantics` / `duality_delay_steps` | `"mealy"` / `"moore"` / `1` — see §1 |
| `counts.*` | `game_state_variables`, `original_game_latches`, `sampling_latches`, `goals`, `fairness_counters`, `controllable_inputs`, `uncontrollable_outputs`, plus the exported AIG's own `aig_inputs`/`aig_outputs`/`aig_ands` |
| `inputs.state[]` | `{policy_input, game_latch, name}` — game-latch binding, by index, not by name |
| `inputs.counter[]` | `{policy_input, fairness, name="curr_%u", reset:0, effective_initial}` — memory bits, `effective_initial` marks which one the all-zero encoding means |
| `inputs.controllable` | always `[]` for the environment side (never present — see §3) |
| `outputs.uncontrollable[]` | `{policy_output, game_input, name}` — the environment's own choices |
| `outputs.counter_next[]` | `{policy_output, fairness, name="curr_next_%u"}` — the memory update |
| `counter_semantics` | prose: all-zero means counter 0; advances `i -> i+1 mod fairness_count` when `fair_i` holds; "the uncontrollable outputs do not read the current controllable letter" |

**`side: "environment"` certificate** (`tlsf-gr1-certificate-v1`,
`write_environment_certificate_json`, `gr1_oxidd.c:1053–1109`): the same
`format`/`side`/`reduction_semantics`/`system_strategy_semantics`/
`strategy_semantics`/`duality_delay_steps` header fields, plus
`status: "unrealizable"`, `environment_counter_strategy_exported: true`,
`witness_condition` (prose, quoted in §4's closed-loop description),
`fixpoint` (the `L = mu Z. ...` string from §5), `counts.*` (adds
`outer_levels`), `rank_semantics` (prose), `move_semantics` (prose: `move_i`
is the *pre-Skolem* relation `bad | target(next)` — the exported
uncontrollable policy is Skolemized from it only after universal
quantification of every current controllable input, `gr1_oxidd.c:1105–1108`
— this is the certificate's own account of the derivation in §3/§4).
`outputs` are validated by name against the exact expected set generated
from `goals`, `fairness_assumptions`, `fairness_counters` (i.e.
`nfair_disj`), and `outer_levels`
(`output_is_expected_environment_certificate`, `gr1_check.c:828–869`;
`validate_environment_certificate_interface`, `gr1_check.c:871–975`) — an
unexpected output name of any kind is rejected as `INVALID` before any BDD
work.

**Cross-artifact and JSON-parsing invariants, shared by both sidecars**
(`validate_sidecars`, `gr1_check.c:548–626`):

- `ck->environment` is decided from the **policy** sidecar's `side` field
  (line 562–563/579), not from a command-line flag; `certificate.status`
  must then agree (`"unrealizable"` iff environment) and
  `certificate.side == policy.side` is cross-checked (~609).
- Both sidecars must satisfy `game_state_variables == ck->nstate` and
  `goals == ck->ngoals` (recomputed from the **game**, never trusted from
  JSON); the environment certificate additionally requires
  `fairness_assumptions == ck->nfair`.
- Every JSON document (certificate and policy alike) is parsed once through
  `json_parse_object` (`gr1_check.c:410–434`), which runs `json_unique`
  (`gr1_check.c:356–408`) over the **entire** parsed tree — any duplicate key
  at any nesting depth, not just the top level, makes the whole document
  parse as absent (`result.doc = nullptr`), which then fails the
  "cannot read"/"does not match this game" checks in `validate_sidecars`
  and yields `INVALID`. This is the mechanism U0's "duplicate decoded JSON
  keys" discrimination test exercises.
- `Gr1CertificateOptions.semantics == GR1_CERTIFICATE_SEMANTICS_STRICT`
  causes the **exporter** to refuse ever producing an UNREAL
  certificate/policy at all (`solve_gr1_oxidd_impl`, `gr1_oxidd.c:2074–2085`,
  `"refusing UNREAL certificate/policy from strict semantics"`) — because a
  strict reduction is documented as REAL-sound only
  (`include/tlsf/gr1_oxidd.h:37–39`). This is a polarity safeguard enforced
  before the checker is ever involved, not a checker responsibility.
- **What is *not* enforced by any of the above:** no source hash, no game
  hash, the JSON `circuit.path` string, `duality_delay_steps`, and most of
  the descriptive `*_semantics`/prose fields are read for cross-checking
  elsewhere in this document but are not independently re-derived and
  compared against the game's own structure the way counts and Boolean
  predicates are. More fundamentally, `validate_sidecars` and the semantic
  obligation checks together prove that the supplied certificate/policy is
  a valid proof *for the game byte content actually supplied as input* —
  they never bind that game to any particular claimed identity. A valid
  certificate could equally verify against a *different* game, if that
  different game happens to satisfy the same obligations; no game-specific
  byte identity is promised by this format or this checker. Identity
  binding, where it exists at all, lives one layer up, in whatever calls
  the checker — see gap 5 below.

## 9. Gaps and open items found while writing this document

These are explicit findings per the task's instruction not to paper over
them; none of them is fixed by U0, whose only checker change turns two
null-name crashes into `INVALID` diagnostics (§3, "Names are mandatory").

1. **§3 finding.** The specific `"Moore environment policy reads current
   controllable"` diagnostic (`gr1_check.c:717–722`) appears to be
   unreachable via an externally mutated same-arity artifact today; the
   arity check and the mandatory-name presence checks jointly close the
   door first. Not unsound (arity enforcement alone suffices), but worth
   knowing before relying on that specific message, or before ever making
   the policy interface's input count variable.
2. **§5.** The zero-explicit-fairness synthetic-disjunct convention on the
   *environment* side is exercised only by U0's one hand-written fixture,
   whose single fairness counter never advances; the two parametric
   generators both declare explicit fairness assumptions.
3. **§6.** `system_winning`'s "declared but unevaluated by `certificate`"
   status is confirmed for the `certificate` method only
   (`test_gr1_unreal_certificate.py`); U0 did not add or find equivalent
   confirmation for `closed-loop`/`both`.
4. **§7.** No deadlock-specific predicate or JSON field exists in this
   format; AIGER latch totality may make this a non-issue, but it was not
   possible to confirm that from the checker code alone (it would require
   checking every upstream frontend that produces these games).
5. **Hash-based source binding (plan §8.4's "wrong game paired with
   recomputed, self-consistent hashes")** does not exist anywhere in
   tlsf-tools' own JSON sidecars, for either polarity — there is no `hash`
   field in this format at all, and the checker proves obligations against
   whichever game bytes it is handed rather than binding to a claimed
   identity (see the invariants list above). An earlier draft of this
   document claimed source-hash binding exists "only in the REAL lift arm";
   that was wrong. Acacia's **direct** GR(1) arm
   (`src/native_gr1_arm.cc:55–125`, the single `run_native_gr1_arm` function
   used for both `real:gr1:oxidd` and the already-existing but unselected
   `unreal:gr1:oxidd`) already checks `args.tlsf_sha256 ==
   pipeline->source_sha256` and a `game_sha256` against the reduced game
   bytes (~72–113) *before* solving, then passes those exact
   hash-verified bytes as `input.game_aag` to `tlsf_gr1_check`
   (~160–242) — for **both polarities**, today, not as a future addition.
   The REAL *lift* arm additionally re-reduces and byte-compares the
   *returned candidate* against a freshly re-derived target
   (`native_param_lift_arm.cc:164–192`), a concern specific to lifting
   (the candidate is constructed by machinery separate from the target
   reduction, so it needs its own binding check) that plain direct solving
   does not have, because direct solving's "candidate" *is* the exact
   target by construction. There is no `unreal:param-lift:oxidd` arm yet
   (that is U1/U2's deliverable), so there is nothing yet analogous to the
   REAL lift arm's re-reduce-and-compare step on the UNREAL side — that
   binding step will need to be built alongside U1/U2, mirroring the
   REAL-lift pattern (plan §5.4), not the simpler direct-arm pattern, since
   lifting has the same candidate/target mismatch risk lifting always has.
   U0's own scope is tlsf-tools only, so none of this Acacia-level binding
   was touched or tested here; U0's "wrong game, same shape" discrimination
   test instead exercises what tlsf-tools' own checker does today at the
   layer U0 actually touches: pairing a certificate/policy with a
   structurally-identical but semantically different game and relying on
   the checker's own game-content cross-checks (justice/fairness predicate
   equality, the one-step rank obligation, reset-membership) to catch it —
   this is a different, checker-level claim from identity binding, not a
   substitute for it.
6. **`--method auto`/`--method both` side selection** is entirely
   policy-sidecar-driven (`gr1_check.c:562–563/579`); a certificate/policy
   pair with mismatched `side` fields is caught (§8), but I did not find
   (or add, to keep scope to what plan §8.4 actually lists) a dedicated test
   pairing a REAL certificate with an UNREAL policy taken from a
   *different* solve of the *same* game. Worth a follow-up alongside item 2.
