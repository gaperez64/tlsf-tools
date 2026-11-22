# GR(1) environment certificates

On GR(1) UNREAL, `tlsfsolve` can export a certificate
(`tlsf-gr1-certificate-v1`) and policy (`tlsf-gr1-policy-v1`) with
`side: "environment"`. `tlsfcertcheck` checks them against the supplied game.
The [region method](gr1-region-method.md) accepts system certificates only.
Public APIs are in [gr1_check.h](../include/tlsf/gr1_check.h).

## Timing and interface

The system moves after seeing the current environment choice: primal
predecessor `∀u ∃c [¬bad ∧ T(next)]`, environment dual
`∃u ∀c [bad ∨ T(next)]`. Environment policies read game state and private
counter memory, and emit uncontrollable inputs plus next counters. They cannot
read either player's current inputs. Both sidecars declare:

```json
"system_strategy_semantics": "mealy",
"strategy_semantics": "moore",
"duality_delay_steps": 1
```

Names starting `controllable_` belong to the system. Game inputs and artifact
inputs/outputs require names; unnamed game latches use `l<j>`. Reserved artifact
names (`curr_%u`, `goal_%u`, `fair_%u`, `y_%u_*`, `x_%u_*`, `z_%u`,
`move_%u`, `inv`, `system_winning`) cannot collide with game inputs/latches.
Every game/artifact latch reset must be constant 0/1. Invalid names, interfaces
or resets yield `INVALID`. Reset checks use the concrete game-latch cube.

## Certificate obligations

After substituting the policy's environment choice, the checker leaves every
system response free and requires:

```text
allowed = successor(progress_target, next_state_after_env_choice) | bad
```

The dual rank structure is:

```text
L = mu Z. OR_j nu Y. AND_i mu X. dpre((Z | !goal_j) & Y & (X | fair_i))
```

The certificate exports state-only `z_k`, `y_{k,j}` and `x_{k,j,i,l}`.
Inner X sets grow with l; each Y is the intersection of final X lanes.
Each Z is the union of its Y goals, grows with k, and the final Z equals inv.
The concrete reset must lie in inv. All `(k,j)` layers participate; different
branches may violate different justice goals.

Each fairness counter mode and synthetic all-zero reset mode is checked.
The counter advances on current-state `fair_i`, otherwise stays. With no
fairness assumptions, a synthetic true lane supplies one logical counter.
An already-bad response needs no rank progress, but this must hold for every
system response. AIG latch updates are total; there is no separate deadlock field.

`closed-loop` checks the full game/policy product for a safe system escape.
No escape gives `CHECK_VERIFIED`; an escape gives `CHECK_REFUTED` and a
counterexample. The required `system_winning` output is exported as NOT inv
but its value is unused by certificate obligations. Its circuit must remain
structurally valid.

## Safety objective

| Mode | Bad predicate |
|---|---|
| `OXIDD_SAFETY_OBJECTIVE_TYPED_BAD_OR` | OR of all bad/b records. |
| `OXIDD_SAFETY_OBJECTIVE_OUTPUT` | Ordinary output at `safety_output_index` (default 0). Raw C API default, including null `Gr1SolveOptions`. |

The CLI and checker choose typed mode for multi-safety, or GR(1) with bad
records or an ordinary-output count other than one. Otherwise they use the
single ordinary output. C callers must set
`Gr1SolveOptions.oxidd.safety_objective` to match; b-only games need typed mode.

## Sidecars

| Policy field | Meaning |
|---|---|
| `side` | `"environment"`. |
| `reduction_semantics` | `"exact"`. Strict reductions cannot export UNREAL artifacts. |
| `system_strategy_semantics` / `strategy_semantics` / `duality_delay_steps` | `"mealy"` / `"moore"` / `1`. |
| `counts.*` | `game_state_variables`, `original_game_latches`, `sampling_latches`, `goals`, `fairness_counters`, `controllable_inputs`, `uncontrollable_outputs`, `aig_inputs`, `aig_outputs`, `aig_ands`. |
| `inputs.state[]` | `{policy_input, game_latch, name}`; binding by index. |
| `inputs.counter[]` | `{policy_input, fairness, name="curr_%u", reset:0, effective_initial}`; the last field marks the all-zero encoding. |
| `inputs.controllable` | `[]`. |
| `outputs.uncontrollable[]` | `{policy_output, game_input, name}`. |
| `outputs.counter_next[]` | `{policy_output, fairness, name="curr_next_%u"}`. |
| `counter_semantics` | All-zero means counter 0; advances on `fair_i`; choices do not read current controls. |

The certificate shares format/side/strategy headers and adds
`status: "unrealizable"`, `environment_counter_strategy_exported: true`,
`witness_condition`, `fixpoint`, `counts.outer_levels`, `rank_semantics` and
`move_semantics`. `move_i` is `bad | target(next)` before Skolemization, which
follows universal quantification of current controls. Output names/counts must
match goals, fairness lanes and outer levels; unexpected names are `INVALID`.

Side/status and game counts must agree; duplicate decoded JSON keys at any
depth are `INVALID`. `auto`/`both` select the side from the policy.
`GR1_CERTIFICATE_SEMANTICS_STRICT` is REAL-sound only and refuses UNREAL export.

Sidecars contain no source/game hash. The checker proves obligations against
the supplied content; it does not bind that content to a claimed byte identity
or validate every descriptive semantics field. Callers must independently bind
source and game bytes. A different game satisfying the obligations may verify.
