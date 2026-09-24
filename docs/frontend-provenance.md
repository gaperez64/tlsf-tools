# Frontend expansion provenance

`tlsf2tlsf --provenance-out instance.json source.tlsf` expands the source and
writes basic TLSF to stdout. `--output` can redirect the TLSF separately. The
JSON schema is `tlsf-tools.frontend-provenance.v1`; consumers must check both
`schema` and `format_version` before using it. `source_sha256` hashes the exact
input bytes, including comments and whitespace. `--param NAME=VALUE` overrides
are reflected in `parameters` and in the expanded records.

Each signal has a direction and a `declaration_id` such as `input:2`. The
ordinal is its source declaration order within INPUTS or OUTPUTS. Expanded
members retain the same ID and carry their concrete `index_tuple`, resolved
`bounds`, and `width`. `dimensions` is the number of declared TLSF bus axes;
the current parser supports one bus axis. A grid flattened into a bus therefore
has one signal axis, while its generating formulas may have two bindings.
`index_role` is `representation-bit` for explicitly typed enum buses and for
source definitions that implement the structurally proved halving recurrence
for floor(log2(x)) followed by its bit-width wrapper. The latter receive
`width_kind: proved-logarithmic-encoding`. The proof checks AST operators and
recursion, never function or signal names. Other computed widths are
`undetermined` and retain their original bound in `width_expression`.
`element` denotes a direct declared bus position, not a proof that positions
are symmetric clients. A consumer must prove any further encoding or symmetry
role before lifting it.

Each `conjuncts` entry records the source block, its one-based formula ordinal,
an AST `source_node_id`, a zero-based `generated_position` within that source
formula, the concrete integer generator `bindings`, expanded
formula text, and the exact names of mentioned expanded signals. Source node
IDs are assigned by source AST preorder before parameter substitution and
definition expansion. They therefore survive signal renaming, basename
changes, and parameter overrides. `source_formula_id` is `BLOCK:ordinal` and
can be used with `source_node_id` to align instances. Conjunctions at the top
level and directly under a top-level G are split; true terms are retained so
the frontend inventory is complete. The pair (`source_formula_id`,
`generated_position`) uniquely identifies an expanded conjunct, including
temporal ranges and repeated definition calls; it remains stable under signal
renaming and source filename changes. Consumers must verify this uniqueness.
When a generator binds a non-integer set element, `ambiguous` is true because
the integer binding tuple is incomplete. A formula reference that does not
resolve to an expanded declaration also sets `ambiguous` and is marked on its
conjunct. Duplicate expanded signal names also set `ambiguous`, even when the
declarations differ. Consumers must decline structural lifting in these cases
and independently verify the signal inventory has unique names.

`gr1_monitor_game.py --provenance-out` reads this output and matches each Spot
monitor to a unique source conjunct by LTL equivalence. It sets
`source_origin_metadata.available` only when the frontend
record is valid and every monitor has one unique origin. Its
`provenance_source` is `frontend` in that case. If matching is ambiguous or the
frontend output is unavailable, the metadata says `suffix-heuristic`; generic
lifting must reject that fallback. The AIG output does not depend on any of
these metadata decisions. The monitor builder reads the TLSF bytes once,
passes that snapshot to both lowering tools and the provenance frontend, and
checks that the frontend SHA-256 equals the snapshot hash.

## Monitor game symbol namespace

`gr1_monitor_game.py` writes every environment input as
`uncontrollable_<TLSF name>` and every system output as
`controllable_<TLSF name>` in the game AIG. This encoding is injective across
roles, including TLSF names that already begin with either prefix or resemble
monitor latches. Internal game symbols use neither prefix. Provenance signal
records retain their TLSF `name` and include the encoded `game_symbol`.
The solver and checker classify `controllable_` symbols as system moves;
policy and certificate artifacts refer to the encoded game symbols.
`tlsfcertcheck --emit-controller` restores the original TLSF input and output
names. `verify_strategy_explicit.py` accepts standalone raw TLSF output names
and game-prefixed strategy outputs by checking the complete interface.
Game AIG symbol bytes differ from previous versions.
