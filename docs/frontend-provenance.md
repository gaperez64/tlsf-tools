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

`width_parameter_ids` lists the one-based IDs in `parameters`, in declaration
order, used by the original lower and upper bus-bound ASTs. Scalar signals
have an empty list. A definition call follows only formals referenced by its
body; unused actual arguments do not contribute dependencies. The field is a
partial list when `width_binding_complete` is false. Recursive definition
visits, unknown names, unsupported width nodes, and traversal beyond the
depth limit set that flag to false. Consumers must decline an incomplete
binding before inferring an `element` owner's parameter axis, and must reject
unknown or duplicate IDs. A separately proved `representation-bit` role stays
unowned even if recursive width dependence is incomplete. Width dependence
alone does not establish client ownership; `undetermined` roles must be
declined. `width_expression` is display text and must never supply an owner.

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

The native reducer records `construction_formula` as canonical text of the
conjunct passed to monitor construction, before source matching. It
independently parses each frontend conjunct into
`source_conjuncts[].normalized_formula`, adding the required outer `G` for
REQUIRE and ASSERT blocks. These two strings use the same source signal names.
The reported `conjunct` can differ after Spot simplifies the monitor formula
(for example, implication to disjunction). On a unique frontend match, the
monitor also receives `source_binding`: the claimed `source_formula_id`,
`generated_position`, and `source_node_id`. Otherwise `source_origin` is null
and `source_binding` is absent. A consumer that needs exact linkage must
require a unique source conjunct key, equality of `source_binding` with both
`source_origin` and that conjunct, and equality of `construction_formula` with
its `normalized_formula`. It must decline missing, inconsistent, or merely
equivalent formulas. This comparison catches a joint swap of `source_origin`
and `source_binding` between equal-support sibling monitors whose construction
formulas differ. Siblings with indistinguishable construction formulas need
independent structural linkage or must be declined.

## Monitor game symbol namespace

`gr1_monitor_game.py` assigns expanded environment inputs
`uncontrollable_i<k>` and system outputs `controllable_o<k>`, where `k` is
the zero-based order within that role's expanded declarations. The lowered
LTL is tokenized according to the TLSF identifier alphabet, then its complete
AP tokens are renamed before Spot parses it. Thus every AP in Spot, the AIG,
policies, and certificates has a canonical structural name. TLSF spelling
cannot change the game bytes or collide with monitor latches; the two role
prefixes remain disjoint and internal symbols use neither prefix.

For an AIG written with `--output game.aag`, the builder also writes
`game.aag.symbols`. This map contains the exact game SHA-256 and ordered
canonical-to-TLSF signal pairs. `tlsfcertcheck --emit-controller` validates
that map against the game before restoring the original input and output
names. Keep the map next to the game when exporting a controller. Provenance
JSON retains the TLSF `name` and records the canonical `game_symbol` for each
signal. `verify_strategy_explicit.py` accepts standalone raw TLSF output
names and older game-prefixed outputs by checking the complete interface.
Game AIG symbol bytes differ from previous versions.
