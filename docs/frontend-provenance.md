# Frontend expansion provenance

`tlsf2tlsf --provenance-out instance.json source.tlsf` writes expanded basic
TLSF to stdout (or `--output`) and provenance JSON separately. Consumers must
check `schema` (`tlsf-tools.frontend-provenance.v1`) and `format_version`.
`source_sha256` hashes exact input bytes, including whitespace/comments;
`parameters` and expanded records reflect `--param NAME=VALUE` overrides.

## Signals and conjuncts

A signal's direction and `declaration_id` (for example `input:2`) identify its
source declaration order within INPUTS or OUTPUTS. Expanded members share that
ID and record concrete `index_tuple`, resolved `bounds`, and `width`.
`dimensions` counts declared bus axes; the parser supports one. A flattened
grid therefore has one signal axis even when its formulas have two bindings.

`index_role: representation-bit` covers explicitly typed enum buses and
structurally proved floor(log2(x)) halving recurrences with bit-width wrappers
(`width_kind: proved-logarithmic-encoding`). The proof checks AST operators and
recursion, never names. Other computed widths are `undetermined`, retaining the
original bound in `width_expression`. `element` means a declared bus position;
consumers must prove any symmetry or further encoding role before lifting.

`width_parameter_ids` lists one-based `parameters` IDs in declaration order
from the original lower/upper bus-bound ASTs; scalars have none. Definition
calls follow only formals used by the body. Recursive visits, unknown names,
unsupported nodes, or traversal beyond the depth limit make
`width_binding_complete` false and the list partial. Decline incomplete
bindings before inferring an `element` owner's axis, and reject unknown/duplicate
IDs. Proved `representation-bit` roles stay unowned even with incomplete
recursive dependence. Width dependence does not prove ownership; decline
`undetermined` roles. Display-only `width_expression` must never supply an owner.

Each `conjuncts` entry contains its block, one-based formula ordinal,
`source_node_id`, zero-based `generated_position` within that formula, concrete
integer generator `bindings`, expanded formula, and exact mentioned signal
names. AST preorder assigns node IDs before substitution/definition expansion,
so they survive signal renaming, basename changes, and parameter overrides.
`source_formula_id` is `BLOCK:ordinal`; combine it with `source_node_id` to
align instances. Top-level conjunctions and those directly under top-level G
are split, retaining true terms for a complete inventory. Consumers must check
uniqueness of (`source_formula_id`, `generated_position`), including temporal
ranges and repeated calls; the pair survives signal renaming and filename changes.

Non-integer generator elements make integer bindings incomplete and set
`ambiguous`. Unresolved formula references also mark their conjunct ambiguous;
duplicate expanded names set the flag even across distinct declarations.
Decline structural lifting in all these cases and independently check signal
name uniqueness.

## Native monitor linkage

The GR(1) reducer matches monitors to unique source conjuncts by canonical text
or native formula equivalence. `source_origin_metadata.available` requires a
valid frontend record and one unique origin per monitor; `provenance_source`
is then `frontend`. Unavailable/ambiguous metadata uses `suffix-heuristic`,
which generic lifting must reject. Metadata decisions do not affect the AIG.
The pipeline retains the source snapshot, its SHA-256, and frontend provenance.

`construction_formula` and reported `conjunct` describe the formula passed to
monitor construction, before matching. The reducer independently parses
`source_conjuncts[].normalized_formula`, wrapping REQUIRE/ASSERT in `G`; both
strings use source signal names. Unique matches receive `source_binding`
(`source_formula_id`, `generated_position`, `source_node_id`); otherwise
`source_origin` is null and `source_binding` absent.

Exact linkage requires a unique conjunct key, identical binding/origin/conjunct
records, and equal `construction_formula`/`normalized_formula`. Decline missing,
inconsistent, or merely equivalent formulas. This catches joint origin/binding
swaps between equal-support siblings with different construction formulas.
Indistinguishable formulas require independent structural linkage or a decline.

## Monitor game symbol namespace

Expanded environment inputs are `uncontrollable_i<k>` and system outputs
`controllable_o<k>`, using zero-based expanded declaration order within each
role. Canonical structural names keep TLSF spelling (including legal `@` and
apostrophes) from changing game bytes or colliding with monitor latches. Role
prefixes are disjoint; internal symbols use neither.

Save the reduction API's symbol-map JSON beside the AIG as `game.aag.symbols`.
It binds ordered canonical-to-TLSF pairs to the exact game SHA-256.
`tlsfcertcheck --emit-controller` validates it before restoring original names;
keep it beside the game for controller export. Provenance records both TLSF
`name` and canonical `game_symbol`.
