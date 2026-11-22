# Frontend provenance

`tlsf2tlsf --provenance-out instance.json source.tlsf` writes basic TLSF to
stdout (or `--output`) and JSON separately. Check `schema`
(`tlsf-tools.frontend-provenance.v1`) and `format_version`. `source_sha256`
hashes exact input bytes; `parameters` and expanded records include overrides.

## Signals and conjuncts

`declaration_id` (such as `input:2`) identifies declaration order within each
direction. Expanded members share it and record `index_tuple`, resolved
`bounds`, and `width`. `dimensions` counts bus axes; the parser supports one.

`index_role: representation-bit` denotes enum buses or structurally proved
logarithmic encodings (`width_kind: proved-logarithmic-encoding`). Other
computed widths are `undetermined`; `element` means a declared bus position.
Neither width dependence nor `element` proves ownership or symmetry.

`width_parameter_ids` lists one-based parameter IDs from the source bound
ASTs. Unknown/recursive/unsupported dependencies or depth exhaustion make
`width_binding_complete` false and the list partial. Decline incomplete element
bindings, unknown/duplicate IDs and undetermined roles. Representation bits
stay unowned; `width_expression` is display text.

Conjunct records contain block, one-based formula ordinal, `source_node_id`,
zero-based `generated_position`, integer generator `bindings`, expanded formula
and mentioned signals. Preorder node IDs precede expansion.
`source_formula_id` is `BLOCK:ordinal`; combine it with `source_node_id` to
align instances across parameter overrides and renaming. Top-level conjunctions
and those directly under top-level G are split, including true terms.
Require unique (`source_formula_id`, `generated_position`) pairs.

Non-integer generator elements, unresolved formula references and duplicate
expanded names set `ambiguous`. Decline structural lifting in those cases and
check signal-name uniqueness independently.

## Native monitor linkage

The GR(1) reducer matches monitors to unique source conjuncts by canonical text
or formula equivalence. Valid records with one origin per monitor set
`source_origin_metadata.available` and `provenance_source: frontend`.
Unavailable/ambiguous origins use `suffix-heuristic`, which generic lifting
must reject. The pipeline retains source bytes, SHA-256 and provenance.

`construction_formula` and `conjunct` describe the monitor's construction input.
The reducer parses `source_conjuncts[].normalized_formula`, wrapping
REQUIRE/ASSERT in G; both strings use source signal names. Unique matches get
`source_binding` (`source_formula_id`, `generated_position`, `source_node_id`).
Otherwise `source_origin` is null and `source_binding` absent.

Exact linkage requires unique conjunct keys, identical binding/origin/conjunct
records, and equal construction/normalized formulas. Decline missing,
inconsistent or merely equivalent formulas. Indistinguishable formulas need
independent structural linkage.

## Monitor game symbol namespace

Expanded inputs use `uncontrollable_i<k>` and outputs `controllable_o<k>` in
zero-based declaration order within each role. Internal symbols use neither
prefix. TLSF spelling therefore cannot collide with monitor latch names.

Save the reduction API's symbol map beside the AIG as `game.aag.symbols`.
It binds ordered canonical-to-TLSF pairs to the game's SHA-256.
`tlsfcertcheck --emit-controller` validates it before restoring original names.
Provenance records both TLSF `name` and canonical `game_symbol`.
