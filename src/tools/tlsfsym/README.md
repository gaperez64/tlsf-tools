# tlsfsym

Census declared index permutations verified on the whole objective.
This optional research tool is built with `-Dresearch_tools=true`.

From the repository root, after the [source-build prerequisites](../../../README.md#build)
including initialized OxiDD:

```sh
meson setup build-research -Dresearch_tools=true --buildtype=release
CARGO_BUILD_JOBS=1 meson compile -C build-research -j 1
build-research/tlsfsym spec.tlsf  # verified index generators (JSON)
```

`tlsfsym FILE` emits one JSON object. It uses `tlsf_convert(text, "Mealy")`'s
expanded whole infinite-word objective and input/output partition, matching
Acacia's native frontend, including strict semantics and target adaptation.
`families` retains declaration provenance; each `ranges` entry groups families
with identical bounds and applies each index permutation simultaneously to all
of them. A candidate's `image[i]` is the image of index `lo+i`. Scalars and
families on other ranges remain fixed. AP maps must be bijections preserving
the input/output partition. Adjacent transpositions precede the rotation; the
rotation is also emitted for a singleton (identity) or two-element range.

The census is a lower bound: different concrete bounds are not coupled,
families on the same range are only permuted together, enum families permute
encoding bits, and canonical inequality is inconclusive.

The tool hash-conses the converted AST, flattening AND/OR and sorting their
children by node ID, and sorting the two EQUIV children. The AST has no XOR
operator; negated EQUIV uses the same sorted children. Other operators retain
their operand order. Hash collisions are resolved by full structural equality.
Equality of the original and renamed root IDs therefore proves symmetry using
only associative/commutative identities. Unequal IDs are inconclusive: the
tool may miss semantic symmetries. `verified_group` is `symmetric` if every
adjacent transposition verifies, otherwise `cyclic` if the rotation verifies,
otherwise `none`; this does not claim to find the largest subgroup.

Unverified candidates include a reason. Conversion failures (including
unresolved parameters or finite semantics) return nonzero with an `unverified`
JSON object, the library diagnostic, no candidates, and a null summary because
families could not be recovered. Unsupported objective nodes or syntax deeper
than 1024 leave candidates unverified. `summary` gives family/range counts and
range sizes; `wall_seconds` measures elapsed wall time from CLI entry through
census construction, excluding final JSON serialization/output. No automaton
construction or solving runs.
