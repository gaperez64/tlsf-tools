# tlsfsym

Census declared index permutations verified on the whole objective.
This optional research tool is built with `-Dresearch_tools=true`.

From the repository root:

```sh
meson setup build-research -Dresearch_tools=true --buildtype=release
CARGO_BUILD_JOBS=2 meson compile -C build-research -j 2
build-research/tlsfsym spec.tlsf  # verified index generators (JSON)
```

Detection is available in every library build through `tlsf/symmetry.h`:
call `tlsf_symmetry_detect(conversion, &result)` on a `TlsfConversionResult`
and free the result with `tlsf_symmetry_result_free`. `generators` contains
only verified nonidentity full AP permutations, indexed into the conversion's
inputs followed by outputs, tagged by range and kind. Ranges also carry verdicts
and candidate diagnostics for this CLI. The result owns its storage independently
of the conversion; allocation failures return `TLSF_SYMMETRY_NO_MEMORY` with no
result. Detection has no global state and performs no conversion itself.

`tlsfsym FILE` emits one JSON object. It uses `tlsf_convert(text, "Mealy")`'s
expanded whole infinite-word objective and input/output partition, matching
Acacia's native frontend, including strict semantics and target adaptation.
`families` retains declaration provenance; each `ranges` entry groups families
with identical bounds and applies each index permutation simultaneously to all
of them. A candidate's `image[i]` is the image of index `lo+i`. Scalars and
families on other ranges remain fixed. AP maps must be bijections preserving
the input/output partition. Adjacent transpositions precede the rotation,
including for a two-element range. Ranges with fewer than two indices report
`verified_group: "none"` and an empty `candidates` array, with no generators.
The identity is never returned as a generator for any range.

The census is a lower bound: different concrete bounds are not coupled,
families on the same range are only permuted together, enum families permute
encoding bits, and canonical inequality is inconclusive.

Excluding the 27 inputs supported only by singleton ranges corrects the
SYNTCOMP26 symmetric-input count from 154 to 127.

The library hash-conses the converted AST, flattening AND/OR and sorting their
children by node ID, and sorting the two EQUIV children. The AST has no XOR
operator; negated EQUIV uses the same sorted children. Other operators retain
their operand order. Hash collisions are resolved by full structural equality.
Equality of the original and renamed root IDs therefore proves symmetry using
only associative/commutative identities. Unequal IDs are inconclusive: the
tool may miss semantic symmetries. For ranges with at least two indices,
`verified_group` is `symmetric` if every adjacent transposition verifies,
otherwise `cyclic` if the rotation verifies, otherwise `none`; this does not
claim to find the largest subgroup.

Unverified candidates include a reason. Conversion failures (including
unresolved parameters or finite semantics) return nonzero with an `unverified`
JSON object, the library diagnostic, no candidates, and a null summary because
families could not be recovered. Unsupported objective nodes or syntax deeper
than 1024 leave candidates unverified. `summary` gives family/range counts and
range sizes; `wall_seconds` measures elapsed wall time from CLI entry through
census construction, excluding final JSON serialization/output. No automaton
construction or solving runs.
