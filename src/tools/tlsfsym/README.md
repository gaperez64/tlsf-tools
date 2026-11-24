# tlsfsym

Find declared-index permutations verified on the whole infinite-word
objective returned by `tlsf_convert(text, "Mealy")`, including strict
semantics and target adaptation.
After the [build prerequisites](../../../README.md#build):

```sh
meson setup build-research -Dresearch_tools=true --buildtype=release
CARGO_BUILD_JOBS=1 meson compile -C build-research -j 1
build-research/tlsfsym spec.tlsf  # verified index generators (JSON)
```

`tlsfsym FILE` emits one JSON object. `families` records declarations;
`ranges` groups families with identical bounds and permutes their indices
together. `image[i]` maps index `lo+i`; other ranges and scalars stay fixed.
AP maps preserve the input/output partition. Adjacent transpositions precede
the rotation, including singleton/two-element rotations.

Verification compares canonical ASTs using AND/OR associativity/commutativity
and EQUIV commutativity. Unequal ASTs are inconclusive. `verified_group` is
`symmetric` if all adjacent transpositions verify, otherwise `cyclic` if the
rotation verifies, otherwise `none`. This is a lower bound: it does not couple
different bounds, independently permute same-range families, or find the
largest subgroup. Enum families permute encoding bits.

Conversion failures, including unresolved parameters and finite semantics,
exit nonzero with an `unverified` object, diagnostic, no candidates and null
summary. Unsupported nodes or syntax deeper than 1024 leave candidates
unverified with a reason. `summary` counts families/ranges and their sizes;
`wall_seconds` excludes final JSON output. The tool constructs no automaton
and runs no solver.
