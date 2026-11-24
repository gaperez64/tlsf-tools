# Preprocessor benchmarks

Build the research tools, then compare Acacia with and without preprocessing:

```sh
scripts/benchgraph.py \
    --corpus ../benchmarks/tlsf \
    --tlsfcompose build-oxidd/tlsfcompose \
    --solver ../acacia-bonsai/build_best_decomp_mona/src/acacia-bonsai \
    --out BENCHGRAPH.md \
    --data benchgraph.tsv \
    --timeout 10 --mem-gb 6
```

Use `--from-data benchgraph.tsv` to render saved results and repeated
`--compose-extra-arg` options to compare preprocessing variants.
