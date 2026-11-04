"""Bounded Pi_2 corpus search using kernel-checked translation validation.

Each admitted completed automaton is checked by the Lean validator; unsupported
constructions and deadlines remain unknown. This does not prove universal C
refinement or promote admission. All artifacts must be below build-sprint.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random


def formulas(max_size, random_count, seed):
    # Exhaustive NNF grammar by AST node count over two positive literals.
    # C ::= a | b | X C | F C | C "&" C | C "|" C | C U C | C M C
    # P ::= C | X P | G P | P "&" P | P "|" P | P R P | P W P
    co = {1: {"a", "b"}}
    pi = {1: set(co[1])}
    for n in range(2, max_size + 1):
        co[n], pi[n] = set(), set()
        for x in co[n - 1]:
            for op in ("X", "F"):
                co[n].add(f"{op}({x})")
        for x in pi[n - 1]:
            for op in ("X", "G"):
                pi[n].add(f"{op}({x})")
        for k in range(1, n - 1):
            for grammar, operators in ((co, ("&", "|", "U", "M")),
                                       (pi, ("&", "|", "R", "W"))):
                for x, y in itertools.product(grammar[k], grammar[n - 1 - k]):
                    for op in operators:
                        if op in ("&", "|") and x > y:
                            continue
                        grammar[n].add(f"({x} {op} {y})")
        pi[n].update(co[n])
    small = []
    for n in range(1, max_size + 1):
        # Direct safety/co-safety are already proved. Keep mixed components.
        small.extend(sorted(f for f in pi[n] - co[n]
                            if any(op in f for op in ("F(", " U ", " M "))))
    windows = ["a", "!a", "X a", "X X a", "(a & X b)",
               "(X b & X X c)", "(a | X b)"]
    protectors = ["F({b})", "(a U ({b}))", "(a M ({b}))",
                  "(({b}) U a)", "(({b}) M a)"]
    for b, template in itertools.product(windows, protectors):
        h = template.format(b=b)
        small.extend([
            f"G({h})", f"G(a -> {h})", f"G(X({h}) | X X b)",
            f"G(({h} & X X b) | F c)", f"G((X X b & {h}) | X F c)",
            f"G(({h} | X X b) & F c)", f"G(({h} | X({h})) & X X b)",
            f"G(F(a & X b) | X({h}))", f"(({h}) R (b U X c))",
            f"(({h}) W (b M X c))",
        ])
    small.extend(["G F(a & X b)", "G(a -> F(X b & X X c))",
                  "G(F(a | (a & X F b)) | X F b)"])
    rng = random.Random(seed)

    def generate(n, cosafety=False):
        if n <= 1:
            return rng.choice(["a", "b", "c", "!a", "!b", "!c"])
        if n == 2 or rng.random() < 0.47:
            op = rng.choice(["X", "X", "F"] if cosafety else ["X", "X", "G"])
            return f"{op}({generate(n - 1, cosafety)})"
        if not cosafety and rng.random() < 0.2:
            return generate(n, True)
        k = rng.randint(1, n - 2)
        op = rng.choice(["&", "|", "U", "M"] if cosafety else ["&", "|", "R", "W"])
        return f"({generate(k, cosafety)} {op} {generate(n - 1 - k, cosafety)})"

    deep = []
    for i in range(random_count):
        n = rng.randint(7, 18)
        deep.append(f"G({generate(n - 1, True)})" if i % 2 == 0 else generate(n))
    # Negation invokes the C constructor's NNF dual, covering Sigma_2 too.
    def with_duals(fs):
        return list(dict.fromkeys(s for f in fs for s in (f, f"!({f})")))
    return with_duals(small), with_duals(deep)


def main():
    from reference import parse, prefix, atoms
    from translation_validate import ROOT, SCRATCH, build_validator, validate_one, request
    import os

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-size", type=int, default=6, choices=range(1, 7))
    parser.add_argument("--random-count", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=80002931)
    parser.add_argument("--timeout", type=float, default=17)
    args = parser.parse_args()
    if args.random_count < 0 or args.timeout <= 0:
        parser.error("random-count must be nonnegative and timeout must be positive")
    out = args.output.resolve()
    assert out.is_relative_to(ROOT / "build-sprint"), "scratch must be under build-sprint"
    out.mkdir(parents=True, exist_ok=True)
    SCRATCH.mkdir(parents=True, exist_ok=True)
    os.environ.update(LEAN_NUM_THREADS="1", LEAN_STACK_SIZE_KB="2048", LEAN_MAIN_USE_THREAD="0",
                      TMPDIR=str(ROOT / "build-sprint/tmp"), CARGO_BUILD_JOBS="1")
    validator, version, _ = build_validator()
    small, deep = formulas(args.max_size, args.random_count, args.seed)
    corpus = list(dict.fromkeys(small + deep))
    data = "\n".join(corpus) + "\n"
    (out / "formulas.ltl").write_text(data)
    result = {"validated": 0, "unknown": [], "failures": [], "seed": args.seed,
              "lean": version, "corpus_sha256": hashlib.sha256(data.encode()).hexdigest()}
    for formula in corpus:
        tree = parse(formula)
        text = request("parity", "general", sorted(atoms(tree)), prefix(tree))
        status, reason, digest = validate_one(args.build.resolve(), validator, text, args.timeout)
        if status == "pass":
            result["validated"] += 1
        elif status in ("not_admitted", "timeout"):
            result["unknown"].append({"formula": formula, "reason": reason})
        else:
            result["failures"].append({"formula": formula, "reason": reason})
        (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: len(v) if isinstance(v, list) else v for k, v in result.items()}, indent=2))
    return 1 if result["failures"] else 2 if result["unknown"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
