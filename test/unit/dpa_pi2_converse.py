"""Bounded research search for the general Pi_2 converse (issue #80).

Run manually; this does not enable general admission or replace a proof:
  python3 test/unit/dpa_pi2_converse.py /path/to/dpa_equivalence --output /tmp/pi2
The executable must be built from this checkout. It compares both inclusions
with Spot, writes a witness on mismatch, and uses allow_unproved explicitly.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random
import resource
import subprocess
import time


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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-size", type=int, default=6, choices=range(1, 7))
    parser.add_argument("--random-count", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=80002931)
    parser.add_argument("--timeout", type=float, default=3)
    args = parser.parse_args()
    if args.random_count < 0 or args.timeout <= 0:
        parser.error("random-count must be nonnegative and timeout must be positive")
    exe = args.executable.resolve(strict=True)
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    small, deep = formulas(args.max_size, args.random_count, args.seed)
    corpus = list(dict.fromkeys(small + deep))
    data = "\n".join(corpus) + "\n"
    (out / "formulas.ltl").write_text(data)
    result = {"small_and_targeted": len(small), "deep": len(deep),
              "total": len(corpus), "equivalent": 0, "declined": [],
              "timeout": [], "failures": [], "seed": args.seed,
              "corpus_sha256": hashlib.sha256(data.encode()).hexdigest()}
    start = time.monotonic()

    def save():
        result["elapsed_s"] = round(time.monotonic() - start, 3)
        (out / "results.json").write_text(json.dumps(result, indent=2) + "\n")

    def check(fs):
        batch = out / "current-batch.ltl"
        batch.write_text("\n".join(fs) + "\n")
        try:
            run = subprocess.run([str(exe), str(batch), "--allow-unproved"],
                                 cwd=out, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE,
                                 timeout=max(args.timeout, min(30, args.timeout * len(fs))))
        except subprocess.TimeoutExpired:
            if len(fs) == 1:
                result["timeout"].extend(fs)
                return
        else:
            if run.returncode == 0:
                result["equivalent"] += len(fs)
                return
            if len(fs) == 1:
                if run.returncode == 77:
                    result["declined"].extend(fs)
                    return
                result["failures"].append({"formula": fs[0], "returncode": run.returncode,
                                           "stderr": run.stderr})
                save()
                raise RuntimeError(f"equivalence harness failed: {fs[0]}\n{run.stderr}")
        # Isolate bounded skips and mismatches without hiding later formulas.
        middle = len(fs) // 2
        check(fs[:middle])
        check(fs[middle:])

    for i in range(0, len(corpus), 128):
        check(corpus[i:i + 128])
        save()
        if i % 1024 == 0:
            print(f"{result['equivalent']}/{len(corpus)} equivalent", flush=True)
    print(json.dumps(result, indent=2))
    return 2 if result["declined"] or result["timeout"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
