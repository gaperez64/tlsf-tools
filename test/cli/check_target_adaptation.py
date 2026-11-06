"""Each occurrence gets exactly one timing shift, including shared leaves."""
import subprocess
import sys


def convert(source):
    result = subprocess.run([sys.argv[1]], input=source, text=True,
                            capture_output=True, check=True)
    return result.stdout


# The reference spells out each intended shift and uses matching timing frames,
# so it never calls the adaptation rewriter. Expansion/printing remain shared.
cases = [
    ("G[0:2] o", "G[0:2](X o)"),
    ("F[1:3] o", "F[1:3](X o)"),
    ("G[0:0] o", "G[0:0](X o)"),
    ("X[0] o", "X[0](X o)"),
    ("G[0:2](o || i)", "G[0:2](X o || i)"),
    ("F[1:3] !o", "F[1:3] !(X o)"),
    ("X[2](o || i)", "X[2](X o || i)"),
    ("G[0:2] F[1:3](o || i)", "G[0:2] F[1:3](X o || i)"),
    ("d && d", "d && d"),
    ("repeat(!o)", "repeat(!(X o))"),
    ("G[0:2] repeat(o)", "G[0:2] repeat(X o)"),
    ("strip(G(o || i))", "strip(G(X o || i))"),
    ("choose(0)", "choose(0)"),
    ("choose(1)", "choose(1)"),
    ("&&[k IN {0,1}] (o || i)", "&&[k IN {0,1}] (X o || i)"),
    ("||[0 <= k <= 1] !o", "||[0 <= k <= 1] !(X o)"),
    ("&&[k IN {0,1}] (ob[k] || ib[k])",
     "&&[k IN {0,1}] (X ob[k] || ib[k])"),
    ("||[k IN {0,1}] element(k)", "||[k IN {0,1}] element(k)"),
    ("&&[f IN {o || i, !o}] f", "&&[f IN {X o || i, !(X o)}] f"),
]
roles = ["INITIALLY", "REQUIRE", "ASSUMPTIONS", "PRESET", "ASSERT",
         "GUARANTEES"]
checks = 0
for semantics in ("Mealy", "Moore", "Strict,Mealy", "Strict,Moore"):
    moore = "Moore" in semantics
    native = "Moore" if moore else "Mealy"
    target = "Mealy" if moore else "Moore"
    # Reverse the declarations too: o/ob are the shifted inputs for Moore.
    declarations = ("INPUTS { o; ob[2]; } OUTPUTS { i; ib[2]; }" if moore
                    else "INPUTS { i; ib[2]; } OUTPUTS { o; ob[2]; }")

    def source(formula, sections, reference):
        atom = "X o" if reference else "o"
        bit = "X ob[k]" if reference else "ob[k]"
        return (f"INFO {{ SEMANTICS: {semantics} "
                f"TARGET: {native if reference else target} }} "
                f"GLOBAL {{ DEFINITIONS {{ d = {atom} || i; "
                f"repeat(x) = x && X x; element(k) = {bit} || ib[k]; "
                f"strip(f) = f ~ G x : x otherwise : false; "
                f"choose(n) = n == 0 : d otherwise : !({atom}); }} }} "
                f"MAIN {{ {declarations} " +
                " ".join(f"{role} {{ {formula}; }}" for role in sections) + " }")

    for formula, expected in cases:
        for sections in [[role] for role in roles] + [roles]:
            actual = convert(source(formula, sections, False))
            reference = convert(source(expected, sections, True))
            assert actual == reference, (semantics, sections, formula,
                                         actual, reference)
            checks += 1
print(f"{checks} target-adaptation comparisons passed")
