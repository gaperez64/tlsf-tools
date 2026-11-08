"""TLSF v1.1 §§4.1–4.8 regressions, including the successive #110 reviews."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

binary = sys.argv[1]
cases = []


def spec(body, definitions="", signals=""):
    return ("INFO { SEMANTICS: Finite,Mealy; TARGET: Mealy; } "
            f"GLOBAL {{ {definitions} }} MAIN {{ INPUTS {{ i; }} "
            f"OUTPUTS {{ o; {signals} }} GUARANTEES {{ {body}; }} }}")


def pair(name, body, direct, definitions="", signals=""):
    cases.append({"name": name, "source": spec(body, definitions, signals),
                  "direct": spec(direct, definitions, signals)})


def reject(name, body, category="typing", definitions="", signals=""):
    cases.append({"name": name, "source": spec(body, definitions, signals),
                  "diagnostic": f"expand: {category}:"})


# §4.7 lexical binding; §4.8 desugaring, including the #110 issue verbatim.
pair("issue110", "&&[f IN CUP[k IN {1,2}] {X[k] o}] f",
     "&&[f IN {X[1] o, X[2] o}] f")
pair("dedup110", "&&[f IN CUP[k IN {1,2}] {X[k] o, X[1] o}] f",
     "&&[f IN {X[1] o, X[2] o}] f")
pair("shadow", "&&[f IN CUP[k IN {1,2}] {&&[k IN {3}] X[k] o}] f", "X[3] o")
pair("shadow-domain", "&&[f IN CUP[k IN {1,2}] {&&[k IN {k+1}] X[k] o}] f",
     "X[2] o && X[3] o")
pair("formula-shadow", "&&[f IN {X o}] &&[f IN {X X o}] f", "X X o")
for inner in ("||[k IN {3}] X[k] o", "X[+[k IN {3}] k] o",
              "X[*[k IN {3}] k] o",
              "&&[j IN CUP[k IN {3}] {X[k] o}] j",
              "&&[j IN CAP[k IN {3}] {X[k] o}] j"):
    pair("shadow-all-binders", "&&[f IN CUP[k IN {1,2}] {" + inner + "}] f", "X[3] o")
for temporal, strong in (("F", False), ("G", False), ("F", True), ("G", True)):
    bounded = temporal + ("[!k:k] o" if strong else "[k:k] o")
    direct = "X[!1] o && X[!2] o" if strong else "X o && X X o"
    pair("closed-range", "&&[f IN CUP[k IN {1,2}] {" + bounded + "}] f", direct)
pair("later-domains", "&&[f IN CUP[k IN {1}, j IN {k,k+1}] {X[j] o}] f",
     "X o && X X o")
pair("nested", "&&[s IN CUP[k IN {1,2}] {{X[k] o}}] &&[f IN s] f",
     "X o && X X o")
pair("actual", "&&[k IN {1,2}] delay(k)", "X o && X X o",
     "DEFINITIONS { delay(x) = X[x] o; }")
pair("actual-capture", "&&[k IN {1}] delay(k)", "X o",
     "DEFINITIONS { delay(x) = &&[k IN {2}] X[x] o; }")
pair("bus-actual", "&&[b IN {bus}] use(b)", "bus[0]",
     "DEFINITIONS { use(x) = x[0]; }", "bus[2];")
pair("sizeof-actual", "&&[b IN {bus}] use(b)", "X[2] o",
     "DEFINITIONS { use(x) = X[SIZEOF x] o; }", "bus[2];")
pair("stored-bus-actual", "&&[s IN {{bus}}] &&[b IN s] use(b)", "bus[0]",
     "DEFINITIONS { use(x) = x[0]; }", "bus[2];")
pair("key-sugar", "SIZE {X[1] o, X o} == 2", "false")
pair("key-strong", "SIZE {X[1] o, X[!1] o} == 2", "true")
pair("key-definition", "SIZE {delay(1), X o} == 1", "true",
     "DEFINITIONS { delay(x) = X[x] o; }")
pair("key-bigop", "SIZE {&&[k IN {1,2}] X[k] o, X o && X X o} == 1", "true")
pair("key-range", "SIZE {F[1:2] o, X (o || X o)} == 1", "true")
pair("key-nested", "SIZE {{X[1] o}, {X o}} == 1", "true")
pair("key-nested-signal", "SIZE {{X[0] o}, {o}} == 1", "true")
pair("key-sum", "X[+[f IN {X[1] o, X o}] 1] o", "X o")
pair("key-difference", "&&[f IN ({X[1] o} (-) {X o})] false", "true")
pair("finite-next", "&&[f IN {X[1] true, X[!1] true}] f", "X true && X[!] true")
pair("finite-next-reversed", "&&[f IN {X[!1] true, X[1] true}] f", "X[!] true && X true")
pair("pattern", "&&[f IN CUP[k IN {1,2}] {X[k] o}] use(f)", "o && X o",
     "DEFINITIONS { use(x) = x ~ X p : p otherwise : false; }")
pair("guard-numeric", "delay(1)", "X[2] o",
     "DEFINITIONS { n(x) = x == 1 : 2 otherwise : 3; delay(x) = X[n(x)] o; }")
# §4.3 numeric equality does not coerce boolean results to numbers.
reject("boolean-numeric-clash", "f(true)", definitions=
       "DEFINITIONS { neg(x) = !x; f(y) = neg(y) == 0 : o otherwise : o; }")

# All syntactic positions are checked even when expansion would never visit.
for body in ("&&[k IN {1}] X[k] d", "&&[f IN CUP[k IN {1}] {X[k] d}] f",
             "SIZE (CUP[k IN {1}] {X[k] d}) == 1",
             "&&[k IN {1}] &&[f IN {&&[k IN {o}] X d}] f"):
    reject("hidden-definition", body, "scoping", "DEFINITIONS { d = k == 1 : true otherwise : false; }")
reject("hidden-error", "o", "scoping",
       "DEFINITIONS { d = k == 1 : X[missing] o otherwise : o; }")
reject("unknown", "missing", "scoping")
reject("outside-body", "(&&[k IN {1}] o) && X[k] o", "scoping")
reject("domain-not-bound", "&&[k IN {k}] o", "scoping")
reject("argument-outside", "x", "scoping", "DEFINITIONS { f(x) = x; }")
reject("dead-branch", "o", "scoping", "DEFINITIONS { d = 1 == 1 : o otherwise : missing; }")

# §§4.3–4.6: loop/pattern freshness; lexical function argument shadowing.
for declaration, signals in (("", "k;"), ("", "k[2];"),
        ("PARAMETERS { k = 1; }", ""), ("DEFINITIONS { k = 1; }", ""),
        ("DEFINITIONS { enum E = k: 0 other: 1; }", ""),
        ("DEFINITIONS { enum k = label: 0 other: 1; }", "")):
    for op in ("&&", "||", "+", "*", "CUP", "CAP"):
        body = f"{op}[k IN {{1,2}}] " + ("{o}" if op in ("CUP", "CAP") else
                                               "1" if op in ("+", "*") else "o")
        if op in ("CUP", "CAP"):
            body = f"SIZE ({body}) == 1"
        elif op in ("+", "*"):
            body = f"({body}) == 1"
        reject(f"fresh-{op}", body, definitions=declaration, signals=signals)
    # Put the function inside the same DEFINITIONS subsection, when present.
    extra = declaration.replace("DEFINITIONS {", "DEFINITIONS { f(k) = o;", 1)
    if extra == declaration:
        extra += " DEFINITIONS { f(k) = o; }"
    pair("shadow-argument", "f(1)", "o", definitions=extra, signals=signals)
    extra = declaration.replace("DEFINITIONS {", "DEFINITIONS { f(x) = x ~ X k : k otherwise : false;", 1)
    if extra == declaration:
        extra += " DEFINITIONS { f(x) = x ~ X k : k otherwise : false; }"
    reject("fresh-pattern", "o", definitions=extra, signals=signals)

for body in ("i[0]", "&&[k IN {1}] k[0]", "&&[k IN {1}] k",
             "X[SIZEOF i] o", "SIZE {1, o} == 2", "i == 1"):
    reject("category", body)
for body in ("label", "label IN {label}", "X[label] o", "i == label",
             "label == 1", "SIZE {label} == 1", "use(label)"):
    reject("enum-position", body, definitions=
           "DEFINITIONS { enum E = label: 0 other: 1; use(x) = x; }")
for body in ("&&[f IN {X[0] i}] use(f)", "use(X[0] i)"):
    reject("identifier-actual", body, definitions="DEFINITIONS { use(x) = X[SIZEOF x] o; }")

reviews = Path(__file__).with_name("scoping_110_reviews.json")
cases.extend(json.loads(reviews.read_text()))
for name, output in (("identity_sugar", "false\n"), ("identity_strength", "true\n"),
                     ("cup_overlap", "X o && X X o\n")):
    fixture = Path(__file__).parents[1] / "fixtures/scoping110" / (name + ".tlsf")
    cases.append({"name": name, "source": fixture.read_text(), "output": output})
# §4.6 lexical reading: shadowing globals preserves the SYNTCOMP examples.
for name in ("arbiter_pb_2_pe_", "arbiter_pb_3_pe_", "arbiter_pb_4_pe_",
             "arbiter_on_inpchange_pb_2_pe_"):
    original = Path(__file__).parents[1] / "fixtures/gr1_monitor_game" / (name + ".tlsf")
    renamed = Path(__file__).parents[1] / "fixtures/scoping110/monitor" / (name + ".tlsf")
    cases.append({"name": "original-" + name, "source": original.read_text(),
                  "direct": renamed.read_text()})

# Review110e: literal §4.8 spellings, including empty, zero and longer ranges,
# all tested as SIZE == 1 so a structurally wrong expansion cannot pass.
for temporal in ("F", "G"):
    op = "||" if temporal == "F" else "&&"
    for strong in (False, True):
        for lo, hi in ((2, 3), (1, 3), (0, 0), (0, 3), (1, 1), (3, 5), (3, 2)):
            nxt = "X[!]" if strong else "X"
            direct = "o"
            for _ in range(hi - lo):
                direct = f"(o {op} {nxt} ({direct}))"
            for _ in range(lo):
                direct = f"{nxt} ({direct})"
            if lo > hi:
                direct = "true" if temporal == "G" else "false"
            bounded = f"{temporal}[{'!' if strong else ''}{lo}:{hi}] o"
            pair("review110e-range", f"SIZE {{{bounded}, {direct}}} == 1", "true")
for expression in ("&&[k IN {2}] F[k:3] o", "range(2,3)", "range0"):
    pair("range-key-environments", f"SIZE {{{expression}, X X (o || X o)}} == 1", "true",
         "DEFINITIONS { range(x,y) = F[x:y] o; range0 = F[2:3] o; }")
pair("range-key-pattern-subject", "SIZE {pick(F[1:2] o), X o} == 1", "true",
     "DEFINITIONS { pick(x) = x ~ (X p || X X p) : X p otherwise : false; }")
# Strength remains distinct on finite words.
for temporal in ("F", "G"):
    pair("range-strength", f"SIZE {{{temporal}[1:3] o, {temporal}[!1:3] o}} == 2", "true")
# Bus indices embed into LTL at every set depth; stored syntax stays usable.
for body in ("SIZE {X[0] b[0], b[0]} == 1",
             "SIZE {b[0], X[0] b[0]} == 1",
             "SIZE {{X[0] b[0]}, {b[0]}} == 1",
             "SIZE {{{X[0] b[0]}}, {{b[0]}}} == 1",
             "&&[f IN ({X[0] b[0]} (-) {b[0]})] f",
             "&&[f IN ({b[0]} (-) {X[0] b[0]})] f",
             "SIZE ({{X[0] b[0]}} (-) {{b[0]}}) == 0",
             "X[0] b[0] IN {b[0]}"):
    pair("review110e-bus-key", body, "true", signals="b[1];")
pair("stored-bus-pattern", "&&[f IN {b[0], X[0] b[0]}] use(X f)", "b[0]",
     "DEFINITIONS { use(x) = x ~ X p : p otherwise : false; }", "b[1];")
# Resolved b_0 must survive numeric closing, direct binding, and further calls.
for element, direct in (("X p", "X b[0]"), ("p", "b[0]"), ("id(p)", "b[0]")):
    for definitions in ("", "b_0 = 9;"):
        pair("review110e-resolved-atom", "use(X b[0])", direct,
             "DEFINITIONS { " + definitions + " id(x) = x; "
             "use(x) = x ~ X p : &&[" + ("q" if definitions else "b_0") + " IN {1}] &&[f IN {" + element + "}] f "
             "otherwise : false; }", "b[1];")
# Arguments can shadow every global category, and use the actual's category.
for declaration, signals in (("", "k;"), ("", "k[2];"),
        ("PARAMETERS { k = 7; }", ""), ("DEFINITIONS { k = 7; }", ""),
        ("DEFINITIONS { enum E = k: 0 other: 1; }", ""),
        ("DEFINITIONS { enum k = label: 0 other: 1; }", "")):
    extra = declaration.replace("DEFINITIONS {", "DEFINITIONS { delay(k) = X[k] o;", 1)
    if extra == declaration:
        extra += " DEFINITIONS { delay(k) = X[k] o; }"
    pair("shadow-argument-category", "delay(2)", "X X o", extra, signals)
    extra = extra.replace("X[k] o", "k == 2 : o otherwise : false")
    pair("shadow-argument-enum-lookup", "delay(2)", "o", extra, signals)
    extra = extra.replace("k == 2 : o otherwise : false", "k[0]")
    pair("shadow-argument-bus", "delay(bus)", "bus[0]", extra, signals + " bus[1];")
    pair("shadow-argument-formula", "f(X o)", "X o",
         extra.replace("delay(k) = k[0]", "f(k) = k"), signals + " bus[1];")
reject("shadow-function-call", "f(1)", definitions="DEFINITIONS { f(f) = f(1); }")
reject("duplicate-arguments", "o", definitions="DEFINITIONS { f(k,k) = o; }")
for body in ("alias == label", "use(alias)", "use(bus(1))"):
    pair("enum-resolved-bus", body, "!b[0] && !b[1]",
         "DEFINITIONS { enum E = label: 00 other: 11; alias = b; "
         "bus(ignored) = b; use(x) = x == label; }", "b[2];")
# §4.4 widths: both orders, inequality, parameters, actuals, domain values,
# and unused/unselected bodies. The diagnostic must name the width failure.
for body in ("b == label", "label == b", "b != label", "use(b)",
             "&&[v IN {b}] use(v)", "&&[s IN {{b}}] &&[v IN s] use(v)"):
    for width in (1, 3):
        cases.append({"name": "review110e-enum-width", "source": spec(body,
            "PARAMETERS { N = " + str(width) + "; } DEFINITIONS { "
            "enum E = label: 00 other: 11; use(x) = x == label; }", "b[N];"),
            "diagnostic": "enum comparison width mismatch"})
    pair("enum-width-match", body, "!b[0] && !b[1]" if "!=" not in body else
         "!(!b[0] && !b[1])", "PARAMETERS { N = 2; } DEFINITIONS { "
         "enum E = label: 00 other: 11; use(x) = x == label; }", "b[N];")
for definition in ("unused = b == label;", "unused(x) = 1 == 1 : o otherwise : b == label;"):
    cases.append({"name": "enum-unused-width", "source": spec("o", "DEFINITIONS { "
        "enum E = label: 00 other: 11; " + definition + " }", "b[1];"),
        "diagnostic": "enum comparison width mismatch"})
cases.append({"name": "enum-mixed-width-domain", "source": spec(
    "&&[v IN {b,c}] use(v)", "DEFINITIONS { enum E = label: 00 other: 11; "
    "use(x) = x == label; }", "b[2]; c[1];"), "diagnostic": "enum comparison width mismatch"})
pair("mixed-width-bus-domain", "&&[v IN {b,c}] X[SIZEOF v] o", "X X o && X o", signals="b[2]; c[1];")
for width in (1, 3):
    cases.append({"name": "enum-width-override", "source": spec("use(b)",
        "PARAMETERS { N = 2; } DEFINITIONS { enum E = label: 00 other: 11; "
        "use(x) = x == label; }", "b[N];"), "args": ["--param", f"N={width}"],
        "diagnostic": "enum comparison width mismatch"})
# Review110f: keep declaration identity injective before any output or set key.
for signals in ("b[1]; b_0;", "b_0; b[1];", "b[1]; b_0[2];",
                "bus_name[12]; bus_name_11;", "b[2..3]; b_2;", "E b; b_0;"):
    for body in ("o", "b[0] && !b_0", "X[SIZE {b[0],b_0}] o",
                 "SIZE {b_0,b[0]} == 2", "SIZE {{b[0]},{b_0}} == 2",
                 "SIZE ({b[0]} (-) {b_0}) == 1"):
        if signals not in ("b[1]; b_0;", "b_0; b[1];", "E b; b_0;") and body != "o":
            continue
        cases.append({"name": "flattened-name-collision", "source": spec(body,
            "DEFINITIONS { enum E = label: 0 other: 1; }", signals),
            "diagnostic": "collides with flattened bus bit"})
for inputs, outputs in (("b[1];", "b_0;"), ("b_0;", "b[1];"),
                        ("b[1]; b_0;", "")):
    cases.append({"name": "flattened-input-output-collision", "source":
        "INFO { SEMANTICS: Mealy; TARGET: Mealy; } MAIN { INPUTS { " + inputs +
        " } OUTPUTS { " + outputs + " } GUARANTEE { true; } }",
        "diagnostic": "collides with flattened bus bit"})
for signals in ("b[1]; b_1;", "b[1]; b_00;", "b[1]; b_65536;",
                "b[1]; b_9999999999999999999999999999999;", "b[2..3]; b_0;",
                "b[2]; c_0;", "b[2]; b_2[1];"):
    pair("noncolliding-declarations", "o", "o", signals=signals)
for width, diagnostic in ((1, None), (2, "collides with flattened bus bit")):
    case = {"name": "collision-resolved-width", "source": spec("o",
        "PARAMETERS { N = 1; }", "b[N]; b_1;"), "args": ["--param", f"N={width}"]}
    case.update({"diagnostic": diagnostic} if diagnostic else {"output": "o\n"})
    cases.append(case)

# §4.3 embedding applies to recursive arguments, including set elements.
for actual in ("o", "b[0]", "true", "1 == 1", "!false", "X[0] o"):
    for base in ("x", "X x"):
        pair("recursive-formula-embedding", f"wrap({actual},1)",
             f"X ({actual})" if base == "x" else f"X X ({actual})",
             f"DEFINITIONS {{ wrap(x,n) = n == 0 : {base} otherwise : wrap(X x,n-1); }}",
             "b[1];")
pair("recursive-set-embedding", "&&[v IN wrap({o},2)] v", "X X o",
     "DEFINITIONS { wrap(s,n) = n == 0 : s otherwise : wrap(CUP[x IN s] {X x},n-1); }")
pair("recursive-boolean-embedding", "wrap(true,1)", "!(!true)",
     "DEFINITIONS { wrap(x,n) = n == 0 : !x otherwise : wrap(!x,n-1); }")
for body in ("n == 0 : X[x] o otherwise : wrap(X x,n-1)",
             "n == 0 : wrap(X x,n-1) otherwise : X[x] o",
             "n == 0 : X x otherwise : wrap(1,n-1)"):
    reject("recursive-boolean-or-numeric-violation", "wrap(true,1)",
           definitions=f"DEFINITIONS {{ wrap(x,n) = {body}; }}")

# §4.4 checks actual surviving bus values, independently of lexical shadowing.
enum_defs = "DEFINITIONS { enum E = label: 00 other: 11; use(x) = x == label; " \
            "pick(x) = x == 1 : c otherwise : b; shadow(v) = &&[v IN {c}] v == label; }"
for body in ("&&[v IN {b}] &&[v IN {c}] v == label", "shadow(b)", "use(pick(1))"):
    pair("width-lexical-and-selected-value", body, "!c[0] && !c[1]", enum_defs, "b[1]; c[2];")
pair("width-shadow-key", "SIZE {&&[v IN {b}] &&[v IN {c}] v == label, c == label} == 1",
     "true", enum_defs, "b[1]; c[2];")
for domain in ("({b,c} (-) {b})", "({b,c} (*) {c})", "({c} (*) {b,c})",
               "CAP[k IN {1}] ({b,c} (-) {b})", "pickset(1)"):
    definitions = enum_defs.replace("DEFINITIONS {", "DEFINITIONS { pickset(x) = x == 1 : {c} otherwise : {b,c};")
    for comparison in ("v == label", "use(v)"):
        pair("width-surviving-domain", f"&&[v IN {domain}] {comparison}",
             "!c[0] && !c[1]", definitions, "b[1]; c[2];")
    pair("width-nested-domain", f"&&[s IN {{{domain}}}] &&[v IN s] use(v)",
         "!c[0] && !c[1]", definitions, "b[1]; c[2];")
for body in ("&&[v IN {c}] &&[v IN {b}] use(v)", "use(pick(2))",
             "&&[v IN ({b,c} (-) {c})] use(v)", "&&[v IN ({b,c} (*) {b})] v == label",
             "&&[v IN {b,c}] use(v)"):
    cases.append({"name": "width-real-violation", "source": spec(body, enum_defs, "b[1]; c[2];"),
                  "diagnostic": "enum comparison width mismatch"})
pair("unrelated-set-width", "use(b)", "!b[0]",
     "DEFINITIONS { enum E = label: 0 other: 1; use(x) = SIZE {x,c} == 2 : x == label otherwise : false; }",
     "b[1]; c[2];")

# Resolved aliases supply the stored bus and every formula identity key.
for definition in ("alias = b;", "alias = second; second = b;",
                   "alias = choose(1); choose(x) = x == 1 : b otherwise : c;"):
    definitions = "DEFINITIONS { " + definition + " get(x) = x[0]; width(x) = SIZEOF x; id(x) = x; }"
    for body, direct in (("alias[0]", "b[0]"), ("X[SIZEOF alias] o", "X X o"),
                         ("X[width(alias)] o", "X X o"), ("get(alias)", "b[0]"),
                         ("id(alias[0])", "b[0]"), ("&&[v IN {alias}] v[0]", "b[0]"),
                         ("&&[v IN {alias[0]}] v", "b[0]"),
                         ("SIZE {alias,b} == 1", "true"),
                         ("SIZE {alias[0], b[0], X[0] alias[0]} == 1", "true"),
                         ("SIZE {{alias[0]}, {b[0]}} == 1", "true"),
                         ("SIZE ({alias} (-) {b}) == 0", "true"),
                         ("SIZE ({alias[0]} (-) {b[0]}) == 0", "true")):
        pair("bus-alias-resolution", body, direct, definitions, "b[2]; c[1];")
for actual in ("o", "1", "X o"):
    for body in ("alias[0]", "X[SIZEOF alias] o"):
        reject("nonbus-alias", body, definitions=f"DEFINITIONS {{ alias = {actual}; }}")

# §4.5 complete names: check the old buffer boundary, multi-digit bits and
# long identifiers through keys, stored elements, declarations and printers.
for length in (253, 254, 255, 256, 1024, 8193):
    bus = "b" * length
    bits = [f"{bus}[{i}]" for i in (0, 1, 10, 11)]
    signals = f"{bus}[12];"
    for body, direct in ((f"X[SIZE {{{','.join(bits)}}}] o", "X[4] o"),
                         (f"SIZE {{{bits[0]},{bits[0]},X[0] {bits[0]}}} == 1", "true"),
                         (f"SIZE {{{{{bits[0]}}},{{{bits[1]}}}}} == 2", "true"),
                         (f"SIZE ({{{bits[0]}}} (-) {{{bits[1]}}}) == 1", "true"),
                         (f"SIZE ({{{bits[0]}}} (*) {{{bits[1]}}}) == 0", "true"),
                         (f"X[+[v IN {{{bits[0]},{bits[1]}}}] 1] o", "X X o"),
                         (f"{bits[0]} && !{bits[1]}", f"{bus}_0 && !{bus}_1")):
        # The direct spelling declares the exact full flattened names.
        cases.append({"name": "complete-bus-names", "source": spec(body, signals=signals),
                      "direct": spec(direct, signals=f"{bus}_0; {bus}_1;")})
    for suffix, collision in (("_0", True), ("_11", True), ("_12", False),
                              ("_00", False), ("_999999999999999999999", False)):
        c = {"name": "complete-name-collision", "source": spec("o", signals=signals + bus + suffix + ";")}
        c.update({"diagnostic": "collides with flattened bus bit"} if collision else {"output": "o\n"})
        cases.append(c)
    for fmt in ("ltl", "ltlxba", "latex"):
        cases.append({"name": "complete-name-printer", "source": spec(f"{bits[0]} && !{bits[1]}", signals=signals),
                      "direct": spec(f"{bus}_0 && !{bus}_1", signals=f"{bus}_0; {bus}_1;"),
                      "args": ["--format", fmt]})

# §4.6: recursive argument types belong to each call, including mutual calls.
for actual in ("1", "o", "true", "b", "{1}", "{{o}}"):
    for recursive in ("{x}", "1", "o", "b", "X o", "{{x}}"):
        for mutual in (False, True):
            definitions = ("DEFINITIONS { f(x,n) = n == 0 : o otherwise : " +
                           ("g(" if mutual else "f(") + recursive + ",n-1); " +
                           ("g(y,n) = f(y,n); " if mutual else "") + "}")
            pair("per-call-recursive-types", f"f({actual},3)", "o", definitions, "b[1];")
for base in ("X[x] o", "X x", "x[0]", "&&[v IN x] v"):
    for reverse in (False, True):
        branches = ("f({x},n-1)", base) if reverse else (base, "f({x},n-1)")
        reject("recursive-real-category-error", "o", definitions=
               f"DEFINITIONS {{ f(x,n) = n == 0 : {branches[0]} otherwise : {branches[1]}; }}")
for base, recursive in (("X x", "1"), ("X[x] o", "X o"),
                        ("x[0]", "o"), ("&&[v IN x] v", "1")):
    reject("recursive-real-actual-error", "o", definitions=
           f"DEFINITIONS {{ f(x,n) = n == 0 : {base} otherwise : f({recursive},n-1); }}")
reject("recursive-real-result-error", "o", definitions=
       "DEFINITIONS { f(x,n) = n == 0 : x otherwise : f({x},n-1); }")
cases.append({"name": "runtime-recursion-guard", "source": spec("loop(1)",
              "DEFINITIONS { loop(n) = loop(n+1); }"), "diagnostic": "recursion too deep"})

# §4.5 checks evaluated indices against resolved bounds, including aliases,
# function actuals, stored values and parameter overrides.
for declaration, valid, invalid in (("b[1];", (0,), (-1,1,2)),
                                     ("b[2..3];", (2,3), (-1,0,1,4))):
    for reference in ("b", "alias", "second"):
        definitions = "DEFINITIONS { alias = second; second = b; get(x,n) = x[n]; }"
        for index in valid + invalid:
            for body in (f"{reference}[{index}]", f"get({reference},{index})",
                         f"&&[v IN {{{reference}}}] v[{index}]",
                         f"&&[v IN {{{reference}[{index}]}}] v"):
                if index in valid:
                    pair("bus-index-in-range", body, f"b[{index}]", definitions, declaration)
                else:
                    cases.append({"name": "bus-index-range-error", "source": spec(body, definitions, declaration),
                                  "diagnostic": "bus index out of range"})
for width, index, good in ((1,0,True),(1,1,False),(2,1,True),(2,2,False)):
    c = {"name": "bus-index-resolved-width", "source": spec(f"b[{index}]", "PARAMETERS { N = 1; }", "b[N];"),
         "args": ["--param", f"N={width}"]}
    c.update({"output": f"b_{index}\n"} if good else {"diagnostic": "bus index out of range"})
    cases.append(c)
# An access in an unselected branch is not evaluated; bounds are a value check.
pair("unselected-index", "pick(0)", "o", "DEFINITIONS { pick(n) = n == 0 : o otherwise : b[1]; }", "b[1];")

# §4.4: exact lexical aliases cannot hide a mismatch in unused/dead syntax.
for chain in ("alias = b;", "alias = second; second = b;", "second = b; alias = second;"):
    for width in (1,2):
        for expression in ("alias == label", "label == alias", "alias != label"):
            for use in ("unused = " + expression + ";", "unused(x) = x == 0 : o otherwise : " + expression + ";"):
                c = {"name": "exact-alias-width", "source": spec("o", "DEFINITIONS { enum E = label: 00 other: 11; " + chain + use + "}", f"b[{width}];")}
                c.update({"output": "o\n"} if width == 2 else {"diagnostic": "enum comparison width mismatch"})
                cases.append(c)
# Aliases have their own GLOBAL environment; caller names must not capture it.
cases.append({"name": "alias-lexical-environment", "source": spec("f(c)",
              "DEFINITIONS { enum E = label: 00 other: 11; alias = b; f(b) = alias == label; }", "b[1]; c[2];"),
              "diagnostic": "enum comparison width mismatch"})
pair("alias-shadowed-by-formal", "f(c)", "!c[0] && !c[1]",
     "DEFINITIONS { enum E = label: 00 other: 11; alias = b; f(alias) = alias == label; }", "b[1]; c[2];")
for domain in ("({alias,c} (-) {alias})", "({alias,c} (*) {c})"):
    pair("alias-filtered-width", f"&&[v IN {domain}] v == label", "!c[0] && !c[1]",
         "DEFINITIONS { enum E = label: 00 other: 11; alias = b; }", "b[1]; c[2];")

# Review110h findings 1–2: bus bounds resolve by dependency, and generated
# fairness binders obey the existing declaration freshness rule.
cases.extend([
    {"name": "forward-width-key-exact", "source": spec("X[SIZEOF a] o", signals="a[SIZE {X[SIZEOF b] o, X o}]; b[2];"), "output": "X X o\n"},
    {"name": "forward-width-index-exact", "source": spec("a[0]", signals="a[SIZE {b[1]}]; b[2];"), "output": "a_0\n"},
])
for signals in ("a[SIZEOF b]; b[2];", "b[2]; a[SIZEOF b];",
                "a[SIZEOF b]; b[SIZEOF c]; c[2];",
                "a[SIZE {X[SIZEOF alias] o, X o}]; b[2];"):
    pair("width-dependencies", "X[SIZEOF a] o", "X X o",
         "DEFINITIONS { alias = b; }", signals)
for signals in ("a[SIZEOF a];", "a[SIZEOF b]; b[SIZEOF a];",
                "a[SIZE {X[SIZEOF b] o}]; b[SIZEOF a];",
                "a[SIZE {b[0]}]; b[SIZEOF a];",
                "a[SIZE {b == label}]; b[SIZEOF a];"):
    reject("cyclic-width", "o", category="typing",
           definitions="DEFINITIONS { enum E = label: 00 other: 11; }", signals=signals)
    cases[-1]["diagnostic"] = "cyclic bus width dependency"
# Enum checks while resolving an earlier bound must use the actual later width.
for width in (1, 2):
    c = {"name": "forward-width-enum-key", "source": spec("o",
         "DEFINITIONS { enum E = label: 00 other: 11; }",
         f"a[SIZE {{b == label}}]; b[{width}];")}
    c.update({"output": "o\n"} if width == 2 else
             {"diagnostic": "enum comparison width mismatch"})
    cases.append(c)
for declaration in ("PARAMETERS { __tlsf_fair_i = 7; }",
                    "PARAMETERS { __tlsf_fair_i = 7; __tlsf_fair_i_1 = 8; }",
                    "DEFINITIONS { __tlsf_fair_i = 7; }",
                    "DEFINITIONS { __tlsf_fair_i(x) = x; }",
                    "DEFINITIONS { enum E = __tlsf_fair_i: 0 other: 1; }",
                    "DEFINITIONS { enum __tlsf_fair_i = label: 0 other: 1; }"):
    source = spec("o", declaration).replace("Finite,Mealy", "Mealy").replace(
        "INPUTS { i; }", "INPUTS { i; b[2]; }")
    cases.append({"name": "fresh-fairness-binder", "source": source,
                  "direct": source.replace("__tlsf_fair_i", "user_i"),
                  "args": ["--fair-environment"]})
for signal in ("__tlsf_fair_i;", "__tlsf_fair_i[1];"):
    source = spec("o", signals=signal).replace("Finite,Mealy", "Mealy").replace(
        "INPUTS { i; }", "INPUTS { i; b[2]; }")
    cases.append({"name": "fresh-fairness-output", "source": source,
                  "direct": source.replace("__tlsf_fair_i", "user_i"),
                  "args": ["--fair-environment"]})
# Table 1 row 19: the complete boolean expression guards the case value.
for n, direct in ((0, "o"), (1, "!o"), (2, "o")):
    pair("compound-guard", f"f({n})", direct, definitions=
         "DEFINITIONS { f(n) = n == 0 || n == 2 : o otherwise : !o; }")

with tempfile.TemporaryDirectory(prefix="scoping110-", dir=os.environ["TMPDIR"]) as temp:
    path = Path(temp) / "case.tlsf"

    def run(source, args=()):
        path.write_text(source)
        return subprocess.run([binary, "--format", "ltl", *args, str(path)],
                              text=True, capture_output=True, timeout=17)

    for index, case in enumerate(cases):
        result = run(case["source"], case.get("args", ()))
        context = (index, case["name"], result.returncode, result.stdout, result.stderr)
        if "diagnostic" in case:
            assert result.returncode != 0 and not result.stdout, context
            assert case["diagnostic"] in result.stderr, context
        else:
            assert result.returncode == 0 and not result.stderr, context
            expected = run(case["direct"], case.get("args", ())) if "direct" in case else None
            if expected:
                assert expected.returncode == 0, (context, expected.stderr)
            assert result.stdout == (expected.stdout if expected else case["output"]), context

    fair_source = spec("o", "PARAMETERS { __tlsf_fair_i = 7; __tlsf_fair_i_1 = 8; }").replace(
        "Finite,Mealy", "Mealy").replace("INPUTS { i; }", "INPUTS { i; b[2]; __tlsf_fair_i_2; }")
    path.write_text(fair_source)
    emitted = subprocess.run([str(Path(binary).resolve().with_name("tlsf2tlsf")),
                              "--fair-environment", str(path)], text=True,
                             capture_output=True, timeout=17)
    assert emitted.returncode == 0 and not emitted.stderr, emitted
    assert "__tlsf_fair_i_3" in emitted.stdout, emitted.stdout
    expected = run(fair_source, ["--fair-environment"])
    roundtrip = run(emitted.stdout)
    assert expected.returncode == roundtrip.returncode == 0, (expected, roundtrip)
    assert expected.stdout == roundtrip.stdout, (expected, roundtrip)

    # The basic-TLSF declaration printer must agree with its formula atoms,
    # including names longer than the AIGER reader's unrelated line buffer.
    for length in (254, 1024, 8193):
        bus = "b" * length
        path.write_text(spec(f"{bus}[0] && !{bus}[1]", signals=f"{bus}[2];"))
        result = subprocess.run([str(Path(binary).resolve().with_name("tlsf2tlsf")),
                                 "--basic", str(path)], text=True,
                                capture_output=True, timeout=17)
        assert result.returncode == 0 and not result.stderr, result
        for bit in (0, 1):
            assert f"{bus}_{bit};" in result.stdout, (length, bit)
        roundtrip = run(result.stdout)
        assert roundtrip.returncode == 0 and not roundtrip.stderr, roundtrip
        assert roundtrip.stdout == f"{bus}_0 && !{bus}_1\n", length
print(f"scoping110: {len(cases)} spec-derived rejection and direct-spelling cases; "
      "3 complete-name basic-TLSF roundtrips; fresh-fairness TLSF roundtrip")
