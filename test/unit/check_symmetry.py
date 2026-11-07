"""Tiny, hand-written specs: census schema, generators and conservative failures."""
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile


exe, fixtures, name = sys.argv[1:]
fixtures = Path(fixtures)


def run(path, code=0):
    p = subprocess.run([exe, str(path)], capture_output=True, text=True, timeout=10)
    assert p.returncode == code, (p.returncode, p.stdout, p.stderr)
    result = json.loads(p.stdout)  # Also rejects extra JSON objects or log lines.
    assert math.isfinite(result["wall_seconds"]) and result["wall_seconds"] >= 0
    return result


def check(result, expected):
    assert result["status"] == "ok", result
    assert result["effective_target"] == "Mealy"
    assert result["summary"] == expected["summary"]
    assert [[f["origin_name"], f["lo"], f["hi"], f["is_output"]]
            for f in result["families"]] == expected["families"]
    partition = [set(result["inputs"]), set(result["outputs"])]
    assert not partition[0] & partition[1]
    for f in result["families"]:
        assert f["size"] == f["hi"] - f["lo"] + 1
        assert f["members"] == [f'{f["origin_name"]}_{i}'
                                for i in range(f["lo"], f["hi"] + 1)]
        assert set(f["members"]) <= partition[f["is_output"]]
        assert not f["is_enum"]
    assert [r["verified_group"] for r in result["ranges"]] == expected["groups"]
    assert [[c["verified"] for c in r["candidates"]]
            for r in result["ranges"]] == expected["verified"]
    for r in result["ranges"]:
        ids = [i for i, f in enumerate(result["families"])
               if (f["lo"], f["hi"]) == (r["lo"], r["hi"])]
        assert r["families"] == ids and r["n_families"] == len(ids)
        assert r["size"] == r["hi"] - r["lo"] + 1
        indices = list(range(r["lo"], r["hi"] + 1))
        assert len(r["candidates"]) == len(indices)
        for k, c in enumerate(r["candidates"]):
            image = indices.copy()
            if k == len(indices) - 1:
                assert c["kind"] == "rotation"
                image = image[1:] + image[:1]
            else:
                assert c["kind"] == "adjacent"
                image[k], image[k + 1] = image[k + 1], image[k]
            assert c["image"] == image
            assert c.get("reason") == (None if c["verified"] else "canonical forms differ")


if name != "edges":
    expected = json.loads((fixtures / "expected.json").read_text())[name]
    result = run(fixtures / (name + ".tlsf"))
    check(result, expected)
    print(f'{name}: {expected["groups"]}, wall_seconds={result["wall_seconds"]:.9f}')
    sys.exit(0)

# Meson runs in its build directory. Keep generated inputs there, too.
with tempfile.TemporaryDirectory(dir=Path.cwd(), prefix="tlsfsym-") as tmp:
    path = Path(tmp) / "spec.tlsf"

    def spec(body, semantics="Mealy"):
        path.write_text(f"INFO {{ SEMANTICS: {semantics} TARGET: Mealy }}\n"
                        f"MAIN {{ {body} }}")
        return run(path)

    r = spec("INPUTS { unused; } OUTPUTS { q; } GUARANTEES { G q; }")
    assert r["families"] == r["ranges"] == []
    assert r["summary"] == {"n_families": 0, "n_ranges": 0, "range_sizes": []}

    r = spec("OUTPUTS { q[7..7]; } GUARANTEES { G q[7]; }")
    assert r["ranges"][0]["verified_group"] == "symmetric"
    assert r["ranges"][0]["candidates"] == [
        {"kind": "rotation", "image": [7], "verified": True}]

    # Equal widths with different bounds are separate permutation domains.
    r = spec("OUTPUTS { q[0..1]; r[4..5]; } GUARANTEES { "
             "G (q[0] <-> r[4]); G (q[1] <-> r[5]); }")
    assert r["summary"]["n_ranges"] == 2
    assert [g["verified_group"] for g in r["ranges"]] == ["none", "none"]

    # Enum declarations use the same provenance API; preserve its metadata.
    path.write_text('INFO { SEMANTICS: Mealy TARGET: Mealy } '
                    'GLOBAL { DEFINITIONS { enum Choice = A: 01 B: 10 C: 11; } } '
                    'MAIN { OUTPUTS { Choice state; } GUARANTEES { G (state == C); } }')
    r = run(path)
    assert r["families"][0]["is_enum"] and r["families"][0]["is_output"]
    assert r["ranges"][0]["verified_group"] == "symmetric"

    # Different association and ordering; EQUIV and its negation commute.
    r = spec("OUTPUTS { q[0..1]; z; } GUARANTEES { "
             "G ((q[0] && (z && q[1])) || ((q[1] || z) || q[0])); "
             "G (q[0] <-> q[1]); G !(q[0] <-> q[1]); }")
    assert r["ranges"][0]["verified_group"] == "symmetric"

    # Only the assumption distinguishes an index. Checking guarantees alone
    # would incorrectly certify the full symmetric group.
    for section in ["INITIALLY", "PRESET", "REQUIRE", "ASSERT", "ASSUMPTIONS"]:
        for semantics in ["Mealy", "Moore,Strict"]:
            r = spec("INPUTS { a; } OUTPUTS { q[0..2]; } "
                     f"{section} {{ q[0]; }} "
                     "GUARANTEES { &&[0 <= i <= 2] G (a <-> q[i]); }", semantics)
            assert r["ranges"][0]["verified_group"] == "none", (section, r)

    # Directional operators retain operand order.
    for op in ["->", "U", "R", "W"]:
        r = spec(f"OUTPUTS {{ q[0..1]; }} GUARANTEES {{ q[0] {op} q[1]; }}")
        assert r["ranges"][0]["verified_group"] == "none", (op, r)

    r = spec("OUTPUTS { q[0..1]; } GUARANTEES { " + "F " * 1030 + "q[0]; }")
    assert r["status"] == "unverified" and "depth" in r["reason"]
    assert r["ranges"][0]["verified_group"] == "none"
    for candidate in r["ranges"][0]["candidates"]:
        assert not candidate["verified"] and "depth" in candidate["reason"]

    for text, reason in [
        ('INFO { SEMANTICS: Mealy TARGET: Mealy } GLOBAL { PARAMETERS { n; } } '
         'MAIN { OUTPUTS { q[0..n-1]; } GUARANTEES { G q[0]; } }', 'parameter'),
        ('INFO { SEMANTICS: Mealy,Finite TARGET: Mealy } '
         'MAIN { OUTPUTS { q[0..1]; } GUARANTEES { G q[0]; } }', 'finite'),
    ]:
        path.write_text(text)
        r = run(path, code=1)
        assert r["status"] == "unverified" and reason in r["reason"].lower(), r
        assert r["summary"] is None and r["ranges"] == []
