#!/usr/bin/env python3
"""Exercise typed width and monitor linkage in the native JSON API."""

import argparse
import copy
import hashlib
import json
import pathlib
import subprocess
import tempfile


def run(*args):
    result = subprocess.run(args, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, (args, result.stdout, result.stderr)


def frontend(tool, source, root):
    target = root / "frontend.json"
    run(str(tool), "--provenance-out", str(target), "--output",
        str(root / "basic.tlsf"), str(source))
    data = json.loads(target.read_text())
    assert data["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    return data


def reduction(tool, source, root, frontend_override=None):
    prefix = root / "game"
    args = [str(tool), str(source), "exact", str(prefix)]
    if frontend_override is not None:
        args.append(str(frontend_override))
    run(*args)
    return json.loads(prefix.with_suffix(".json").read_text())


def by_declaration(data):
    rows = {}
    for row in data["signals"]:
        rows.setdefault(row["declaration_id"], []).append(row)
    return rows


def reference_element_owner_ids(row, parameters):
    """Apply the documented typed-ID ownership rule to emitted JSON."""
    if row.get("index_role") != "element":
        return None
    if row.get("width_binding_complete") is not True:
        return None
    ids = row.get("width_parameter_ids")
    parameter_ids = [parameter.get("id") for parameter in parameters]
    if (any(type(axis) is not int or axis < 1 for axis in parameter_ids) or
            len(parameter_ids) != len(set(parameter_ids)) or
            not isinstance(ids, list) or
            any(type(axis) is not int for axis in ids) or
            len(ids) != len(set(ids)) or
            any(axis not in parameter_ids for axis in ids)):
        return None
    return tuple(ids)


def check_linkage(data):
    conjuncts = {(row["source_formula_id"], row["generated_position"]): row
                 for row in data["source_conjuncts"]}
    assert len(conjuncts) == len(data["source_conjuncts"])
    bound = set()
    for monitor in data["monitors"]:
        origin = monitor["source_origin"]
        assert origin is not None
        key = (origin["source_formula_id"], origin["generated_position"])
        assert key not in bound
        bound.add(key)
        source = conjuncts[key]
        assert monitor["source_binding"] == {
            field: origin[field] for field in
            ("source_formula_id", "generated_position", "source_node_id")}
        assert all(origin[field] == source[field] for field in
                   ("block", "source_node_id", "bindings", "signal_refs"))
        assert monitor["construction_formula"] == source["normalized_formula"]
    assert len(bound) == len(data["monitors"])


def width_cases(frontend_tool, reducer, root):
    source = root / "width.tlsf"
    source.write_text('''INFO { TITLE: "typed widths" DESCRIPTION: "typed widths"
  SEMANTICS: Mealy TARGET: Mealy }
GLOBAL { PARAMETERS { n = 3; m = 3; }
  DEFINITIONS {
    unused(v) = 3;
    used(v) = v;
    recursive(v) = v <= 0 : 1 otherwise : recursive(v - 1) + 1;
  }
}
MAIN { INPUTS { direct[0..n-1]; other[0..m-1];
                 fixed[0..unused(n)-1]; derived[0..used(n)-1];
                 rec[0..recursive(n)-1]; }
  OUTPUTS { grant; }
  GUARANTEE { G grant; }
}
''')
    data = frontend(frontend_tool, source, root)
    assert not data["ambiguous"]
    ids = {row["name"]: row["id"] for row in data["parameters"]}
    assert ids["n"] != ids["m"]
    rows = by_declaration(data)
    for name, expected_ids, complete, role in (
            ("direct", [ids["n"]], True, "element"),
            ("other", [ids["m"]], True, "element"),
            ("fixed", [], True, "undetermined"),
            ("derived", [ids["n"]], True, "undetermined"),
            ("rec", [ids["n"]], False, "undetermined")):
        members = next(members for members in rows.values()
                       if members[0]["source_name"] == name)
        assert all(row["width_parameter_ids"] == expected_ids and
                   row["width_binding_complete"] is complete and
                   row["index_role"] == role for row in members), (name, members)

    # A reference consumer decides ownership from typed IDs, never display text.
    direct = next(members[0] for members in rows.values()
                  if members[0]["source_name"] == "direct")
    other = next(members[0] for members in rows.values()
                 if members[0]["source_name"] == "other")
    assert reference_element_owner_ids(direct, data["parameters"]) == (ids["n"],)
    assert reference_element_owner_ids(other, data["parameters"]) == (ids["m"],)
    direct_text, other_text = direct["width_expression"], other["width_expression"]
    assert direct_text != other_text
    other["width_expression"] = direct_text
    assert reference_element_owner_ids(other, data["parameters"]) == (ids["m"],)
    direct["width_expression"] = other_text
    assert reference_element_owner_ids(direct, data["parameters"]) == (ids["n"],)
    invalid = copy.deepcopy(direct)
    invalid["width_parameter_ids"] = []
    assert reference_element_owner_ids(invalid, data["parameters"]) == ()
    invalid["width_parameter_ids"] = [ids["n"]]
    invalid["width_binding_complete"] = False
    assert reference_element_owner_ids(invalid, data["parameters"]) is None
    invalid["width_binding_complete"] = True
    invalid["width_parameter_ids"] = [ids["n"], ids["n"]]
    assert reference_element_owner_ids(invalid, data["parameters"]) is None
    invalid["width_parameter_ids"] = [max(ids.values()) + 1]
    assert reference_element_owner_ids(invalid, data["parameters"]) is None
    invalid["width_parameter_ids"] = [ids["n"]]
    invalid["index_role"] = "undetermined"
    assert reference_element_owner_ids(invalid, data["parameters"]) is None

    renamed = root / "renamed.tlsf"
    renamed.write_text(source.read_text().replace("n =", "lanes =")
                       .replace("unused(n)", "unused(lanes)")
                       .replace("used(n)", "used(lanes)")
                       .replace("recursive(n)", "recursive(lanes)")
                       .replace("direct", "requests")
                       .replace("grant", "answer")
                       .replace("0..n-1", "0..lanes-1"))
    renamed_data = frontend(frontend_tool, renamed, root)
    assert renamed_data["source_sha256"] != data["source_sha256"]
    assert [(row["declaration_id"], row["index_tuple"],
             row["width_parameter_ids"], row["width_binding_complete"],
             row["index_role"]) for row in data["signals"]] == [
                 (row["declaration_id"], row["index_tuple"],
                  row["width_parameter_ids"], row["width_binding_complete"],
                  row["index_role"]) for row in renamed_data["signals"]]
    native = reduction(reducer, source, root)
    assert all(row["width_parameter_ids"] == data_row["width_parameter_ids"]
               for row, data_row in zip(native["inputs"] + native["outputs"],
                                        data["signals"]))
    check_linkage(native)
    renamed_native = reduction(reducer, renamed, root)
    check_linkage(renamed_native)
    assert [(row["declaration_id"], row["width_parameter_ids"],
             row["width_binding_complete"], row["index_role"])
            for row in native["inputs"] + native["outputs"]] == [
                (row["declaration_id"], row["width_parameter_ids"],
                 row["width_binding_complete"], row["index_role"])
                for row in renamed_native["inputs"] + renamed_native["outputs"]]


def representation_bits(frontend_tool, source, root):
    data = frontend(frontend_tool, source, root)
    bits = [row for row in data["signals"]
            if row["index_role"] == "representation-bit"]
    assert bits
    assert all(row["width_parameter_ids"] == [] for row in bits)
    encoded = root / "encoded.tlsf"
    encoded.write_text('''INFO { TITLE: "encoded" DESCRIPTION: "binary index"
  SEMANTICS: Mealy TARGET: Mealy }
GLOBAL { PARAMETERS { n = 3; }
  DEFINITIONS {
    half_count(x) = x <= 1 : 0 otherwise : 1 + half_count(x / 2);
    bit_count(x) = x == 0 : 0 otherwise : 1 + half_count(x - 1);
  }
}
MAIN { INPUTS { request[0..n-1]; }
  OUTPUTS { encoded[0..bit_count(n)-1]; }
  GUARANTEE { G encoded[0]; }
}
''')
    data = frontend(frontend_tool, encoded, root)
    axis_id = data["parameters"][0]["id"]
    elements = [row for row in data["signals"]
                if row["source_name"] == "request"]
    bits = [row for row in data["signals"]
            if row["source_name"] == "encoded"]
    assert elements and bits
    assert all(row["index_role"] == "element" and
               row["width_parameter_ids"] == [axis_id] and
               row["width_binding_complete"] is True for row in elements)
    assert all(row["index_role"] == "representation-bit" and
               row["width_parameter_ids"] == [axis_id] and
               row["width_binding_complete"] is False for row in bits)


def sibling_cases(reducer, root):
    template = '''INFO { TITLE: "siblings" DESCRIPTION: "equal support"
  SEMANTICS: Mealy TARGET: Mealy }
MAIN { INPUTS { i; } OUTPUTS { o; }
  GUARANTEE { %s }
}
'''
    formulas = ("G F o; G F !o;", "G F !o; G F o;")
    orders = []
    for index, formula in enumerate(formulas):
        source = root / f"siblings-{index}.tlsf"
        source.write_text(template % formula)
        data = reduction(reducer, source, root)
        check_linkage(data)
        monitors = data["monitors"]
        assert len(monitors) == 2
        assert (monitors[0]["role"] == monitors[1]["role"] == "justice")
        assert (monitors[0]["source_origin"]["signal_refs"] ==
                monitors[1]["source_origin"]["signal_refs"])
        assert monitors[0]["construction_formula"] != monitors[1]["construction_formula"]
        orders.append(tuple(monitor["construction_formula"] for monitor in monitors))
        corrupted = copy.deepcopy(data)
        a, b = corrupted["monitors"]
        for field in ("source_origin", "source_binding"):
            a[field], b[field] = b[field], a[field]
        try:
            check_linkage(corrupted)
        except AssertionError:
            pass
        else:
            raise AssertionError("joint origin and binding swap was accepted")
    assert orders[0] == tuple(reversed(orders[1]))


def construction_independence(frontend_tool, reducer, root):
    source = root / "construction.tlsf"
    source.write_text('''INFO { TITLE: "construction" DESCRIPTION: "construction"
  SEMANTICS: Mealy TARGET: Mealy }
MAIN { INPUTS { i; } OUTPUTS { o; }
  GUARANTEE { G F o; }
}
''')
    baseline = reduction(reducer, source, root)
    check_linkage(baseline)
    assert len(baseline["monitors"]) == 1
    original_formula = baseline["monitors"][0]["construction_formula"]

    # Test-only frontend substitution: GF(o or X o) is equivalent to GF o,
    # but has a different canonical syntax. Monitor construction is unchanged.
    inventory = frontend(frontend_tool, source, root)
    assert len(inventory["conjuncts"]) == 1
    inventory["conjuncts"][0]["formula"] = "G F (o || X o)"
    override = root / "equivalent-frontend.json"
    override.write_text(json.dumps(inventory))
    changed = reduction(reducer, source, root, override)
    assert changed["source_origin_metadata"]["available"] is True
    assert changed["monitors"][0]["source_binding"] == baseline["monitors"][0]["source_binding"]
    assert changed["monitors"][0]["construction_formula"] == original_formula
    assert changed["source_conjuncts"][0]["normalized_formula"] != original_formula
    try:
        check_linkage(changed)
    except AssertionError:
        pass
    else:
        raise AssertionError("equivalent but different construction/source formulas accepted")


def ambiguous_source_match(reducer, root):
    source = root / "duplicate.tlsf"
    source.write_text('''INFO { TITLE: "duplicate" DESCRIPTION: "duplicate"
  SEMANTICS: Mealy TARGET: Mealy }
MAIN { INPUTS { i; } OUTPUTS { o; }
  GUARANTEE { G F o; G F o; }
}
''')
    data = reduction(reducer, source, root)
    assert len(data["source_conjuncts"]) == 2
    assert len(data["monitors"]) == 1
    assert data["source_origin_metadata"]["available"] is False
    monitor = data["monitors"][0]
    assert monitor["construction_formula"]
    assert monitor["source_origin"] is None
    assert "source_binding" not in monitor


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--frontend", type=pathlib.Path, required=True)
    parser.add_argument("--reducer", type=pathlib.Path, required=True)
    parser.add_argument("--enum-fixture", type=pathlib.Path, required=True)
    parser.add_argument("--builddir", type=pathlib.Path, required=True)
    args = parser.parse_args()
    args.frontend = args.frontend.resolve()
    args.reducer = args.reducer.resolve()
    with tempfile.TemporaryDirectory(dir=args.builddir) as directory:
        root = pathlib.Path(directory)
        width_cases(args.frontend, args.reducer, root)
        representation_bits(args.frontend, args.enum_fixture, root)
        sibling_cases(args.reducer, root)
        construction_independence(args.frontend, args.reducer, root)
        ambiguous_source_match(args.reducer, root)
    print("typed provenance: width, rename, representation, construction and ambiguity checks passed")


if __name__ == "__main__":
    main()
