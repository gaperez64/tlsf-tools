#!/usr/bin/env python3
"""Compare native environment ranks with the saved prototype candidates."""

import argparse
import json
import pathlib
import subprocess
import sys
import time

NODE_TOLERANCE = 32
APPLY_TOLERANCE = 40


def compare(native, reference):
    from test_gr1_environment_provenance import parse_circuit
    from u1_candidate import Bdd

    bdd = Bdd(cap=3000000, op_cap=12000000)

    def roots(path):
        circuit = parse_circuit(path.read_text())
        labels = {lit // 2: circuit.input_names[index]
                  for index, lit in enumerate(circuit.inputs)}
        return {name: bdd.from_aig(circuit, circuit.output(name), labels)
                for name in circuit.output_names.values()
                if name.startswith(("z_", "y_", "x_"))}

    expected = roots(reference)
    observed = roots(native)
    names_equal = expected.keys() == observed.keys()
    different = [name for name in observed
                 if expected.get(name) != observed[name]]
    return names_equal and not different, len(expected), different


def status_fields(line):
    return dict(part.split("=", 1) for part in line.split() if "=" in part)


def rule_name(learned):
    if learned[0] == "summary":
        return "summary"
    if learned[0] == "previous_rank_or_anchor":
        return "previous-z"
    if learned[0] == "anchor_free":
        return "anchor-free"
    return "projection"


def compare_classes(native_path, prototype):
    native = json.loads(pathlib.Path(str(native_path) + ".classes.json").read_text())
    expected = prototype["class_trace"]
    def inventory(rows):
        return {tuple(row["names"]): row for row in rows}
    observed_by_name, expected_by_name = inventory(native), inventory(expected)
    if len(observed_by_name) != len(native) or len(expected_by_name) != len(expected):
        return False, "duplicate class identity", []
    if observed_by_name.keys() != expected_by_name.keys():
        return False, "class identity inventory differs", []
    work = []
    for identity, reference in expected_by_name.items():
        actual = observed_by_name[identity]
        if actual["rule"] != reference["rule"]:
            return False, f"rule differs for {identity}", work
        if reference["rule"] in ("projection", "anchor-free") and (
                actual["arity"] != reference["arity"] or
                actual["mode"] != reference["mode"]):
            return False, f"projection fit differs for {identity}", work
        if (reference["rule"] == "previous-z" and
                actual["predecessor"] != reference["predecessor"]):
            return False, f"predecessor differs for {identity}", work
        if (abs(actual["nodes"] - reference["nodes"]) > NODE_TOLERANCE or
                abs(actual["applies"] - reference["applies"]) > APPLY_TOLERANCE):
            return False, f"cumulative BDD work differs for {identity}", work
        work.append({"names": identity, "rule": reference["rule"],
                     "native_nodes": actual["nodes"],
                     "prototype_nodes": reference["nodes"],
                     "native_applies": actual["applies"],
                     "prototype_applies": reference["applies"]})
    return True, "", work


def prototype_ranks(args, source, directory, size, output):
    import cross_lane
    import u1_candidate as candidate

    probe_dir = args.out / f"{size}-{source.parent.name}-seeds"
    probe_dir.mkdir(parents=True, exist_ok=True)
    selected = subprocess.run(
        [sys.executable, str(args.prototype / "window_probe.py"),
         "--repo", str(args.repo), "--build", str(args.seed_build),
         "--output", str(probe_dir), "--instance", str(source),
         "--heldout", str(size), "--managed-marker"],
        capture_output=True, text=True, timeout=300, check=False)
    if selected.returncode:
        raise RuntimeError(selected.stdout + selected.stderr)
    audit = json.loads((probe_dir / "observations.json").read_text())[0]
    if audit["stage"] != "candidate_ready":
        raise RuntimeError(f"seed screen ended at {audit['stage']}")
    bdd = cross_lane.Bdd(time.monotonic() + 180, cap=3000000,
                         op_cap=12000000, order="owner-interleave")
    views = [candidate.View(probe_dir / "case-000" / f"seed-{number}",
                            number, bdd) for number in (3, 4, 5)]
    plan = candidate.identity_preflight(views)
    classes = {}
    class_names = {}
    for view, policy, circuit, _, labels, outputs in plan:
        if policy:
            continue
        for position, key in outputs:
            if key[0] not in ("z", "y", "x"):
                continue
            root = bdd.from_aig(circuit, circuit.outputs[position], labels)
            classes.setdefault((False, candidate.class_key(key)), []).append(
                (view, root, key[3:5]))
            if view is views[0]:
                class_names.setdefault((False, candidate.class_key(key)),
                                       set()).add(circuit.output_names[position])
    learned = {}
    class_trace = []
    for key, observations in classes.items():
        try:
            learned[key] = candidate.learn(bdd, observations)
        except candidate.Decline as error:
            if error.stage != "schema":
                raise
            try:
                learned[key] = candidate.learn_with_summary(bdd, observations)
            except candidate.Decline as summary_error:
                kind, outer = key[1][:2]
                previous = (False, ("z", outer - 1, None, None, None))
                if outer == 0 or kind not in ("z", "y", "x") or previous not in classes:
                    raise summary_error
                learned[key] = candidate.learn_with_predecessor(
                    bdd, observations, classes[previous], f"z_{outer - 1}")
        fit = learned[key]
        rule = rule_name(fit)
        class_trace.append({
            "names": sorted(class_names[key]), "rule": rule,
            "arity": (fit[1] if rule == "anchor-free" else fit[0]
                      if rule == "projection" else 0),
            "mode": ((0 if fit[2] == "and" else 1) if rule == "anchor-free"
                     else (0 if fit[1] == "and" else 1)
                     if rule == "projection" else 0),
            "predecessor": fit[1] if rule == "previous-z" else "",
            "nodes": len(bdd.nodes), "applies": bdd.ops})
    prefix = source.with_suffix("")
    candidate.validate_target_reduction(prefix, source.read_text())
    target = candidate.View(prefix, size, bdd)
    roots = {}
    outer = audit["detail"]["outer_levels"]
    for level in range(outer):
        names = [f"z_{level}"]
        for goal in range(len(target.game.justice)):
            names.append(f"y_{level}_{goal}")
            for fair in range(max(1, len(target.game.fairness))):
                depth = max((key[1][2] + 1 for key in learned
                             if not key[0] and key[1][0] == "x"
                             and key[1][1] == level
                             and key[1][3] == target.goals[goal].kind
                             and key[1][4] == target.fairs[fair].kind),
                            default=0)
                names.extend(f"x_{level}_{goal}_{fair}_{inner}"
                             for inner in range(depth))
        for name in names:
            key = target.output_key(name)
            roots[name] = candidate.instantiate(
                bdd, target, key, learned[(False, candidate.class_key(key))],
                roots)
    inputs = [(target.input_by_name[target.game.latch_name(lit // 2)],
               target.game.latch_name(lit // 2))
              for lit, _ in target.game.latches]
    inputs.extend((target.input_by_name[target.game.input_names[position]],
                   target.game.input_names[position])
                  for position in range(len(target.game.inputs)))
    aig = candidate.Aag(inputs)
    for name, root in roots.items():
        aig.outputs.append((name, aig.from_bdd(bdd, root)))
    output.write_text(aig.render())
    return {"classes": len(learned), "nodes": len(bdd.nodes),
            "applies": bdd.ops, "class_trace": class_trace}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=pathlib.Path, required=True)
    parser.add_argument("--binary", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument("--oracle", type=pathlib.Path, required=True)
    parser.add_argument("--prototype", type=pathlib.Path, required=True)
    parser.add_argument("--repo", type=pathlib.Path, required=True)
    parser.add_argument("--seed-build", type=pathlib.Path, required=True)
    parser.add_argument("--fault-binary", type=pathlib.Path, required=True)
    args = parser.parse_args()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(args.oracle))
    sys.path.insert(0, str(args.prototype))
    # Every comparison reads files the binaries just wrote, so stale artifacts
    # from an earlier run must not be able to stand in for a missing output.
    if args.out.exists() and any(args.out.iterdir()):
        sys.exit(f"output directory {args.out} is not empty; use a fresh one")
    args.out.mkdir(parents=True, exist_ok=True)
    rows = []
    failures = []
    expected_keys = set()
    for size in (7, 9):
        directory = args.base / str(size)
        expected_rows = json.loads((directory / "summary.json").read_text())
        for expected in expected_rows:
            index = expected["index"]
            expected_keys.add((size, index))
            stem = f"case-{index:03d}"
            source = directory / stem / f"{stem}-target.tlsf"
            output = args.out / f"{size}-{stem}-rank.aag"
            result = subprocess.run(
                [str(args.binary), str(source), str(output)],
                capture_output=True, text=True, timeout=300, check=False)
            status_line = result.stdout.strip().splitlines()[-1:]
            status = status_line[0] if status_line else ""
            row = {"size": size, "index": index,
                   "prototype_stage": expected["stage"],
                   "native_exit": result.returncode,
                   "native_status": status,
                   "native_error": result.stderr.strip(),
                   "rank_equal": None, "rank_count": None,
                   "classes_equal": None,
                   "different": []}
            if result.returncode == 0:
                reference = args.out / f"{size}-{stem}-prototype-rank.aag"
                try:
                    row["prototype_rank_work"] = prototype_ranks(
                        args, source, directory / stem, size, reference)
                    row["rank_equal"], row["rank_count"], row["different"] = compare(
                        output, reference)
                    row["classes_equal"], row["class_error"], row["class_work"] = (
                        compare_classes(output, row["prototype_rank_work"]))
                    fields = status_fields(status)
                    row["work_within_tolerance"] = (
                        abs(int(fields["nodes"]) - row["prototype_rank_work"]["nodes"])
                        <= NODE_TOLERANCE and
                        abs(int(fields["applies"]) - row["prototype_rank_work"]["applies"])
                        <= APPLY_TOLERANCE)
                except Exception as error:
                    row["reference_error"] = str(error)
            if (result.returncode or not row["rank_equal"] or
                    not row["classes_equal"] or not row.get("work_within_tolerance")):
                failures.append(f"{size}-{stem}: native decline, reference error, "
                                "unequal rank, or unequal class")
            rows.append(row)
            print(json.dumps({key: value for key, value in row.items()
                              if key not in ("prototype_rank_work", "class_work")}),
                  flush=True)
            (args.out / "regular-results.json").write_text(
                json.dumps(rows, indent=2) + "\n")
    control_rows = []
    for size in (7, 9):
        directory = args.base / str(size)
        controls = {row["case"]: row for row in json.loads(
            (directory / "controls.json").read_text())}
        renamed = directory / "renamed-case-13" / "case-000-target.tlsf"
        renamed_native = args.out / f"{size}-renamed-rank.aag"
        result = subprocess.run(
            [str(args.binary), str(renamed), str(renamed_native)],
            capture_output=True, text=True, timeout=300, check=False)
        row = {"size": size, "case": "renamed-case-13",
               "prototype_stage": controls["renamed-case-13"]["stage"],
               "native_exit": result.returncode,
               "native_status": result.stdout.strip(),
               "native_error": result.stderr.strip(), "rank_equal": None}
        if result.returncode == 0:
            reference = args.out / f"{size}-renamed-prototype-rank.aag"
            try:
                row["prototype_rank_work"] = prototype_ranks(
                    args, renamed, renamed.parent, size, reference)
                row["rank_equal"], row["rank_count"], row["different"] = compare(
                    renamed_native, reference)
                row["classes_equal"], row["class_error"], row["class_work"] = (
                    compare_classes(renamed_native, row["prototype_rank_work"]))
                fields = status_fields(result.stdout)
                row["work_within_tolerance"] = (
                    abs(int(fields["nodes"]) - row["prototype_rank_work"]["nodes"])
                    <= NODE_TOLERANCE and
                    abs(int(fields["applies"]) - row["prototype_rank_work"]["applies"])
                    <= APPLY_TOLERANCE)
            except Exception as error:
                row["reference_error"] = str(error)
        if (result.returncode or not row["rank_equal"] or
                not row.get("classes_equal") or not row.get("work_within_tolerance")):
            failures.append(f"{size}-renamed: native decline, reference error, "
                            "unequal rank, or unequal class")
        control_rows.append(row)
        source = directory / "case-013" / "case-013-target.tlsf"
        sibling = subprocess.run(
            [str(args.fault_binary), str(source),
             str(args.out / f"{size}-sibling-rank.aag"), "5"],
            capture_output=True, text=True, timeout=300, check=False)
        control_rows.append({
            "size": size, "case": "sibling-swap",
            "prototype_stage": controls["sibling-swap"]["stage"],
            "native_exit": sibling.returncode,
            "native_status": sibling.stdout.strip(),
            "native_error": sibling.stderr.strip(),
            "rank_equal": None})
        if sibling.returncode == 0 or (
                status_fields(sibling.stdout).get("stage") !=
                controls["sibling-swap"]["stage"]):
            failures.append(f"{size}-sibling-swap: stage differs")
        real = directory / "target-real" / "case-000-target.tlsf"
        real_result = subprocess.run(
            [str(args.binary), str(real),
             str(args.out / f"{size}-real-rank.aag")],
            capture_output=True, text=True, timeout=300, check=False)
        control_rows.append({
            "size": size, "case": "target-real",
            "prototype_stage": controls["target-real"]["stage"],
            "native_exit": real_result.returncode,
            "native_status": real_result.stdout.strip(),
            "native_error": real_result.stderr.strip(),
            "rank_equal": None})
        if real_result.returncode == 0 or (
                status_fields(real_result.stdout).get("stage") !=
                controls["target-real"]["stage"]):
            failures.append(f"{size}-target-real: stage differs")
        from test_gr1_certcheck import replace_output
        baseline = args.out / f"{size}-case-013-rank.aag"
        mutation = args.out / f"{size}-mutated-rank.aag"
        mutation.write_text(replace_output(baseline.read_text(), "z_0",
                                           invert=True))
        equal, _, different = compare(mutation, baseline)
        control_rows.append({
            "size": size, "case": "mutated-rank",
            "prototype_stage": controls["mutated-rank"]["stage"],
            "native_exit": 0,
            "native_status": "post-rank mutation control",
            "native_error": "",
            "rank_equal": equal,
            "different": different,
            "rank_check_boundary": "policy and checker follow in N2b"})
        if equal or "z_0" not in different:
            failures.append(f"{size}-mutated-rank: mutation was not detected")
        (args.out / "controls-results.json").write_text(
            json.dumps(control_rows, indent=2) + "\n")
    (args.out / "all-results.json").write_text(
        json.dumps(rows + control_rows, indent=2) + "\n")
    if (len(rows) != 22 or len(expected_keys) != 22 or
            {(row["size"], row["index"]) for row in rows} != expected_keys or
            len(control_rows) != 8 or
            {(row["size"], row["case"]) for row in control_rows} !=
            {(size, case) for size in (7, 9) for case in
             ("renamed-case-13", "sibling-swap", "target-real", "mutated-rank")} or
            len(rows + control_rows) != 30):
        failures.append("missing confirmation row")
    real_seed_rows = []
    real_seed_template = pathlib.Path(__file__).with_name("env_real_seed.tlsf").read_text()
    if real_seed_template.count("width = 7;") != 1:
        raise RuntimeError("REAL seed control width binding changed")
    for size in (7, 9):
        source = args.out / f"real-seed-{size}.tlsf"
        source.write_text(real_seed_template.replace("width = 7;", f"width = {size};"))
        result = subprocess.run(
            [str(args.binary), str(source),
             str(args.out / f"real-seed-{size}-rank.aag")],
            capture_output=True, text=True, timeout=300, check=False)
        fields = status_fields(result.stdout)
        real_seed_rows.append({"size": size, "native_exit": result.returncode,
                               "native_status": result.stdout.strip(),
                               "native_error": result.stderr.strip()})
        if (result.returncode != 1 or fields.get("stage") != "seed_check" or
                fields.get("solves") != "1" or fields.get("checks") != "1" or
                "checked REAL seed is ineligible for U" not in result.stderr):
            failures.append(f"{size}-real-seed: checked REAL seed was not rejected")
    (args.out / "real-seed-results.json").write_text(
        json.dumps(real_seed_rows, indent=2) + "\n")
    (args.out / "failures.json").write_text(json.dumps(failures, indent=2) + "\n")
    if failures:
        for failure in failures:
            print(failure, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
