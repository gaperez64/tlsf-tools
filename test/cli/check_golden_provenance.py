"""Check reference provenance, content binding, and the owner's golden size cap."""
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

root = Path(sys.argv[1]) / "test/fixtures/golden"
retirement = json.loads((root.parents[2] / "tools/analysis/oracle-retirement.json").read_text())
assert set(retirement["source_rebindings"]) == {
    "include/tlsf/aiger.h", "include/tlsf/safety_oxidd.h",
    "src/lib/gr1_oxidd.c", "src/lib/precheck_unreal.h",
    "src/lib/print_ltlxba.c", "src/lib/print_ltlxba.h", "src/lib/rewrite.h",
    "test/cli/check_golden_provenance.py",
}


def retirement_digest(name, historical):
    binding = retirement["source_rebindings"].get(name)
    if binding:
        assert historical == binding["previous_sha256"], (name, "wrong historical source binding")
        return binding["current_sha256"]
    return historical


manifest = json.loads((root / "provenance.json").read_text())
for path in root.glob("*.json"):
    if path.name in ("tool-versions.json", "skipped.json", "provenance.json"):
        continue
    suite = manifest[path.stem]
    assert "independent_checks" in suite and "native_snapshot" in suite, path
    if path.stem in ("native-reduction", "native-lift"):
        assert suite["status"] == "independently confirmed", path
        assert suite["cases"] == (436 if path.stem == "native-reduction" else 13)
        assert suite["native_status_counts"]["0"] > 0
    records = json.loads(path.read_text())
    if path.stem == "assumption-pruning":
        assert suite["status"] == "independently confirmed", path
        assert suite["verdicts"] == sum(row[0] == "verdict" for row in records) == 63
        assert suite["exports"] == sum(row[0] != "verdict" for row in records) == 85
        source = root.parents[1] / "oracle/test_assumption_pruning.py"
        assert suite["test_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    digest = hashlib.sha256(json.dumps(records, separators=(",", ":")).encode()).hexdigest()
    assert suite["sha256"] == digest, (path, "unconfirmed payload")
    historical = records
    if "pruning_source_updates" in suite:
        historical = copy.deepcopy(records)
        for patch in suite["pruning_source_updates"]:
            source = (root.parents[2] / patch["source"]).read_text()
            before = patch["before_source"]
            assert hashlib.sha256(before.encode()).hexdigest() == patch["before_sha256"]
            assert hashlib.sha256(source.encode()).hexdigest() == patch["after_sha256"]
            # Only the explanatory description changed, preserving every
            # successful circuit and its original independent confirmation.
            description = r'DESCRIPTION:\s*"[^"\n]*"'
            assert re.sub(description, "", before) == re.sub(description, "", source)
            assert len(patch["records"]) == 4
            for index, label in patch["records"]:
                assert historical[index][0] == label
                field = historical[index][1]
                if label == ".json":
                    field = field["source_origin_metadata"]
                else:
                    assert label == ".metadata.json"
                assert field["source_sha256"] == patch["after_sha256"]
                field["source_sha256"] = patch["before_sha256"]
        restored_hash = hashlib.sha256(json.dumps(historical, separators=(",", ":")).encode()).hexdigest()
        assert restored_hash == suite["pre_pruning_sources_sha256"]
    if "phase1_sha256" in suite:
        restored = list(historical)
        if "phase2_declines" in suite:
            patches = {row["case"]: row for row in suite["phase2_declines"]}
            restored = []
            found = set()
            i = 0
            while i < len(historical):
                label, value = historical[i]
                case = value[0] + ":" + value[1] if label == "status" else None
                if case in patches:
                    patch = patches[case]
                    assert historical[i:i+2] == patch["after"]
                    assert patch["before"][0] == ["status", value[:2] + [0]]
                    assert value[2] == 3 and patch["reason"]
                    restored.extend(patch["before"])
                    found.add(case)
                    i += 2
                else:
                    restored.append(historical[i])
                    i += 1
            assert found == patches.keys()
        else:
            for patch in suite["phase2_changes"]:
                assert restored[patch["index"]] == patch["after"]
                assert patch["before"] == ["native-admission", 0]
                assert patch["after"] == ["native-admission", 3]
                restored[patch["index"]] = patch["before"]
        phase1 = hashlib.sha256(json.dumps(restored, separators=(",", ":")).encode()).hexdigest()
        assert phase1 == suite["phase1_sha256"], (path, "non-decline expectation changed")
    if path.stem in ("native-reduction", "native-lift"):
        label = "status" if path.stem == "native-reduction" else "lift"
        cases = [row[1] for row in records if row[0] == label]
        assert len(cases) == suite["cases"], path
        assert dict(Counter(str(row[-1]) for row in cases)) == suite["native_status_counts"], path
for name, digest in manifest["dpa"]["files_sha256"].items():
    assert hashlib.sha256((root / "dpa" / name).read_bytes()).hexdigest() == digest, name
translation = root / "translation"
if translation.exists():
    provenance = json.loads((translation / "provenance.json").read_text())
    report = json.loads((translation / "report.json").read_text())
    payload = (translation / "hashes.tsv").read_bytes()
    assert hashlib.sha256(payload).hexdigest() == provenance["hashes_sha256"]
    assert hashlib.sha256((translation / "report.json").read_bytes()).hexdigest() == provenance["report_sha256"]
    rows = payload.decode().splitlines()
    assert len(rows) == provenance["golden_artifacts"] > 0
    assert sum(row.split("\t")[1] == "pass" for row in rows) == provenance["validated_artifacts"] > 0
    requests = set()
    for row in rows:
        digest, verdict, request = row.split("\t")
        assert re.fullmatch("[0-9a-f]{64}", digest) and verdict == "pass"
        assert request.startswith(("TV1 parity ", "TV1 buchi "))
        assert request not in requests, "duplicate translation request"
        requests.add(request)
    assert "4.35.0" in provenance["lean"] and provenance["date"]
    assert provenance["validation_theorems"] == [
        "Tlsf.Dpa.Validation.validate_parity_sound",
        "Tlsf.Dpa.Validation.validate_buchi_sound"]
    if "compiler_order_validation" in provenance:
        update = provenance["compiler_order_validation"]
        receipt_path = root.parents[2] / update["receipt"]
        assert hashlib.sha256(receipt_path.read_bytes()).hexdigest() == update["sha256"]
        receipt = json.loads(receipt_path.read_text())
        assert receipt["timeout_seconds"] == 17
        assert receipt["validator_executable_sha256"] == provenance["validator_executable_sha256"]
        assert receipt["hashes_sha256"] == provenance["hashes_sha256"]
        count = update["revalidated_artifacts"]
        assert count == receipt["mismatching_rows"] == len(receipt["cases"]) > 0
        assert receipt["outcomes"] == {"pass": count}
        assert update["changed_golden_hashes"] == receipt["changed_golden_hashes"] == 0
        assert len({case["row"] for case in receipt["cases"]}) == count
        for case in receipt["cases"]:
            digest, verdict, request = rows[case["row"] - 1].split("\t")
            assert request == case["request"] and verdict == case["status"] == "pass"
            assert digest == case["fixed_sha256"] == case["golden_sha256"]
            assert digest != case["clang_before_sha256"]
        for name, digest in receipt["source_sha256"].items():
            assert provenance["source_sha256"][name] == digest
    for suite in manifest.values():
        if isinstance(suite, dict) and "general_admission_recoveries" in suite:
            recovery = suite["general_admission_recoveries"]
            assert recovery["translation_hashes_sha256"] == provenance["hashes_sha256"]
    assert report["partial_set"] is None
    assert report["zero_failures"] == (not report["failures"])
    assert report["zero_failures"], "general admission requires zero finished validation failures"
    assert report["fresh_run"] and report["timeout_seconds"] == 17
    assert report["attempted_requests"] == report["formula_ap_orders"] * 4
    assert sum(report["outcomes"].values()) + report["not_admitted_requests"] == report["attempted_requests"]
    assert report["outcomes"].get("fail", 0) == 0
    assert report["outcomes"]["pass"] == provenance["validated_artifacts"] == len(rows)
    assert report["outcomes"].get("timeout", 0) == len(report["timeouts"])
    for timeout in report["timeouts"]:
        assert timeout["request"] not in requests, "timed-out case has a golden"
    assert len(provenance["corpus_sources"]) == 217
    rebindings = provenance.get("source_rebindings", {})
    if rebindings:
        assert rebindings["date"] and rebindings["reason"]
        assert rebindings["checks"] == ["dpa_translation_hashes", "dpa_deadline"]
        assert rebindings["hashes_sha256"] == provenance["hashes_sha256"]
        assert rebindings["artifacts"] == provenance["golden_artifacts"]
        assert rebindings["changed_golden_hashes"] == 0
        assert set(rebindings["sources"]) == {
            "include/tlsf/dpa.h", "src/lib/dpa.c", "src/lib/dpa_internal.h",
            "proofs/TlsfProofs/Dpa/Impl/Buchi.lean",
        }
        for name, binding in rebindings["sources"].items():
            assert set(binding) == {"previous_sha256", "current_sha256"}
            assert binding["previous_sha256"] == provenance["source_sha256"][name]
            assert binding["current_sha256"] != binding["previous_sha256"]
    for name, digest in provenance["source_sha256"].items():
        digest = rebindings.get("sources", {}).get(name, {}).get("current_sha256", digest)
        update = provenance.get("dag_extension", {}).get("sources", {}).get(name)
        if update:
            assert update["previous_sha256"] == digest
            digest = update["current_sha256"]
        assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == retirement_digest(name, digest), name
    for name, digest in provenance["corpus_sources"].items():
        assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest
    for failure in report["failures"]:
        assert failure["status"] == "fail" and failure["minimized"]["disabled"]
        request = " ".join(["TV1", failure["kind"], failure["mode"],
                            str(len(failure["names"])), *failure["names"], failure["prefix"]])
        assert request not in requests, "failing formula has a passing golden"
    expected = {f"{group}/{mode}/{kind}" for group in
                ("corpus", "equivalence", "golden", "review") for mode in
                ("default", "general") for kind in ("parity", "buchi")}
    assert set(report["counts"]) == expected
    for key, counts in report["counts"].items():
        assert set(counts) == {"pass", "fail", "timeout"} and counts["fail"] == 0
        assert sum(counts.values()) + report["not_admitted"].get(key, 0) == report["formulas_per_set"][key.split("/")[0]]
    if "dag_extension" in provenance:
        update = provenance["dag_extension"]
        receipt_path = root.parents[2] / update["receipt"]
        assert hashlib.sha256(receipt_path.read_bytes()).hexdigest() == update["sha256"]
        receipt = json.loads(receipt_path.read_text())
        dag = receipt_path.parent
        dag_report = json.loads((dag / "report.json").read_text())
        assert hashlib.sha256((dag / "hashes.tsv").read_bytes()).hexdigest() == receipt["hashes_sha256"]
        assert hashlib.sha256((dag / "report.json").read_bytes()).hexdigest() == receipt["report_sha256"]
        assert dag_report["fresh_run"] and "4.35.0" in receipt["lean"]
        assert dag_report["normalization_premise"]["authority"] == "caller-trusted"
        assert dag_report["normalization_premise"]["checked_by_this_validator"] is False
        assert "universal C implementation refinement" in dag_report["not_established"]
        assert len(receipt["conditional_objective_theorems"]) == 2
        assert re.fullmatch("[0-9a-f]{40}", receipt["revision"])
        # Preserve the original receipt when only test registration and its
        # provenance guard change. Production/proof sources cannot be rebound.
        test_rebindings = update.get("test_source_rebindings", {})
        if test_rebindings:
            assert test_rebindings["date"] and test_rebindings["reason"]
            assert test_rebindings["checks"] == [
                "native_both_api", "dpa_dag_translation_hashes", "golden_provenance",
            ]
            assert set(test_rebindings["sources"]) == {
                "test/unit/meson.build", "test/cli/check_golden_provenance.py",
            }
            for name, binding in test_rebindings["sources"].items():
                assert set(binding) == {"previous_sha256", "current_sha256"}
                assert binding["previous_sha256"] == receipt["source_sha256"][name]
                assert binding["current_sha256"] != binding["previous_sha256"]
        for name, digest in receipt["source_sha256"].items():
            digest = test_rebindings.get("sources", {}).get(name, {}).get("current_sha256", digest)
            assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == retirement_digest(name, digest), name
        for name, binding in update["sources"].items():
            assert receipt["source_sha256"][name] == binding["current_sha256"]
        cases = dag_report["cases"]
        assert receipt["attempted_requests"] == len(cases)
        assert dict(Counter(c["status"] for c in cases)) == dag_report["outcomes"]
        assert set(dag_report["outcomes"]) <= {"pass", "not_admitted"}
        hashes = {}
        for row in (dag / "hashes.tsv").read_text().splitlines():
            digest, verdict, request = row.split("\t")
            assert re.fullmatch("[0-9a-f]{64}", digest) and verdict == "pass"
            assert request.startswith(("TVD1 parity ", "TVD1 buchi "))
            assert request not in hashes
            hashes[request] = digest
        assert len(hashes) == receipt["validated_artifacts"] == dag_report["outcomes"]["pass"]
        assert {c["kind"] for c in cases if c["status"] == "pass"} == {"parity", "buchi"}
        assert {c["mode"] for c in cases} == {"default", "general"}
        for c in cases:
            if c["status"] == "pass":
                assert hashes[c["request"]] == c["dump_sha256"]
            else:
                assert c["dump_sha256"] is None and c["request"] not in hashes
size = sum(p.stat().st_size for p in root.rglob("*") if p.is_file())
assert size <= 4_400_000, ("golden directory exceeds 4.4 MB", size)
print(f"golden provenance checked; {size} bytes <= 4400000-byte cap")
