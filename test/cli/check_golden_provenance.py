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
runtime_update = json.loads((root.parents[2] / "tools/analysis/macos-runtime.json").read_text())
# This build-only update preserves the original validation receipts. It cannot
# rebind translator or proof sources, even if their golden outputs still match.
assert set(runtime_update["source_rebindings"]) == {
    "src/lib/meson.build", "test/cli/check_golden_provenance.py",
}
assert runtime_update["date"] and runtime_update["reason"]

limits_update = json.loads((root.parents[2] / "tools/analysis/native-limits-portability.json").read_text())
# Native GR(1) resource handling changed independently of the DPA translator.
# Keep its historical receipts intact; this ledger cannot rebind DPA/proof
# sources, the reducer, test registration, or any golden payload.
assert set(limits_update["source_rebindings"]) == {
    "include/tlsf/gr1_lift.h", "include/tlsf/gr1_oxidd.h",
    "src/lib/gr1_lift.cc", "src/lib/gr1_oxidd.c", "src/lib/gr1_shared.hh",
    "test/cli/check_golden_provenance.py",
}
assert limits_update["date"] and limits_update["reason"]
assert limits_update["changed_golden_hashes"] == 0
assert set(limits_update["added_sources_sha256"]) == {"src/lib/resource_usage.h"}
for name, digest in limits_update["added_sources_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


row_update = json.loads((root.parents[2] / "tools/analysis/dpa-row-layout.json").read_text())
assert row_update["date"] and row_update["reason"]
assert row_update["checks"] == [
    "full_release_research_tests", "dpa_translation_hashes",
    "dpa_dag_translation_hashes", "dpa_deadline", "dpa_row_identity",
    "proof_source_references", "golden_provenance", "no_external_oracles",
    "lake_build", "clang_format",
]
assert row_update["changed_golden_hashes"] == 0
assert set(row_update["source_rebindings"]) == {
    "proofs/README.md",
    "proofs/TlsfProofs/Dpa/Impl/Admission.lean",
    "proofs/TlsfProofs/Dpa/Impl/Buchi.lean",
    "proofs/TlsfProofs/Dpa/Impl/Classes.lean",
    "proofs/TlsfProofs/Dpa/Impl/Component.lean",
    "proofs/TlsfProofs/Dpa/Impl/Dual.lean",
    "proofs/TlsfProofs/Dpa/Impl/Extractor.lean",
    "proofs/TlsfProofs/Dpa/Impl/Factoring.lean",
    "proofs/TlsfProofs/Dpa/Impl/Selection.lean",
    "proofs/TlsfProofs/Dpa/Impl/Tags.lean",
    "proofs/TlsfProofs/Dpa/Impl/Transport.lean",
    "src/lib/dpa.c", "src/lib/dpa_dela.c", "src/lib/dpa_formula.c",
    "src/lib/dpa_internal.h", "src/lib/dpa_zielonka.c",
    "test/cli/check_golden_provenance.py", "test/cli/check_no_external_oracles.py",
    "test/cli/check_proof_references.py", "test/unit/dpa_contract.c",
    "test/unit/dpa_equivalence.cpp", "test/unit/meson.build", "tools/golden/test_gates.py",
}
assert set(row_update["preserved_artifacts_sha256"]) == {
    "test/fixtures/golden/translation/hashes.tsv",
    "test/fixtures/golden/translation/report.json",
    "test/fixtures/golden/translation/dag/hashes.tsv",
    "test/fixtures/golden/translation/dag/report.json",
    "test/fixtures/golden/translation/dag/provenance.json",
}
for name, digest in row_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


tv1_update = json.loads((root.parents[2] / "tools/analysis/tv1-whitespace.json").read_text())
assert tv1_update["date"] and tv1_update["reason"]
assert tv1_update["checks"] == [
    "golden_provenance", "lake_build", "validator_self_test",
    "translation_validate_tests", "translation_receipt_replay",
    "meson_tests", "no_external_oracles", "reference_semantics_and_oracle_guard",
]
assert tv1_update["changed_golden_hashes"] == 0
assert set(tv1_update["source_rebindings"]) == {
    "proofs/TlsfProofs/Dpa/Validation/Dump.lean",
    "proofs/TlsfProofs/Dpa/Validation/ProtocolChecks.lean",
    "test/cli/check_golden_provenance.py",
}
assert set(tv1_update["preserved_artifacts_sha256"]) == {
    "test/fixtures/golden/translation/hashes.tsv",
    "test/fixtures/golden/translation/report.json",
    "test/fixtures/golden/translation/provenance.json",
    "test/fixtures/golden/translation/dag/hashes.tsv",
    "test/fixtures/golden/translation/dag/report.json",
    "test/fixtures/golden/translation/dag/provenance.json",
    "tools/analysis/dpa-row-layout.json", "tools/golden/historical-files.json",
}
for name, digest in tv1_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name
replay = tv1_update["translation_replay"]
assert replay["receipt"] == "tools/analysis/tv1-whitespace/translation-replay.txt"
assert replay["validated_artifacts"] == sum(
    len((root / suite / "hashes.tsv").read_text().splitlines())
    for suite in ("translation", "translation/dag"))
assert "4.35.0" in replay["lean"]
assert replay["protocol_self_test"] == "57 protocol checks, 0 failures"
assert re.fullmatch("[0-9a-f]{64}", replay["validator_executable_sha256"])
receipt = root.parents[2] / replay["receipt"]
assert hashlib.sha256(receipt.read_bytes()).hexdigest() == replay["sha256"]
assert receipt.read_text() == f"{replay['validated_artifacts']} passing requests revalidated by {replay['lean']}\n"


fuzz_update = json.loads((root.parents[2] / "tools/analysis/generated-input-tests.json").read_text())
assert fuzz_update["date"] and fuzz_update["reason"]
assert fuzz_update["checks"] == [
    "gcc_full_tests", "clang_full_tests", "translation_receipt_replay",
    "no_benchmark_hardcoding", "clang_format",
]
assert fuzz_update["changed_golden_hashes"] == 0
assert set(fuzz_update["source_rebindings"]) == {
    "meson.build", "meson.options", "src/lib/print_tlsf.c",
    "test/cli/check_golden_provenance.py",
}
for name, binding in fuzz_update["source_rebindings"].items():
    assert set(binding) == {"previous_sha256", "current_sha256"}
    assert all(re.fullmatch("[0-9a-f]{64}", digest) for digest in binding.values()), name
    assert binding["previous_sha256"] != binding["current_sha256"], name
assert set(fuzz_update["preserved_artifacts_sha256"]) == set(tv1_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/tv1-whitespace.json", "tools/analysis/tv1-whitespace/translation-replay.txt",
}
for name, digest in fuzz_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name
replay = fuzz_update["translation_replay"]
assert replay["receipt"] == "tools/analysis/generated-input-tests/translation-replay.txt"
assert replay["validated_artifacts"] == tv1_update["translation_replay"]["validated_artifacts"]
assert "4.35.0" in replay["lean"]
assert replay["protocol_self_test"] == "57 protocol checks, 0 failures"
assert re.fullmatch("[0-9a-f]{64}", replay["validator_executable_sha256"])
receipt = root.parents[2] / replay["receipt"]
assert hashlib.sha256(receipt.read_bytes()).hexdigest() == replay["sha256"]
assert receipt.read_text() == f"{replay['validated_artifacts']} passing requests revalidated by {replay['lean']}\n"


f3_update = json.loads((root.parents[2] / "tools/analysis/f3-target-adaptation.json").read_text())
assert f3_update["date"] and f3_update["reason"]
assert f3_update["checks"] == [
    "gcc_full_tests", "f3_alloc_replay", "clang_fuzz_build",
    "clang_layout_provenance_replays", "target_adaptation", "objective_alloc",
    "no_benchmark_hardcoding", "clang_format",
]
assert f3_update["changed_golden_hashes"] == 0
assert set(f3_update["source_rebindings"]) == {
    "src/lib/expand.c", "src/lib/spec.c", "test/cli/check_golden_provenance.py",
}
golden_files = {str(path.relative_to(root.parents[2])) for path in root.rglob("*") if path.is_file()}
assert set(f3_update["preserved_artifacts_sha256"]) == golden_files | set(fuzz_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/generated-input-tests.json",
    "tools/analysis/generated-input-tests/translation-replay.txt",
}
for name, digest in f3_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


expansion_update = json.loads((root.parents[2] / "tools/analysis/expansion-allocation-and-equality.json").read_text())
assert expansion_update["date"] and expansion_update["reason"]
assert expansion_update["checks"] == [
    "gcc_full_tests", "clang_fuzz_build", "clang_layout_provenance_replays",
    "target_adaptation", "objective_alloc", "finite_set_next_goldens",
    "native_and_translation_replay", "no_benchmark_hardcoding", "clang_format",
]
assert expansion_update["changed_golden_hashes"] == 0
assert set(expansion_update["source_rebindings"]) == {
    "src/lib/expand.c", "test/cli/check_golden_provenance.py",
}
assert set(expansion_update["preserved_artifacts_sha256"]) == set(f3_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/f3-target-adaptation.json",
}
for name, digest in expansion_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


provenance_rollback = json.loads((root.parents[2] / "tools/analysis/expansion-provenance-rollback.json").read_text())
assert provenance_rollback["date"] and provenance_rollback["reason"]
assert provenance_rollback["checks"] == [
    "gcc_full_tests", "clang_layout_provenance_replays", "objective_alloc",
    "native_and_translation_replay", "no_benchmark_hardcoding", "clang_format",
    "successful_provenance_byte_identity",
]
assert provenance_rollback["changed_golden_hashes"] == 0
assert set(provenance_rollback["source_rebindings"]) == {
    "src/lib/expand.c", "test/cli/check_golden_provenance.py",
}
assert set(provenance_rollback["preserved_artifacts_sha256"]) == set(expansion_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/expansion-allocation-and-equality.json",
}
for name, digest in provenance_rollback["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


substitution_update = json.loads((root.parents[2] / "tools/analysis/expansion-substitution-provenance.json").read_text())
assert substitution_update["date"] and substitution_update["reason"]
assert substitution_update["checks"] == provenance_rollback["checks"]
assert substitution_update["changed_golden_hashes"] == 0
assert set(substitution_update["source_rebindings"]) == {
    "src/lib/expand.c", "test/cli/check_golden_provenance.py",
}
assert set(substitution_update["preserved_artifacts_sha256"]) == set(provenance_rollback["preserved_artifacts_sha256"]) | {
    "tools/analysis/expansion-provenance-rollback.json",
}
for name, digest in substitution_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


success_update = json.loads((root.parents[2] / "tools/analysis/expansion-success-provenance.json").read_text())
assert success_update["date"] and success_update["reason"]
assert success_update["checks"] == substitution_update["checks"]
assert success_update["changed_golden_hashes"] == 0
assert set(success_update["source_rebindings"]) == {
    "src/lib/expand.c", "test/cli/check_golden_provenance.py",
}
assert set(success_update["preserved_artifacts_sha256"]) == set(substitution_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/expansion-substitution-provenance.json",
}
for name, digest in success_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


shared_update = json.loads((root.parents[2] / "tools/analysis/expansion-shared-provenance.json").read_text())
assert shared_update["date"] and shared_update["reason"]
assert shared_update["checks"] == success_update["checks"]
assert shared_update["changed_golden_hashes"] == 0
assert set(shared_update["source_rebindings"]) == {
    "src/lib/expand.c", "test/cli/check_golden_provenance.py",
}
assert set(shared_update["preserved_artifacts_sha256"]) == set(success_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/expansion-success-provenance.json",
}
for name, digest in shared_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


vptr_update = json.loads((root.parents[2] / "tools/analysis/fuzz-vptr-portability.json").read_text())
assert vptr_update["date"] and vptr_update["reason"]
assert vptr_update["checks"] == [
    "clang_fuzz_build", "clang_c_driver_link", "clang_provenance_replays",
    "gcc_full_tests", "clang_format",
]
assert vptr_update["changed_golden_hashes"] == 0
assert set(vptr_update["source_rebindings"]) == {
    "meson.build", "test/cli/check_golden_provenance.py",
}
assert set(vptr_update["preserved_artifacts_sha256"]) == set(shared_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/expansion-shared-provenance.json",
}
for name, digest in vptr_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


dedup_update = json.loads((root.parents[2] / "tools/analysis/set-dedup-108.json").read_text())
assert dedup_update["date"] and dedup_update["reason"]
assert dedup_update["checks"] == [
    "set_dedup", "set_dedup_field_inventory", "ltl_finite_set_next",
    "ltl_finite_set_next_reversed", "full_meson_tests", "lake_build",
    "proof_source_references", "golden_provenance", "no_external_oracles",
]
assert dedup_update["changed_golden_hashes"] == 0
assert set(dedup_update["source_rebindings"]) == {
    "proofs/README.md", "proofs/TlsfProofs.lean", "src/lib/expand.c",
    "test/cli/meson.build", "test/unit/meson.build",
    "test/cli/check_golden_provenance.py",
}
assert set(dedup_update["preserved_artifacts_sha256"]) == set(vptr_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/fuzz-vptr-portability.json",
}
for name, digest in dedup_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name


scoping_update = json.loads((root.parents[2] / "tools/analysis/tlsf-scoping-110.json").read_text())
precedence_update = scoping_update["precedence110j"]
boundary_update = scoping_update["precedence110k"]
partition_update = scoping_update["precedence110l"]
perf_update = scoping_update["perf112"]
grammar_update = scoping_update["grammar112g"]
assert grammar_update["date"] and grammar_update["reason"]
assert grammar_update["changed_golden_hashes"] == 0
assert set(grammar_update["source_rebindings"]) == {
    "README.md", "proofs/README.md", "src/lib/tlsf.y", "src/lib/meson.build",
    "src/lib/spec_parse.c", "test/cli/check_case_boundaries_110.py",
    "test/cli/check_golden_provenance.py",
}
assert grammar_update["removed_sources_sha256"] == partition_update["added_sources_sha256"]
for name in grammar_update["removed_sources_sha256"]:
    assert not (root.parents[2] / name).exists(), name


def grammar_digest(name, historical):
    binding = grammar_update["source_rebindings"].get(name)
    if binding:
        assert historical == binding["previous_sha256"], name
        return binding["current_sha256"]
    return historical


assert perf_update["date"] and perf_update["reason"]
assert perf_update["changed_golden_hashes"] == 0
assert set(perf_update["source_rebindings"]) == {
    "include/tlsf/arena.h", "src/lib/arena.c", "src/lib/expand_check.c",
    "test/cli/check_scoping_110.py",
    "test/cli/check_golden_provenance.py",
}


def perf_digest(name, historical):
    binding = perf_update["source_rebindings"].get(name)
    if binding:
        assert historical == binding["previous_sha256"], name
        historical = binding["current_sha256"]
    return grammar_digest(name, historical)


assert partition_update["date"] and partition_update["reason"]
assert partition_update["changed_golden_hashes"] == 0
assert set(partition_update["source_rebindings"]) == {
    "README.md", "src/lib/tlsf.y", "test/cli/check_case_boundaries_110.py",
    "test/cli/check_golden_provenance.py", "src/lib/meson.build",
    "src/lib/spec_parse.c",
}
assert set(partition_update["added_sources_sha256"]) == {
    "src/lib/case_boundaries.c", "src/lib/case_boundaries.h",
    "src/lib/tlsf_boundary.y",
}
# Removed files retain their original addition hashes in the retirement entry.
for name, digest in partition_update["added_sources_sha256"].items():
    assert grammar_update["removed_sources_sha256"][name] == digest, name
assert boundary_update["date"] and boundary_update["reason"]
assert boundary_update["changed_golden_hashes"] == 0
assert set(boundary_update["source_rebindings"]) == {
    "README.md", "src/lib/tlsf.y", "test/cli/check_golden_provenance.py",
    "test/cli/meson.build",
}
assert set(boundary_update["added_sources_sha256"]) == {
    "test/cli/check_case_boundaries_110.py",
}
for name, digest in boundary_update["added_sources_sha256"].items():
    binding = partition_update["source_rebindings"].get(name)
    if binding:
        assert binding["previous_sha256"] == digest, name
        digest = binding["current_sha256"]
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == grammar_digest(name, digest), name
assert precedence_update["date"] and precedence_update["reason"]
assert precedence_update["changed_golden_hashes"] == 0
assert set(precedence_update["added_sources_sha256"]) == {
    "test/cli/check_precedence_110.py", "test/fixtures/scoping110/precedence_v12.ltl",
}
for name, digest in precedence_update["added_sources_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name
for name, replacement in precedence_update["fixture_replacements"].items():
    assert replacement["reason"]
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == replacement["previous_sha256"]
    assert replacement["replacement"] in precedence_update["added_sources_sha256"]
    assert replacement["current_sha256"] == precedence_update["added_sources_sha256"][replacement["replacement"]]
assert set(precedence_update["record_replacements"]) == {"native-reduction"}
patches = precedence_update["record_replacements"]["native-reduction"]
assert len(patches) == 4
records = json.loads((root / "native-reduction.json").read_text())
for patch, semantics in zip(patches, ("exact", "strict", "exact", "strict")):
    index = patch["index"]
    assert patch["reason"]
    assert records[index:index + len(patch["before"])] == patch["before"]
    if patch["source"] == "test/fixtures/cases/precedence_v12.tlsf":
        assert patch["before"][0] == ["status", ["precedence_v12.tlsf", semantics, 0]]
        assert patch["after"] == [
            ["status", ["precedence_v12.tlsf", semantics, 3]],
            ["decline", "reduce status 1: mp-class: outside proved DPA Buchi fragment\n"],
        ]
    else:
        assert patch["source"] == "test/fixtures/cases/recursion.reemit.tlsf"
        assert patch["before"][0] == patch["after"][0] == [
            "status", ["recursion.reemit.tlsf", semantics, 2]]
        assert patch["after"][1] == [
            "decline", "pipeline: parse: 15:74: parse error: syntax error, unexpected TOK_SEMI\n"]
    assert hashlib.sha256((root.parents[2] / patch["source"]).read_bytes()).hexdigest() == patch["source_sha256"]
assert scoping_update["date"] and scoping_update["reason"]
assert scoping_update["changed_golden_hashes"] == 0
assert set(scoping_update["source_rebindings"]) == {
    "README.md", "include/tlsf/ast.h", "proofs/README.md", "proofs/TlsfProofs/SetDedup.lean",
    "src/lib/expand.c", "src/lib/spec.c", "src/lib/meson.build", "test/api/convert.cpp",
    "test/api/decompose_cpp.cpp", "test/cli/check_golden_provenance.py",
    "test/cli/meson.build", "test/oracle/golden.py",
    "test/unit/meson.build", "test/unit/set_dedup_field_inventory.py",
    "test/unit/objective_alloc.c", "test/unit/set_dedup.c",
    "test/cli/check_exactness_guards.py",
    "test/oracle/test_compose_driver_semantics.py",
    "test/oracle/test_decomposition_exactness.py",
    "test/oracle/test_review4_exports.py",
    "test/cli/test_frontend_provenance.py", "test/oracle/test_gr1_monitor_game.py",
}
assert set(scoping_update["added_sources_sha256"]) == {
    "src/lib/expand_check.c", "src/lib/expand_check.h",
    "test/cli/check_scoping_110.py", "test/cli/scoping_110_reviews.json",
    "test/unit/expansion_scope.c", "tools/analysis/impact110.py",
    "test/fixtures/scoping110/aiger_unclassified_atom.stderr",
    "test/fixtures/scoping110/issue110.tlsf",
    "test/fixtures/scoping110/cup_overlap.tlsf",
    "test/fixtures/scoping110/identity_sugar.tlsf",
    "test/fixtures/scoping110/identity_strength.tlsf",
    "test/fixtures/scoping110/pattern_conflict_v12.stderr",
    "test/fixtures/scoping110/undeclared_at_atom.stderr",
    *("test/fixtures/scoping110/monitor/" + name + ".tlsf" for name in (
        "arbiter_on_inpchange_pb_2_pe_", "arbiter_pb_2_pe_",
        "arbiter_pb_3_pe_", "arbiter_pb_4_pe_")),
}
assert set(scoping_update["preserved_artifacts_sha256"]) >= set(dedup_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/set-dedup-108.json",
}
for name, digest in scoping_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name
for name, digest in scoping_update["added_sources_sha256"].items():
    binding = precedence_update["source_rebindings"].get(name)
    if binding:
        assert binding["previous_sha256"] == digest, name
        digest = binding["current_sha256"]
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == perf_digest(name, digest), name
for name, entry in scoping_update["fixture_replacements"].items():
    assert entry["reason"] and entry["replacement"] in scoping_update["added_sources_sha256"]
    assert entry["previous_sha256"] == scoping_update["preserved_artifacts_sha256"][name]
    assert entry["current_sha256"] == scoping_update["added_sources_sha256"][entry["replacement"]]
assert scoping_update["golden_source_hash_replacements"] == {
    entry["previous_sha256"]: entry["current_sha256"]
    for entry in scoping_update["fixture_replacements"].values()
}
assert len(scoping_update["expectation_changes"]) == 6
for entry in scoping_update["expectation_changes"]:
    assert entry["file"] in scoping_update["preserved_artifacts_sha256"]
    assert entry["reason"] and entry["before"] and entry["after"]
assert set(scoping_update["record_replacements"]) == {"native-reduction", "monitor-game"}
assert len(scoping_update["record_replacements"]["native-reduction"]) == 12
assert len(scoping_update["record_replacements"]["monitor-game"]) == 1
for suite, patches in scoping_update["record_replacements"].items():
    records = json.loads((root / (suite + ".json")).read_text())
    end = 0
    for patch in patches:
        index = patch["index"]
        assert index >= end and patch["reason"]
        end = index + len(patch["before"])
        assert records[index:end] == patch["before"]
        if suite == "native-reduction":
            assert patch["source"] in scoping_update["preserved_artifacts_sha256"]
        else:
            assert patch["source_generator"] == "test/oracle/test_gr1_monitor_game.py"
            assert patch["source_generator"] in scoping_update["source_rebindings"]
            assert hashlib.sha256(patch["source_text"].encode()).hexdigest() == patch["source_sha256"]
            assert patch["before"][0] == ["reduce", ["collision", "exact", 3]]
            assert patch["after"][0] == ["reduce", ["collision", "exact", 2]]
            assert "collides with flattened bus bit" in patch["after"][1][1]
        assert patch["after"][0][0] == ("status" if suite == "native-reduction" else "reduce")
        assert patch["after"][0][1][-1] == 2
        assert patch["after"][0][1][:2] == patch["before"][0][1][:2]
        assert patch["after"][1][0] == "decline"
        assert "pipeline: expand: expand: " in patch["after"][1][1]
for suite, count in scoping_update["golden_source_hash_occurrences"].items():
    payload = (root / (suite + ".json")).read_text()
    assert sum(payload.count(digest) for digest in
               scoping_update["golden_source_hash_replacements"]) == count > 0
assert len(scoping_update["generated_source_repairs"]) == 4
for repair in scoping_update["generated_source_repairs"]:
    assert repair["file"] in scoping_update["source_rebindings"] and repair["reason"]

strict_bounds_update = json.loads((root.parents[2] / "tools/analysis/strict-bounds-114.json").read_text())
assert strict_bounds_update["date"] and strict_bounds_update["reason"]
assert strict_bounds_update["checks"] == [
    "gcc_full_tests", "strict_bounds_114", "normalize_bounds",
    "native_and_translation_replay", "no_benchmark_hardcoding", "clang_format",
]
assert strict_bounds_update["changed_golden_hashes"] == 0
assert set(strict_bounds_update["source_rebindings"]) == {
    "src/lib/expand.c", "src/lib/normalize.c", "test/cli/meson.build",
    "test/unit/meson.build", "test/cli/check_golden_provenance.py",
}
assert set(strict_bounds_update["preserved_artifacts_sha256"]) == set(scoping_update["preserved_artifacts_sha256"]) | {
    "tools/analysis/tlsf-scoping-110.json",
}
for name, digest in strict_bounds_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name
assert set(strict_bounds_update["added_sources_sha256"]) == {
    "test/cli/check_strict_bounds.py", "test/fixtures/printer/strict_bounds.json",
    "test/unit/normalize_bounds.c",
}
for name, digest in strict_bounds_update["added_sources_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name

integer_next_update = json.loads((root.parents[2] / "tools/analysis/integer-next-115-117.json").read_text())
assert integer_next_update["date"] and integer_next_update["reason"]
assert integer_next_update["changed_golden_hashes"] == 0
assert set(integer_next_update["source_rebindings"]) == {
    "src/lib/expand.c", "src/lib/normalize.c", "src/lib/tlsf.l", "src/lib/tlsf.y",
    "test/cli/meson.build", "test/cli/check_golden_provenance.py",
}
assert set(integer_next_update["added_sources_sha256"]) == {
    "test/cli/check_integer_next.py", "test/fixtures/printer/checked_integer.json",
    "test/fixtures/printer/indexed_next.json",
}
assert set(integer_next_update["preserved_artifacts_sha256"]) == {"tools/analysis/strict-bounds-114.json"}
for field in ("added_sources_sha256", "preserved_artifacts_sha256"):
    for name, digest in integer_next_update[field].items():
        assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name

literal_update = json.loads((root.parents[2] / "tools/analysis/integer-literal-116.json").read_text())
assert literal_update["date"] and literal_update["reason"]
assert literal_update["changed_golden_hashes"] == 0
assert literal_update["checks"] == [
    "integer_literal_116", "integer_literal_cli_116", "proof_source_references",
    "golden_provenance", "full_meson_tests", "lake_build", "lean_axiom_audit",
]
assert set(literal_update["source_rebindings"]) == {
    "proofs/README.md", "proofs/TlsfProofs.lean", "test/unit/meson.build",
    "test/cli/meson.build", "test/cli/check_golden_provenance.py",
}
assert set(literal_update["added_sources_sha256"]) == {
    "proofs/TlsfProofs/IntegerLiteral.lean", "test/unit/integer_literal.c",
    "test/cli/check_integer_literal.py",
}
assert set(literal_update["correspondence_sources_sha256"]) == {
    "src/lib/tlsf.l", "src/lib/tlsf.y", "src/lib/expand.c", "src/lib/spec_parse.c",
}
assert set(literal_update["preserved_artifacts_sha256"]) == set(
    strict_bounds_update["preserved_artifacts_sha256"]) | {
        "tools/analysis/strict-bounds-114.json", "tools/analysis/integer-next-115-117.json",
    }
for name, digest in literal_update["preserved_artifacts_sha256"].items():
    assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == digest, name

UPDATES = (retirement, runtime_update, limits_update, row_update, tv1_update,
           fuzz_update, f3_update, expansion_update, provenance_rollback,
           substitution_update, success_update, shared_update, vptr_update,
           dedup_update, scoping_update, precedence_update, boundary_update,
           partition_update, perf_update, grammar_update, strict_bounds_update,
           integer_next_update, literal_update)


def rebound_digest(name, historical, updates=UPDATES):
    for update in updates:
        binding = update["source_rebindings"].get(name)
        if binding:
            assert historical == binding["previous_sha256"], (name, "wrong historical source binding")
            historical = binding["current_sha256"]
    return historical


# New proof/test sources and unchanged correspondence sources may be rebound by
# later ledgers; frozen receipts above must remain byte-for-byte unchanged.
for field in ("added_sources_sha256", "correspondence_sources_sha256"):
    for name, digest in literal_update[field].items():
        successors = UPDATES[UPDATES.index(literal_update) + 1:]
        assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == rebound_digest(
            name, digest, successors), name


for index, update in enumerate(UPDATES[3:], 3):
    successors = UPDATES[index + 1:]
    for name, binding in update["source_rebindings"].items():
        assert set(binding) == {"previous_sha256", "current_sha256"}
        assert all(re.fullmatch("[0-9a-f]{64}", digest) for digest in binding.values()), name
        assert binding["previous_sha256"] != binding["current_sha256"], name
        assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == rebound_digest(
            name, binding["current_sha256"], successors), name


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
        assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == rebound_digest(name, digest), name
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
            assert hashlib.sha256((root.parents[2] / name).read_bytes()).hexdigest() == rebound_digest(name, digest), name
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
