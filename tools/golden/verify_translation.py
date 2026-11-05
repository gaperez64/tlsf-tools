"""Replay the existing C/Lean receipts without changing historical hashes."""
from translation_validate import ROOT, SCRATCH, build_validator, validate_one


def verify(build, output):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    validator, version, checks = build_validator()
    print(version, checks, flush=True)
    count = 0
    for relative in ("translation", "translation/dag"):
        path = ROOT / "test/fixtures/golden" / relative / "hashes.tsv"
        for line in path.read_text().splitlines():
            expected, verdict, request = line.split("\t")
            assert verdict == "pass"
            status, reason, actual = validate_one(build, validator, request, 17)
            assert status == "pass" and actual == expected, (relative, request, status, reason, actual, expected)
            count += 1
            if count % 200 == 0:
                print(f"C/Lean receipt replay: {count} passed", flush=True)
    (output / "translation-replay.txt").write_text(f"{count} passing requests revalidated by {version}\n")
    print(f"C/Lean: {count} passing requests replayed; every dump hash unchanged", flush=True)
