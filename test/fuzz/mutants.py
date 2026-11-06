#!/usr/bin/env python3
"""Recompile one-line library mutants in a disposable copy; never edit the tree."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def command(args, build, log):
    subprocess.run(args, cwd=build, stdout=log, stderr=log, check=True)


def compile_mutant(record, build, source, entries, links, log):
    relative = Path(record["file"])
    if relative.parent != Path("src/lib") or relative.suffix != ".c":
        raise ValueError(f"not a library C source: {relative}")
    original = ROOT / relative
    destination = source / relative
    if destination.resolve().is_relative_to(ROOT):
        raise ValueError("refusing to edit the source tree")
    lines = original.read_text().splitlines(keepends=True)
    index = record["line"] - 1
    if "\n" in record["old"] or "\n" in record["new"]:
        raise ValueError("mutants must change exactly one line")
    if lines[index] != record["old"] + "\n" or record["old"] == record["new"]:
        raise ValueError(f"stale/no-op mutant: {record['check']}")
    lines[index] = record["new"] + "\n"
    destination.write_text("".join(lines))
    entry = next(e for e in entries
                 if (build / e["file"]).resolve() == original)
    args = shlex.split(entry["command"])
    obj = source / "mutant.o"
    # Redirect every compiler output, including dependency files, into tempdir.
    for option, value in (("-o", obj), ("-MF", source / "mutant.d"), ("-MQ", obj)):
        if option in args:
            args[args.index(option) + 1] = str(value)
    args[args.index(entry["file"])] = str(destination)
    command(args, build, log)
    args = links[record["target"]].copy()
    output = args.index("-o") + 1
    replay = build / args[output]
    executable = source / "mutant-replay"
    args[output] = str(executable)
    # The replacement object precedes the archive: its original is not extracted.
    args.insert(args.index("src/lib/libtlsf.a"), str(obj))
    args = [a.replace("$ORIGIN", str(replay.parent)) for a in args]
    command(args, build, log)
    return executable


def run_seed(executable, seed):
    env = dict(os.environ, ASAN_OPTIONS="detect_leaks=0")
    return subprocess.run([executable, seed], capture_output=True, env=env,
                          timeout=30)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("build", type=Path, help="configured GCC or Clang build")
    args = parser.parse_args()
    build = args.build.resolve()
    records = json.loads((ROOT / "test/fuzz/mutants.json").read_text())
    active = [r for r in records if "removed" not in r]
    checks = {c for p in (ROOT / "test/fuzz").glob("*.c")
              for c in re.findall(r"CHECK\((\w+),", p.read_text())}
    if checks != {r["check"] for r in active} or len(active) != len(checks):
        raise ValueError("every active check must have exactly one mutant")
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    targets = sorted({r["target"] for r in active})
    with (build / "fuzz-mutants.log").open("w") as log:
        command(["ninja", "-j", "1", *[
            f"test/fuzz/fuzz-{t}-replay" for t in targets]], build, log)
        entries = json.loads((build / "compile_commands.json").read_text())
        links = {t: shlex.split(subprocess.check_output(
            ["ninja", "-t", "commands", f"test/fuzz/fuzz-{t}-replay"],
            cwd=build, text=True).splitlines()[-1]) for t in targets}
        failed = 0
        with tempfile.TemporaryDirectory(prefix="tlsf-mutants-") as tmp:
            source = Path(tmp)
            shutil.copytree(ROOT / "src/lib", source / "src/lib")
            for record in active:
                seed = ROOT / "test/fuzz/corpus" / record["target"] / record["seed"]
                if hashlib.sha1(seed.read_bytes()).hexdigest() != record["seed"]:
                    raise ValueError(f"seed SHA-1 mismatch: {seed}")
                # Also reject a seed that already fails without the mutation.
                baseline = run_seed(build / f"test/fuzz/fuzz-{record['target']}-replay", seed)
                if baseline.returncode:
                    raise ValueError(f"baseline fails: {record['check']}")
                executable = compile_mutant(record, build, source, entries, links, log)
                result = run_seed(executable, seed)
                log.write(f"\n{record['check']} {record['seed']} rc={result.returncode}\n")
                log.write(result.stdout.decode(errors="replace"))
                log.write(result.stderr.decode(errors="replace"))
                killed = (result.returncode == -signal.SIGABRT and
                          f"CHECK {record['check']} failed\n".encode() in result.stderr)
                failed += not killed
                print(f"{record['check']} {record['seed']} {'KILLED' if killed else 'FAIL'}", flush=True)
                # Other copied library files always retain their original bytes.
                (source / record["file"]).write_bytes((ROOT / record["file"]).read_bytes())
        for record in records:
            if "removed" in record:
                print(f"{record['check']} REMOVED: {record['removed']}")
        print(f"{len(active) - failed}/{len(active)} killed at the recorded check; log: {log.name}")
        return bool(failed)


if __name__ == "__main__":
    raise SystemExit(main())
