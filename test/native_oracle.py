#!/usr/bin/env python3
"""Build pinned 8b158d7 in the Meson build tree and compare step-1 behavior."""

import io
import json
import pathlib
import shutil
import subprocess
import sys
import tarfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
BUILD = pathlib.Path(sys.argv[1]).resolve()
WORK = BUILD / "oracle-8b158d7"
SOURCE = WORK / "source"
REFERENCE = WORK / "reference-build"
SHA = "8b158d7b237693aeae12e7b1b5b3020a199cb1b3"


def command(*args, cwd=ROOT, timeout=300):
    result = subprocess.run(args, cwd=cwd, capture_output=True, timeout=timeout)
    if result.returncode:
        raise AssertionError(f"{args}: {result.stderr.decode(errors='replace')}")
    return result.stdout


def invoke(build, tool, *args):
    return subprocess.run(["./" + tool, *map(str, args)], cwd=build,
                          capture_output=True, timeout=90)


def equal(label, left, right):
    if left != right:
        raise AssertionError(f"{label}: reference={left!r} current={right!r}")


equal("pinned reference", command("git", "rev-parse", "8b158d7^{commit}").strip(),
      SHA.encode())
submodule_revision = command("git", "ls-tree", SHA, "external/oxidd").split()[2]
equal("pinned OxiDD submodule",
      command("git", "-C", str(ROOT / "external/oxidd"), "rev-parse", "HEAD").strip(),
      submodule_revision)
WORK.mkdir(exist_ok=True)
if not (SOURCE / ".oracle-extracted").exists():
    if SOURCE.exists():
        shutil.rmtree(SOURCE)
    SOURCE.mkdir()
    with tarfile.open(fileobj=io.BytesIO(command("git", "archive", SHA))) as tar:
        tar.extractall(SOURCE, filter="data")
    (SOURCE / ".oracle-extracted").write_text(SHA)
submodule = SOURCE / "external" / "oxidd"
if not submodule.is_symlink():
    if submodule.exists():
        submodule.rmdir()
    submodule.symlink_to(ROOT / "external" / "oxidd")
if not (REFERENCE / "tlsfsolve").exists():
    command("meson", "setup", str(REFERENCE), str(SOURCE),
            "-Doxidd=enabled", "-Dresearch_tools=true", "-Dcpp_std=c++20",
            timeout=300)
    command("meson", "compile", "-C", str(REFERENCE), "-j1",
            "tlsf2tlsf", "tlsfsolve", "tlsfcertcheck", timeout=900)

cases = ROOT / "test" / "cases"
provenance = WORK / "provenance.json"
for label, args in (
    ("override provenance", ["--basic", "--param", "n=4",
                             "--provenance-out", provenance,
                             cases / "expand_demo.tlsf"]),
    ("plain override", ["--param", "k=4", cases / "param_demo.tlsf"]),
    ("unknown override", ["--basic", "--param", "missing=1",
                          cases / "expand_demo.tlsf"]),
    ("duplicate override", ["--basic", "--param", "n=4", "--param", "n=5",
                            cases / "expand_demo.tlsf"]),
    ("malformed TLSF", [cases / "bad_syntax.tlsf"]),
):
    outcomes = []
    for build in (REFERENCE, BUILD):
        provenance.unlink(missing_ok=True)
        result = invoke(build, "tlsf2tlsf", *args)
        outcomes.append((result.returncode, result.stdout, result.stderr,
                         provenance.read_bytes() if provenance.exists() else None))
    equal(label, *outcomes)

reference = invoke(REFERENCE, "tlsf2tlsf", "--basic", "--param", "n=4",
                   "--provenance-out", provenance, cases / "expand_demo.tlsf")
equal("reference expansion exit", reference.returncode, 0)
origin = provenance.read_bytes()
provenance.unlink()
direct = invoke(BUILD, "native_api_c", "--expand", cases / "expand_demo.tlsf",
                provenance)
equal("direct expansion exit", direct.returncode, 0)
equal("direct expansion bytes", direct.stdout, reference.stdout)
equal("direct provenance bytes", provenance.read_bytes(), origin)

real = WORK / "real.aag"
real.write_text("aag 3 2 1 1 0 0 0 1 0\n2\n4\n6 6 1\n0\n1\n6\n"
                "i0 u0\ni1 controllable_c0\no0 bad\nj0 justice_0\n")
for label, game, expected in (("real", real, 0),
                              ("unreal", cases / "gr1_fair2.aag", 1)):
    outcomes = []
    certificate = WORK / "certificate.aag"
    policy = WORK / "policy.aag"
    paths = (certificate, pathlib.Path(f"{certificate}.json"),
             policy, pathlib.Path(f"{policy}.json"))
    for build in (REFERENCE, BUILD):
        for path in paths:
            path.unlink(missing_ok=True)
        solve = invoke(build, "tlsfsolve", "--certificate", certificate,
                       "--policy", policy, game)
        equal(f"{label} solve exit", solve.returncode, expected)
        artifacts = tuple(path.read_bytes() for path in paths)
        evidence = WORK / "evidence.json"
        check = invoke(build, "tlsfcertcheck", "--method", "certificate",
                       "--certificate", certificate, "--policy-json", paths[3],
                       "--json-out", evidence, game, policy)
        report = json.loads(evidence.read_text())
        outcomes.append((solve.returncode, solve.stdout, artifacts,
                         check.returncode, report["verdict"],
                         tuple((name, value["verdict"])
                               for name, value in report["methods"].items())))
    equal(f"{label} solve/export/check", *outcomes)
    prefix = WORK / "direct"
    direct = invoke(BUILD, "native_api_c", "--export", game, certificate,
                    policy, prefix)
    equal(f"{label} direct exit", direct.returncode, 0)
    equal(f"{label} direct side", direct.stdout.strip(), str(expected).encode())
    equal(f"{label} direct artifacts",
          tuple(pathlib.Path(f"{prefix}{suffix}").read_bytes() for suffix in
                (".certificate.aag", ".certificate.json", ".policy.aag",
                 ".policy.json")), outcomes[0][2])
    if label == "real":
        for method in ("auto", "closed-loop", "both", "region"):
            reports = []
            for build in (REFERENCE, BUILD):
                evidence = WORK / "method-evidence.json"
                evidence.unlink(missing_ok=True)
                command_line = ["--method", method, "--certificate", certificate,
                                "--certificate-json", paths[1],
                                "--json-out", evidence]
                if method != "region":
                    command_line += ["--policy-json", paths[3], game, policy]
                else:
                    command_line += [game]
                checked = invoke(build, "tlsfcertcheck", *command_line)
                report = json.loads(evidence.read_text())
                reports.append((checked.returncode, report["verdict"],
                                tuple((name, value["verdict"])
                                      for name, value in
                                      report.get("methods", {}).items())))
            equal(f"{label} {method} method", *reports)

malformed = WORK / "malformed.aag"
malformed.write_text("not an aag\n")
for label, tool, args in (
    ("solve malformed", "tlsfsolve", [malformed]),
    ("solve node cap", "tlsfsolve", ["--oxidd-nodes", "1", real]),
    ("check malformed", "tlsfcertcheck", [malformed, malformed]),
    ("check node cap", "tlsfcertcheck",
     ["--node-cap", "1", "--method", "certificate", "--certificate",
      certificate, "--policy-json", paths[3], game, policy]),
):
    results = [invoke(build, tool, *args) for build in (REFERENCE, BUILD)]
    equal(label, (results[0].returncode, results[0].stdout, results[0].stderr),
          (results[1].returncode, results[1].stdout, results[1].stderr))

print("reference 8b158d7 differential passed")
