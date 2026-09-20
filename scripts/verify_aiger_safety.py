#!/usr/bin/env python3
"""Independently verify a legacy-safety controller using AIGER and ABC PDR.

Exit 0 means proven safe, 1 means a counterexample, 2 means unknown/error.
The original game supplies the property and plant state. The controller's
private state is kept separate when combine-aiger closes the loop.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys
import time


def interface(path):
    """Inspect canonical ASCII produced/validated by the external AIGER reader."""
    lines = path.read_text().splitlines()
    header = lines[0].split()
    if header[0] != "aag" or not 6 <= len(header) <= 10:
        raise ValueError("expected canonical ASCII AIGER")
    counts = list(map(int, header[1:]))
    counts += [0] * (9 - len(counts))
    _, ni, nl, no, na, nb, nc, nj, nf = counts
    if any((nc, nj, nf)):
        raise ValueError("constraints and liveness properties are unsupported")
    for line in lines[1 + ni:1 + ni + nl]:
        latch = list(map(int, line.split()))
        if len(latch) == 3 and latch[2] not in (0, 1):
            raise ValueError("only constant latch resets are supported")
    names = {"i": {}, "o": {}}
    for line in lines[1 + ni + nl + no + nb + na:]:
        if line == "c":
            break
        if line and line[0] in names:
            key, name = line.split(" ", 1)
            index = int(key[1:])
            if index in names[key[0]] or not name:
                raise ValueError("missing or duplicate interface symbol")
            names[key[0]][index] = name
    result = {"counts": counts, "inputs": [], "outputs": []}
    for kind, count, label in (("i", ni, "inputs"), ("o", no, "outputs")):
        # The game error output can be unnamed; callers validate signal ports.
        ports = [names[kind].get(i) for i in range(count)]
        named = [name for name in ports if name is not None]
        if len(set(named)) != len(named):
            raise ValueError(f"duplicate {label}")
        if any(name.startswith("AIGER_NEXT_") for name in named):
            raise ValueError("combine-aiger's special AIGER_NEXT_ aliases are unsupported")
        result[label] = ports
    return result


def validate_ports(game, controller):
    if game["counts"][3] != 1 or any(game["counts"][5:]):
        raise ValueError("game must have O=1, B=C=J=F=0 (legacy-safety)")
    if any(controller["counts"][5:]):
        raise ValueError("controller must not contain properties")
    if None in game["inputs"] + controller["inputs"] + controller["outputs"]:
        raise ValueError("game inputs and controller ports must be named")
    controlled = {name for name in game["inputs"] if name.startswith("controllable_")}
    environment = set(game["inputs"]) - controlled
    if set(controller["outputs"]) != controlled:
        raise ValueError("controller outputs must exactly match controllable_ game inputs")
    if not set(controller["inputs"]) <= environment:
        raise ValueError("controller inputs must be environmental game inputs")
    return environment


def fingerprint(path):
    path = Path(path).resolve(strict=True)
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return {"path": str(path), "sha256": digest.hexdigest()}


def executable(name):
    found = shutil.which(str(name))
    if found is None:
        raise ValueError(f"executable not found: {name}")
    return str(Path(found).resolve())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--game", required=True, type=Path)
    parser.add_argument("--strategy", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path, help="new evidence directory")
    parser.add_argument("--aiger-dir", type=Path, help="directory with aigmove and aigtoaig")
    parser.add_argument("--combine-aiger", default="combine-aiger")
    parser.add_argument("--abc", default="abc")
    parser.add_argument("--timeout", type=float, default=120, help="seconds per external step")
    args = parser.parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("--timeout must be finite and positive")
    out = args.out.resolve()
    try:
        out.mkdir(parents=True, exist_ok=False)
    except OSError as exc:
        parser.error(str(exc))
    result = {"status": "ERROR", "steps": [], "tools": {}}

    def run(label, command, stdout=None):
        step = {"label": label, "command": list(map(str, command))}
        result["steps"].append(step)
        start = time.monotonic()
        try:
            with (out / (stdout or f"{label}.stdout")).open("wb") as output:
                with (out / f"{label}.stderr").open("wb") as error:
                    proc = subprocess.run(command, cwd=out, stdout=output, stderr=error,
                                          timeout=args.timeout, check=False)
            step["returncode"] = proc.returncode
            if proc.returncode:
                raise ValueError(f"{label} failed with exit {proc.returncode}")
        except subprocess.TimeoutExpired:
            result["status"] = "UNKNOWN"
            raise ValueError(f"{label} timed out") from None
        finally:
            step["seconds"] = round(time.monotonic() - start, 6)

    try:
        for label in ("game", "strategy"):
            result[label] = fingerprint(getattr(args, label))
        commands = {"combine-aiger": args.combine_aiger, "abc": args.abc}
        for label in ("aigmove", "aigtoaig"):
            commands[label] = args.aiger_dir / label if args.aiger_dir else label
        for label, command in commands.items():
            commands[label] = executable(command)
            result["tools"][label] = fingerprint(commands[label])

        for label in ("game", "strategy"):
            run(f"read-{label}", [commands["aigtoaig"],
                                 result[label]["path"], f"{label}.aag"])
        environment = validate_ports(interface(out / "game.aag"),
                                     interface(out / "strategy.aag"))
        run("property", [commands["aigmove"], "-r", "game.aag", "monitor.aag"])
        run("compose", [commands["combine-aiger"], "monitor.aag", "strategy.aag"],
            stdout="composed.aag")
        run("validate-composition", [commands["aigtoaig"], "composed.aag",
                                     "closed-loop.aag"])
        closed = interface(out / "closed-loop.aag")
        if (set(closed["inputs"]) != environment or closed["counts"][3] != 0
                or closed["counts"][5] != 1):
            raise ValueError("composition must retain only environment inputs and one bad property")
        run("binary", [commands["aigtoaig"], "closed-loop.aag", "closed-loop.aig"])
        result["closed_loop"] = fingerprint(out / "closed-loop.aig")
        # Fixed filenames avoid injecting paths into ABC's command interpreter.
        # -s disables user startup scripts. PDR is unbounded; BMC is insufficient.
        run("proof", [commands["abc"], "-s", "-c",
                      "read_aiger closed-loop.aig; pdr; write_status proof.status"])
        status = (out / "proof.status").read_text().split()[0]
        result["status"] = {"snl_UNSAT": "SAFE", "snl_SAT": "UNSAFE",
                            "snl_UNK": "UNKNOWN"}.get(status, "ERROR")
    except (OSError, ValueError, IndexError) as exc:
        result["error"] = str(exc)
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"] + (": " + result["error"] if "error" in result else ""))
    return {"SAFE": 0, "UNSAFE": 1}.get(result["status"], 2)


if __name__ == "__main__":
    sys.exit(main())
