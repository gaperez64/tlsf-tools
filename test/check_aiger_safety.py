#!/usr/bin/env python3
"""End-to-end checks with the actual external composition and proof tools."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--aiger-dir", required=True)
    parser.add_argument("--combine-aiger", required=True)
    parser.add_argument("--abc", required=True)
    args = parser.parse_args()
    verifier = Path(__file__).resolve().parents[1] / "scripts/verify_aiger_safety.py"
    # q' = u, initially q=1; bad = controllable_c XOR q.
    memory_game = "aag 6 2 1 1 3\n2\n4\n6 2 1\n12\n8 4 6\n10 5 7\n12 9 11\ni0 u\ni1 controllable_c\n"
    memory_controller = "aag 2 1 1 1 0\n2\n4 2 1\n4\ni0 u\no0 controllable_c\n"
    # A wrong decision becomes observable one tick later, not at initialization.
    delayed_game = "aag 4 2 1 1 1\n2\n4\n6 8\n6\n8 2 5\ni0 u\ni1 controllable_c\n"
    copy_controller = "aag 1 1 0 1 0\n2\n2\ni0 u\no0 controllable_c\n"
    false_controller = "aag 1 1 0 1 0\n2\n0\ni0 u\no0 controllable_c\n"
    cases = [
        ("memory-safe", memory_game, memory_controller, "SAFE", 0),
        ("wrong-reset", memory_game, memory_controller.replace("4 2 1", "4 2 0"), "UNSAFE", 1),
        ("delayed-safe", delayed_game, copy_controller, "SAFE", 0),
        ("delayed-unsafe", delayed_game, false_controller, "UNSAFE", 1),
        ("missing-control", memory_game, "aag 0 0 0 0 0\n", "ERROR", 2),
        ("wrong-port", memory_game, memory_controller.replace("controllable_c", "c"), "ERROR", 2),
        ("controller-sees-control", memory_game, memory_controller.replace("i0 u", "i0 controllable_c"), "ERROR", 2),
        ("uninitialized", memory_game, memory_controller.replace("4 2 1", "4 2 4"), "ERROR", 2),
        ("alias", memory_game.replace("i0 u", "i0 AIGER_NEXT_u"), memory_controller, "ERROR", 2),
        ("typed-game", "aag 1 1 0 0 0 1\n2\n2\ni0 u\n", false_controller, "ERROR", 2),
        ("no-proof", memory_game, memory_controller, "ERROR", 2),
    ]
    with tempfile.TemporaryDirectory(prefix="tlsf-verify-safety-") as tmp:
        root = Path(tmp)
        for name, game, controller, status, code in cases:
            game_path, controller_path = root / "game.aag", root / "controller.aag"
            game_path.write_text(game)
            controller_path.write_text(controller)
            command = [sys.executable, str(verifier), "--game", str(game_path),
                       "--strategy", str(controller_path), "--out", str(root / name),
                       "--aiger-dir", args.aiger_dir, "--combine-aiger", args.combine_aiger,
                       "--abc", args.abc, "--timeout", "10"]
            if name == "no-proof":
                # A successful process exit without a proof must never pass.
                command[command.index("--abc") + 1] = shutil.which("true")
            proc = subprocess.run(command, capture_output=True, text=True, check=False)
            result = json.loads((root / name / "result.json").read_text())
            assert (proc.returncode, result["status"]) == (code, status), (
                name, proc.stdout, proc.stderr, result)
            if status == "ERROR" and name != "no-proof":
                assert not any(step["label"] == "proof" for step in result["steps"]), result
            if status == "SAFE":
                before = (root / name / "result.json").read_bytes()
                repeated = subprocess.run(command, capture_output=True, check=False)
                assert repeated.returncode == 2
                assert (root / name / "result.json").read_bytes() == before
            print(f"{name}: {status}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
