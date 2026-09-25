#!/usr/bin/env python3
"""Unit checks for replay classification and the zero-loss summary."""

from __future__ import annotations

import importlib.util
import pathlib
import sys


path = pathlib.Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("evaluate_automata_study", path)
assert spec is not None and spec.loader is not None
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)

assert study.classify(0, True, False, "REALIZABLE") == "TIMEOUT"
assert study.classify(137, False, True, "") == "RESOURCE_LIMIT"
assert study.classify(0, False, False, "REALIZABLE\n") == "REALIZABLE"
assert study.classify(1, False, False, "UNREALIZABLE\n") == "UNREALIZABLE"
assert study.classify(2, False, False, "UNKNOWN\n") == "UNKNOWN"
assert study.classify(1, False, False, "REALIZABLE\n") == "ERROR"


def row(schedule: str, orientation: str, verdict: str) -> dict[str, str]:
    return {
        "spec_id": "case",
        "schedule": schedule,
        "orientation": orientation,
        "repetition": "1",
        "verdict": verdict,
        "seconds": "1.0",
    }


assert study.is_win(row("off", "real", "REALIZABLE"))
assert study.is_win(row("off", "unreal-formula", "UNREALIZABLE"))
assert study.is_win(row("off", "direct", "WINNING"))

summary = study.summary_rows(
    [
        row("off", "real", "REALIZABLE"),
        row("alternate", "real", "RESOURCE_LIMIT"),
    ],
    "off",
)
alternate = next(item for item in summary if item["schedule"] == "alternate")
assert alternate["resource_limits"] == 1
assert alternate["baseline_losses"] == 1
assert alternate["zero_loss_gate"] == "false"
