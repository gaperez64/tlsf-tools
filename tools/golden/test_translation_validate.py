#!/usr/bin/env python3
"""Offline regressions for the shared C/Lean wall-clock budget and verdicts."""
import subprocess
import sys
import tempfile
from pathlib import Path
from time import monotonic
import unittest
from unittest.mock import patch

import translation_validate as tv


class BudgetTests(unittest.TestCase):
    def setUp(self):
        tv.SCRATCH.parent.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=tv.SCRATCH.parent)
        self.addCleanup(self.temp.cleanup)
        self.scratch = Path(self.temp.name)
        self.scope = patch.object(tv, "SCRATCH", self.scratch)
        self.scope.start()
        self.addCleanup(self.scope.stop)

    def simulate(self, phases):
        clock, budgets = [100.0], []

        def run(command, timeout):
            duration, code, stdout, stderr = phases[len(budgets)]
            budgets.append(timeout)
            clock[0] += min(duration, timeout)
            if duration > timeout:
                raise subprocess.TimeoutExpired(command, timeout)
            return subprocess.CompletedProcess(command, code, stdout, stderr)

        with patch.object(tv, "monotonic", side_effect=lambda: clock[0]), \
                patch.object(tv, "run", side_effect=run):
            verdict = tv.validate_one(self.scratch, self.scratch / "lean", "request", 17)
        return verdict, budgets

    def test_shared_budget_timeout(self):
        verdict, budgets = self.simulate([(10, 0, "dump", ""), (8, 0, "pass\n", "")])
        self.assertEqual(budgets, [17, 7])
        self.assertEqual(verdict[0], "timeout")
        self.assertIsNone(verdict[2])

    def test_finished_check_passes(self):
        verdict, budgets = self.simulate([(10, 0, "dump", ""), (6, 0, "pass\n", "")])
        self.assertEqual(budgets, [17, 7])
        self.assertEqual(verdict, ("pass", "", tv.sha(b"dump")))

    def test_c_timeout_never_starts_lean(self):
        verdict, budgets = self.simulate([(18, 0, "dump", "")])
        self.assertEqual(budgets, [17])
        self.assertEqual(verdict[0], "timeout")

    def test_decline_has_no_validated_hash(self):
        verdict, budgets = self.simulate([(1, 77, "declined", "")])
        self.assertEqual(verdict, ("not_admitted", "unsupported", None))
        self.assertEqual(budgets, [17])

    def test_reference_rejection_and_invalid_verdict_fail(self):
        for code, stdout, stderr in [(1, "", "reference rejected"), (0, "garbage", "")]:
            with self.subTest(code=code, stdout=stdout):
                verdict, _ = self.simulate([(1, 0, "dump", ""), (1, code, stdout, stderr)])
                self.assertEqual(verdict[0], "fail")

    def test_c_error_fails(self):
        verdict, _ = self.simulate([(1, 2, "", "parse/AP error")])
        self.assertEqual(verdict[0], "fail")

    def test_real_processes_share_deadline(self):
        dumper = self.scratch / "test/unit/dpa_dump"
        dumper.parent.mkdir(parents=True)
        validator = self.scratch / "lean"
        for program, output in [(dumper, "dump"), (validator, "pass")]:
            program.write_text(f"#!{sys.executable}\nimport time\ntime.sleep(0.2)\nprint({output!r})\n")
            program.chmod(0o755)
        started = monotonic()
        verdict = tv.validate_one(self.scratch, validator, "request", 0.3)
        self.assertEqual(verdict[0], "timeout")
        self.assertLess(monotonic() - started, 0.8)


if __name__ == "__main__":
    unittest.main()
