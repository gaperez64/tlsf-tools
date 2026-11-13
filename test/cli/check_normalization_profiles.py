#!/usr/bin/env python3
"""Distinguish the composed Sickert profile from either stage in isolation."""
import subprocess
import sys

norm, convert = sys.argv[1:]
source = '''INFO { SEMANTICS: Mealy TARGET: Mealy }
MAIN { INPUTS { a; req; c; } OUTPUTS { p; b; }
GUARANTEES { G(req -> (a U (G F p))); G F(c -> (a W b)); } }
'''


def objective(schedule):
    normalized = subprocess.check_output(
        [norm, '--passes', schedule], input=source, text=True, timeout=30)
    return subprocess.check_output([convert], input=normalized, text=True, timeout=30)


bounded = objective('sickert-bounded')
assert bounded == objective('sickert-stage2:1,weak,sickert-stage3:1,weak')
assert bounded != objective('sickert-stage2:1,weak')
assert bounded != objective('sickert-stage3:1,weak')
