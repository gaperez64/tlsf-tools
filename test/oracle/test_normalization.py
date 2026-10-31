#!/usr/bin/env python3
"""Pin normalized TLSF and independently confirmed equivalent objectives."""
from pathlib import Path
import subprocess
import sys

from golden import Golden

norm, convert, cases, *selection = sys.argv[1:]
schedules = [("match-safe:1", "normalization_patterns.tlsf"),
             ("route-safe:1", "normalization_route.tlsf"),
             ("sickert-stage2:2", "normalization_sickert2.tlsf"),
             ("sickert-stage3:1", "normalization_sickert3.tlsf"),
             ("sickert-bounded", "normalization_sickert3.tlsf")]
for schedule, name in schedules:
    if selection and selection != [schedule, name]:
        continue
    gold = Golden("norm-" + schedule.replace(":", "-"))
    source = Path(cases) / name
    normalized = subprocess.check_output([norm, "--passes", schedule, str(source)], text=True, timeout=30)
    gold.check("tlsf", normalized)
    original = subprocess.check_output([convert, str(source)], text=True, timeout=30).strip()
    transformed = subprocess.check_output([convert], input=normalized, text=True, timeout=30).strip()
    gold.check("original", original)
    gold.check("normalized", transformed)
    gold.finish()
