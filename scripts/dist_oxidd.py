#!/usr/bin/env python3
"""Include the nested OxiDD sources and their identity in Meson source exports."""
import os
import pathlib
import shutil

import oxidd_stamp
from oxidd_sources import sources

root = pathlib.Path(__file__).resolve().parents[1]
dest = pathlib.Path(os.environ["MESON_PROJECT_DIST_ROOT"])
source = root / "external/oxidd"
commit, dirty = oxidd_stamp.revision(source)
for path in sources(source):
    target = dest / "external/oxidd" / path.relative_to(source)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, target)
(dest / "oxidd-source-revision").write_text(f"{commit}\n{dirty}\n")
