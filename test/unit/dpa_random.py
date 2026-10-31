"""Replay the committed fixed-seed fragment corpus."""
import subprocess
import sys

executable, corpus, mode = sys.argv[1:]
assert mode in ("default", "research")
subprocess.run([executable, corpus] + (["--allow-unproved"] if mode == "research" else []),
               check=True, timeout=110)
