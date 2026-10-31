"""AST visitor and string API outputs, including cluster signal partitions."""
import subprocess
import sys
from golden import Golden

executable, fixture = sys.argv[1:]
gold = Golden("conversion")
result = subprocess.run([executable, fixture], text=True, capture_output=True, timeout=30)
assert result.returncode == 0, result.stderr
gold.check("ast-export", result.stdout)
gold.finish()
