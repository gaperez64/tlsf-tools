"""Compare every public options offset in C/C++ with and without NDEBUG."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile


root, build = map(Path, sys.argv[1:])
compilers = json.loads((build / "meson-info/intro-compilers.json").read_text())["host"]
fields = """node_cap cache_cap gc_mode gc_threshold_percent verbosity trace
safety_objective safety_output_index failure var_order order_file
demand_transitions realizability_only trace_roots trace_gate trace_node_limit
trace_scratch_bytes deadline_mono_ns cancelled cancel_ctx max_artifact_bytes""".split()
source = '''#include "tlsf/oxidd_options.h"
#ifdef __cplusplus
#define ALIGNOF alignof
#else
#define ALIGNOF _Alignof
#endif
int main(void) {
  printf("size=%zu\\n", sizeof(OxiddSolveOptions));
  printf("alignment=%zu\\n", (size_t)ALIGNOF(OxiddSolveOptions));
'''
for field in fields:
    source += (f'  printf("{field}=%zu\\n", '
               f'offsetof(OxiddSolveOptions, {field}));\n')
source += "  return 0;\n}\n"

with tempfile.TemporaryDirectory(prefix="oxidd-layout-", dir=build) as temp:
    directory = Path(temp)
    layouts = {}
    for language, standard, suffix in (("c", "c11", "c"), ("cpp", "c++20", "cpp")):
        probe = directory / ("probe." + suffix)
        probe.write_text(source)
        for mode in ("-UNDEBUG", "-DNDEBUG"):
            binary = directory / "probe"
            subprocess.run([*compilers[language]["exelist"], "-std=" + standard,
                            mode, "-I" + str(root / "include"), str(probe),
                            "-o", str(binary)], check=True)
            layouts[language + mode] = subprocess.check_output([binary])
    if len(set(layouts.values())) != 1:
        raise AssertionError(f"NDEBUG/language-dependent OxiddSolveOptions layout: {layouts}")
    print(next(iter(layouts.values())).decode(), end="")
    print("C/C++ debug/release layouts agree")
