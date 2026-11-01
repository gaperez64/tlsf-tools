#!/usr/bin/env python3
"""Native reduction artifacts pinned before the monitor rewrite, both semantics."""
import argparse
import json
from pathlib import Path
import pathlib
import subprocess
import tempfile

from golden import Golden
from reduction_golden import native_artifacts, decline


def generated(directory: pathlib.Path) -> list[pathlib.Path]:
    names = ["i", "@", "a'", "controllable_x", "uncontrollable_x",
             "monitor_0_state_0", "assumption_safety_violated", "req@i"]
    outputs = ["o", "z'", "controllable_o", "uncontrollable_y",
               "curr_0", "val'", "@", "monitor_1_state_2"]
    guarantees = ["G ({i} -> {o});", "G !{i};", "G {o};",
                  "G ({i} -> X {o});", "G F {o};",
                  "G !{i}; G {o};", "G ({i} -> F {o});"]
    result = []
    for index, (input_name, output_name) in enumerate(zip(names, outputs)):
        if input_name == output_name:
            continue
        source = directory / f"generated-{index}.tlsf"
        source.write_text(f'''INFO {{
  TITLE: "native differential"
  DESCRIPTION: "generated"
  SEMANTICS: Mealy
  TARGET: Mealy
}}
MAIN {{
  INPUTS {{ {input_name}; }}
  OUTPUTS {{ {output_name}; }}
  ASSUMPTIONS {{ G F {input_name}; }}
  GUARANTEES {{ {guarantees[index % len(guarantees)].format(i=input_name, o=output_name)} }}
}}
''')
        result.append(source)
    crossed = [
        ("controllable_o0", "uncontrollable_i0"),
        ("controllable_o1", "uncontrollable_i1"),
        ("uncontrollable_i0", "controllable_o0"),
        ("controllable_o0_extra", "uncontrollable_i0_extra"),
        ("controllable_o0x", "uncontrollable_i0x"),
        ("controllable_o0_1", "uncontrollable_i0_1"),
    ]
    for index, (input_name, output_name) in enumerate(crossed):
        source = directory / f"generated-crossed-{index}.tlsf"
        source.write_text(f'''INFO {{
  TITLE: "native differential crossed names"
  DESCRIPTION: "generated"
  SEMANTICS: Mealy
  TARGET: Mealy
}}
MAIN {{
  INPUTS {{ {input_name}; }}
  OUTPUTS {{ {output_name}; }}
  ASSUMPTIONS {{ G F {input_name}; }}
  GUARANTEES {{ G F {output_name}; }}
}}
''')
        result.append(source)
    for label, semantics, assumptions, guarantees in (
            ("moore", "Moore", "true;", "G o;"),
            ("unsupported-mp", "Mealy", "true;", "F G o;"),
            ("safety-release", "Mealy", "G i;", "G o;"),
            ("safety-bad", "Mealy", "true;", "G !o;"),
            ("fallback", "Mealy", "true;",
             "G (F o || ((!i || X i) && (i || X !i)));"),
            ("duplicate-origin", "Mealy", "true;", "G o; G (o && true);")):
        source = directory / f"generated-{label}.tlsf"
        source.write_text(f'''INFO {{
  TITLE: "native differential"
  DESCRIPTION: "generated"
  SEMANTICS: {semantics}
  TARGET: {semantics}
}}
MAIN {{
  INPUTS {{ i; }}
  OUTPUTS {{ o; }}
  ASSUMPTIONS {{ {assumptions} }}
  GUARANTEES {{ {guarantees} }}
}}
''')
        result.append(source)
    return result



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--builddir", type=Path, required=True)
    args = parser.parse_args()
    build = args.builddir.resolve()
    fixtures = Path(__file__).resolve().parents[1] / "fixtures/cases"
    gold = Golden("native-reduction")
    count = 0
    with tempfile.TemporaryDirectory(dir=build) as temp:
        directory = Path(temp)
        sources = sorted(fixtures.glob("*.tlsf")) + generated(directory)
        for source in sources:
            for semantics in ("exact", "strict"):
                label = source.name + ":" + semantics
                if not gold.enabled(label):
                    continue
                prefix = directory / "result"
                command = [str(build / "test/api/native_reduction"), str(source),
                           semantics, str(prefix)]
                try:
                    result = subprocess.run(command, text=True, capture_output=True, timeout=60)
                except subprocess.TimeoutExpired:
                    gold.timeout(label)
                    continue
                assert result.returncode in (0, 2, 3), (source, semantics, result.stderr)
                gold.check("status", [source.name, semantics, result.returncode])
                if result.returncode == 0:
                    try:
                        native_artifacts(gold, prefix)
                    except AssertionError as error:
                        raise AssertionError(label) from error
                else:
                    decline(gold, result.stderr)
                count += 1
                if count % 20 == 0:
                    print(f"native reduction {count}: {source.name}", flush=True)
    gold.finish()
    print(f"native reduction goldens: {count} exact/strict cases")


if __name__ == "__main__":
    main()
