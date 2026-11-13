#!/usr/bin/env python3
"""Positive and negative controls for status, table and selection checkers."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
CLI = ROOT / 'test/cli'


def check(command, success, **kwargs):
    result = subprocess.run(list(map(str, command)), capture_output=True,
                            text=True, timeout=30, **kwargs)
    assert (result.returncode == 0) == success, (command, result)
    return result


def main():
    for expected, message in ((0, 'REALIZABLE'), (1, 'UNREALIZABLE'), (2, 'UNKNOWN')):
        for actual in (0, 1, 2, 3):
            check([CLI / 'check_contains.sh', expected, '^' + message + '$',
                   sys.executable, '-c',
                   f'import sys; print({message!r}); sys.exit({actual})'],
                  actual == expected)
    check([CLI / 'check_contains.sh', 0, 'absent', sys.executable, '-c',
           'print("other")'], False)
    # Invalid/partial selections must fail before attempting to run a tool.
    for selection in (['typo', 'file'], ['match-safe:1'], ['match-safe:1', 'typo']):
        result = check([sys.executable, ROOT / 'test/oracle/test_normalization.py',
                        'missing-norm', 'missing-convert', 'missing-cases',
                        *selection], False)
        assert 'unknown normalization selection' in result.stderr, result

    with tempfile.TemporaryDirectory(prefix='harness-controls-') as temporary:
        temp = Path(temporary)
        stub = temp / 'table stub.py'
        stub.write_text('''#!/usr/bin/env python3
import os
from pathlib import Path
import sys

def table(name, header, row):
    shape = os.environ['SHAPE'] if name == os.environ['TABLE'] else 'valid'
    if shape == 'empty':
        return ''
    if shape == 'header':
        return header + '\\n'
    if shape == 'bad':
        row = 'bad'
    return header + '\\n' + row + '\\n' + (row + '\\n' if shape == 'extra' else '')

if '--output' in sys.argv:
    output = Path(sys.argv[sys.argv.index('--output') + 1])
    output.mkdir()
    (output / 'automata.tsv').write_text(table('automata',
        'schema_version\\tgeneration_status\\tstates', '2\\tok\\t1'))
    (output / 'source-features.tsv').write_text(table('source',
        'schema_version\\tguard_nodes\\tspec_id', '2\\t1\\tfixture'))
elif '--schema-version' in sys.argv:
    print(2)
elif '--split' in sys.argv:
    sys.exit(1)
elif '--source-features' in sys.argv:
    print(table('source', 'file\\tschema_version\\tstatus\\tguard_nodes\\tinputs\\toutputs',
                'fixture\\t2\\tok\\t1\\t1\\t1'), end='')
else:
    print(table('bench', 'file\\tschema_version\\tstatus\\tguard_nodes\\tformula_size_raw\\tguard_temporal_ops\\tguard_max_depth\\tguard_max_temporal_depth',
                'fixture\\t2\\tok\\t1\\t1\\t1\\t1\\t1'), end='')
''')
        stub.chmod(0o755)
        for harness, tables, arguments in (
            ('check_automata_study.sh', ('automata', 'source'), [stub] + ['unused'] * 6),
            ('check_benchgraph_schema.sh', ('bench', 'source'), [stub, 'unused']),
        ):
            for table in tables:
                for shape in ('valid', 'empty', 'header', 'extra', 'bad'):
                    check([CLI / harness, *arguments], shape == 'valid',
                          env=dict(os.environ, TABLE=table, SHAPE=shape))

        info = temp / 'meson-info'
        info.mkdir()
        headers = [path.name for path in (ROOT / 'include/tlsf').iterdir()
                   if path.suffix in ('.h', '.hpp')] + ['version.h']
        plan = {'headers': {name: {'destination': '{includedir}/tlsf/' + name}
                            for name in headers}, 'targets': {}}
        (info / 'intro-install_plan.json').write_text(json.dumps(plan))
        for modes, success in ((['replay'], True), (['replay', 'fuzzer'], True),
                               (['replay', 'unrelated'], False)):
            targets = [{'name': 'fuzz-dpa-checks-' + mode,
                        'defined_in': str(ROOT / 'test/fuzz/meson.build'),
                        'target_sources': [{'sources': [str(ROOT / 'test/fuzz/dpa_checks.c')]}]}
                       for mode in modes]
            (info / 'intro-targets.json').write_text(json.dumps(targets))
            check([sys.executable, ROOT / 'test/api/check_layout.py', ROOT, temp], success)
    print('status, table, selection and fuzz layout controls passed')


if __name__ == '__main__':
    main()
