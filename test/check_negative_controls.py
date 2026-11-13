#!/usr/bin/env python3
"""Recompile each repaired checker with one wrong expectation; require failure.

Only test objects are mutated, under the configured build directory. Production
objects, compiler flags (including NDEBUG), and link inputs are retained.
"""
import argparse
import json
from pathlib import Path
import shlex
import subprocess


def run(command, build):
    return subprocess.run(command, cwd=build, text=True, capture_output=True,
                          timeout=120)


def replace_arg(command, option, value):
    command[command.index(option) + 1] = str(value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('build', type=Path)
    parser.add_argument('--research', action='store_true')
    args = parser.parse_args()
    build = args.build.resolve()
    root = Path(__file__).resolve().parents[1]
    scratch = build / 'assertion-negative-controls'
    scratch.mkdir(exist_ok=True)
    commands = json.loads((build / 'compile_commands.json').read_text())
    cases = [
        ('api/ast_visitor.c', 'CHECK(callbacks == decoded(visited));',
         'CHECK(callbacks != decoded(visited));', []),
        ('api/decompose_cpp.cpp',
         'CHECK(conversion.verdict == tlsf::Verdict::Unknown);',
         'CHECK(conversion.verdict != tlsf::Verdict::Unknown);', []),
        ('api/visitor_cpp.cpp', 'CHECK(ast.root());', 'CHECK(!ast.root());', []),
        ('api/convert.cpp', 'CHECK(result.preprocessed_ltl == "G (X a -> b)");',
         'CHECK(result.preprocessed_ltl != "G (X a -> b)");', []),
        ('api/native_lift_c.c', '== TLSF_GR1_LIFT_CANCELLED);',
         '!= TLSF_GR1_LIFT_CANCELLED);', []),
        ('api/native_reduction_c.c', 'TLSF_GR1_REDUCE_OK);',
         'TLSF_GR1_REDUCE_ERROR);', []),
        ('unit/native_contract_api.cpp', 'CHECK(failed);', 'CHECK(!failed);', []),
        ('unit/native_env_contract_api.cpp', 'CHECK(failed);', 'CHECK(!failed);', []),
    ]
    if args.research:
        cases.append(('unit/pruning_cache.c', 'CHECK(calls == 1);',
                      'CHECK(calls != 1);', []))
    runtime_source = root / 'test' / 'unit' / 'oxidd_runtime.c'
    runtime_commands = [row for row in commands
                        if (build / row['file']).resolve() == runtime_source]
    address_sanitized = any(
        arg.startswith('-fsanitize=') and 'address' in arg.split('=', 1)[1].split(',')
        for row in runtime_commands for arg in shlex.split(row['command']))
    if runtime_commands and not address_sanitized:
        # Make the actual setup syscall fail, rather than just invert a result.
        cases.append(('unit/oxidd_runtime.c', 'setrlimit(RLIMIT_AS, &limit)',
                      'setrlimit(-1, &limit)', ['0']))
    for name, old, new, runtime_args in cases:
        source = root / 'test' / name
        entries = [row for row in commands
                   if (build / row['file']).resolve() == source]
        assert len(entries) == 1, (name, entries)
        row = entries[0]
        command = shlex.split(row['command'])
        original_object = command[command.index('-o') + 1]
        target = 'test/' + str(Path(name).with_suffix(''))
        link = run(['ninja', '-t', 'commands', target], build)
        assert link.returncode == 0, link.stderr
        link_command = shlex.split(link.stdout.splitlines()[-1])
        assert original_object in link_command, (name, link_command)
        text = source.read_text()
        assert old in text, (name, old)
        mutated_source = scratch / source.name
        mutated_source.write_text(text.replace(old, new, 1))
        mutated_object = scratch / (source.stem + '.o')
        # Preserve the original executable's relative dependency search paths.
        binary = build / Path(target).parent / ('negative-control-' + source.stem)
        command[command.index(row['file'])] = str(mutated_source)
        replace_arg(command, '-o', mutated_object)
        for option in ('-MT', '-MQ'):
            if option in command:
                replace_arg(command, option, mutated_object)
        if '-MF' in command:
            replace_arg(command, '-MF', mutated_object.with_suffix('.d'))
        command += ['-iquote', str(source.parent)]
        compiled = run(command, build)
        assert compiled.returncode == 0, (name, compiled.stderr)
        link_command[link_command.index(original_object)] = str(mutated_object)
        replace_arg(link_command, '-o', binary)
        linked = run(link_command, build)
        assert linked.returncode == 0, (name, linked.stderr)
        result = run([str(binary), *runtime_args], build)
        predicate = new.removeprefix('CHECK(').removesuffix(');')
        diagnostic = ' '.join(result.stderr.split())
        assert (result.returncode == 1 and 'check failed:' in diagnostic
                and predicate in diagnostic), (
            name, result.returncode, result.stdout, result.stderr)
        if name.endswith('oxidd_runtime.c'):
            assert 'setrlimit(-1, &limit) == 0' in result.stderr, result.stderr
        print(f'{name}: wrong expectation rejected', flush=True)


if __name__ == '__main__':
    main()
