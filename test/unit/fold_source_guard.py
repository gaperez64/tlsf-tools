"""Keep fixture/corpus family names out of fold implementation literals."""

import ast
from pathlib import Path
import re
import sys


FAMILY = re.compile(
    r"load|balancer|arbiter|request|grant|idle|lift|elevator|amba|prioritized|simple|full",
    re.IGNORECASE,
)

# Exact existing literals only; these describe proof operations, not families.
ALLOW = {
    "full Boolean BDD equality of W/X/Y/goals",  # Whole Boolean state space.
    "Target transition relation and lifted invariant/ranks.",  # Proof transport.
}

TOKENS = re.compile(
    # #include header-name tokens are not C++ string literals.
    r'(?P<header>#[ \t]*include\b[^\n]*)'
    r'|(?P<space>\s+|//[^\n]*|/\*.*?\*/)'
    r'|(?P<raw>(?:u8|u|U|L)?R"(?P<delim>[^ ()\\\t\r\n]{0,16})\('
    r'(?P<body>.*?)\)(?P=delim)")'
    r'|(?P<string>(?:u8|u|U|L)?"(?:\\.|[^"\\])*")'
    r"|(?P<char>(?:u8|u|U|L)?'(?:\\.|[^'\\])*')"
    r'|(?P<other>.)',
    re.DOTALL,
)


def literals(source):
    parts = []
    line = 0
    for token in TOKENS.finditer(source):
        if token.lastgroup in {'header', 'space'}:
            continue
        if token.lastgroup in {'raw', 'string'}:
            if not parts:
                line = source.count('\n', 0, token.start()) + 1
            if token.lastgroup == 'raw':
                parts.append(token.group('body'))
            else:
                quoted = token.group('string')
                parts.append(ast.literal_eval(quoted[quoted.index('"'):]))
        else:
            if parts:
                yield line, ''.join(parts)
                parts.clear()
    if parts:
        yield line, ''.join(parts)


def violations(source):
    return [(line, value) for line, value in literals(source)
            if FAMILY.search(value) and value not in ALLOW]


def self_check():
    assert not violations('// "load"\n/* "grant" */\n#include "gr1_lift.h"\n')
    assert not violations('auto s = "neutral"; char c = \'"\';')
    assert not violations('auto s = "full Boolean BDD equality of W/X/Y/goals";')
    for word in FAMILY.pattern.split('|'):
        assert violations(f'auto s = "{word.upper()}";')
    assert violations('auto s = "lo" /* hidden */ "ad";')
    assert violations(r'auto s = "\x6c\157ad";')
    assert violations('auto s = u8R"tag(request)tag";')
    assert violations('auto s = R"(\n#include "load"\n)";')
    assert violations('#include "gr1_lift.h"\n\nauto s = "idle";') == [(3, 'idle')]
    assert violations('auto s = "full Boolean BDD equality of W/X/Y/goals-extra";')


def main():
    self_check()
    lib = Path(sys.argv[1]) / 'src/lib'
    sources = {lib / 'gr1_lift.cc'}
    # Automatically cover separate fold implementation files if any are added.
    sources.update(p for p in lib.rglob('*fold*')
                   if p.suffix in {'.c', '.cc', '.cpp', '.h', '.hh', '.hpp'})
    failures = []
    for path in sorted(sources):
        failures.extend(f'{path}:{line}: forbidden family literal {value!r}'
                        for line, value in violations(path.read_text()))
    if failures:
        sys.exit('\n'.join(failures))
    print(f'Checked {len(sources)} fold source file(s)')


if __name__ == '__main__':
    main()
