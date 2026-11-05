"""Independent LTL/LTLf semantics on explicit words, using Python integers.

No production parser, normalization, derivatives, automata, or BDD code is
imported. A lasso is a finite graph of positions; temporal operators are their
defining least/greatest fixed points. Finite words are nonempty, with weak X
and strong X[!]. Sampling equivalence is evidence, never a language proof.
"""
import json
import random
import re


TOKEN = re.compile(r'\s*(X\[!\]|X\[\?\]|<->|<=>|->|=>|&&|\|\||[()!~&|^]|'
                   r'"(?:\\.|[^"\\])*"|[A-Za-z_@][A-Za-z0-9_@\x27]*|[01])')
BINARY = {"<->": (2, "e"), "<=>": (2, "e"), "->": (1, "i"), "=>": (1, "i"),
          "^": (3, "^"), "xor": (3, "^"), "|": (4, "|"), "||": (4, "|"),
          "&": (5, "&"), "&&": (5, "&"),
          "U": (6, "U"), "R": (6, "R"), "W": (6, "W"), "M": (6, "M")}


def parse(text):
    tokens, position = [], 0
    while position < len(text.rstrip()):
        match = TOKEN.match(text, position)
        if not match:
            raise ValueError(f"invalid formula at {text[position:]!r}")
        token = match[1]
        # The archived infix corpus also uses compact unary forms (GFb, GXc).
        # Quoted atoms are always literal, including uppercase operator names.
        compact = re.fullmatch(r"([GFX]+)([a-z][A-Za-z0-9_]*)", token)
        tokens.extend(list(token) if re.fullmatch(r"[GFX]+", token) else
                      [*compact[1], compact[2]] if compact else [token])
        position = match.end()
    index = 0

    def expression(minimum=0):
        nonlocal index
        if index == len(tokens):
            raise ValueError("missing operand")
        token = tokens[index]
        index += 1
        if token == "(":
            left = expression()
            if index == len(tokens) or tokens[index] != ")":
                raise ValueError("missing closing parenthesis")
            index += 1
        elif token in ("!", "~", "X", "X[!]", "X[?]", "F", "G"):
            left = ("!" if token == "~" else token, expression(7))
        elif token in ("true", "false", "tt", "ff", "0", "1"):
            left = ("1" if token in ("true", "tt", "1") else "0",)
        elif token.startswith('"'):
            left = ("ap", json.loads(token))
        elif token not in BINARY and token != ")":
            left = ("ap", token)
        else:
            raise ValueError(f"unexpected token {token}")
        while index < len(tokens) and tokens[index] in BINARY:
            precedence, op = BINARY[tokens[index]]
            if precedence < minimum:
                break
            index += 1
            # Binary temporal operators and implication associate right.
            right = expression(precedence + (op in ("&", "|", "^", "e")))
            left = (op, left, right)
        return left

    result = expression()
    if index != len(tokens):
        raise ValueError(f"trailing tokens: {tokens[index:]}")
    return result


def parse_prefix(text):
    tokens = iter(text.split())

    def consume():
        token = next(tokens)
        if token.startswith("$"):
            return ("ap", token[1:])
        if token in ("0", "1"):
            return (token,)
        if token in ("!", "X", "X[!]", "F", "G"):
            return (token, consume())
        if token in ("&", "|", "i", "e", "^", "U", "R", "W", "M"):
            return (token, consume(), consume())
        raise ValueError(token)
    result = consume()
    if next(tokens, None) is not None:
        raise ValueError("trailing prefix tokens")
    return result


def prefix(tree):
    if tree[0] == "ap":
        return "$" + tree[1]
    return " ".join([tree[0], *(prefix(child) for child in tree[1:])])


def atoms(tree):
    if tree[0] == "ap":
        return {tree[1]}
    return set().union(*(atoms(c) for c in tree[1:]))


def evaluate(tree, names, word, loop_start=None):
    """Truth at position zero; loop_start=None denotes a finite word."""
    if not word or len(set(names)) != len(names):
        raise ValueError("nonempty word and distinct AP names required")
    if loop_start is not None and not 0 <= loop_start < len(word):
        raise ValueError("invalid loop entry")
    positions = {name: i for i, name in enumerate(names)}
    if not atoms(tree) <= positions.keys():
        raise ValueError(f"undeclared APs: {atoms(tree) - positions.keys()}")
    if any(mask < 0 or mask >= 1 << len(names) for mask in word):
        raise ValueError("letter outside the declared alphabet")
    size, full = len(word), (1 << len(word)) - 1
    last = 1 << (size - 1)
    memo = {}

    def advance(value, weak=False):
        tail = weak if loop_start is None else bool(value & (1 << loop_start))
        return (value >> 1) | (last if tail else 0)

    def visit(node):
        if node in memo:
            return memo[node]
        op = node[0]
        if op == "ap":
            value = sum(1 << i for i, mask in enumerate(word)
                        if mask & (1 << positions[node[1]]))
        elif op in ("0", "1"):
            value = full if op == "1" else 0
        else:
            a = visit(node[1])
            b = visit(node[2]) if len(node) == 3 else None
            if op == "!":
                value = full ^ a
            elif op in ("X", "X[!]", "X[?]"):
                value = advance(a, op != "X[!]")
            elif op in ("&", "|", "^", "i", "e"):
                value = {"&": a & b, "|": a | b, "^": a ^ b,
                         "i": (full ^ a) | b, "e": full ^ (a ^ b)}[op]
            else:
                greatest = op in ("G", "R", "W")
                value = full if greatest else 0
                while True:
                    nxt = advance(value, greatest)
                    if op == "F":
                        updated = a | nxt
                    elif op == "G":
                        updated = a & nxt
                    elif op in ("U", "W"):
                        updated = b | (a & nxt)
                    elif op in ("R", "M"):
                        updated = b & (a | nxt)
                    else:
                        raise ValueError(op)
                    if value == updated:
                        break
                    value = updated
        memo[node] = value
        return value
    return bool(visit(tree) & 1)


def membership(formula, names, words, finite=False):
    tree = parse(formula) if isinstance(formula, str) else formula
    if finite:
        return "".join("1" if evaluate(tree, names, word) else "0" for word in words)
    return "".join("1" if evaluate(tree, names, p + q, len(p)) else "0"
                   for p, q in words)


def sample_equivalent(left, right, seed=20852, count=128, finite=False):
    a, b = parse(left), parse(right)
    names = sorted(atoms(a) | atoms(b))
    rng = random.Random(seed)
    words = [[rng.randrange(1 << len(names)) for _ in range(rng.randrange(1, 7))]
             for _ in range(count)] if finite else [
                 ([rng.randrange(1 << len(names)) for _ in range(rng.randrange(5))],
                  [rng.randrange(1 << len(names)) for _ in range(rng.randrange(1, 7))])
                 for _ in range(count)]
    assert membership(a, names, words, finite) == membership(b, names, words, finite), (left, right)


def random_formulas(seed=20852, count=128):
    """Seeded construction of safety, recurrence, and their Boolean products."""
    rng = random.Random(seed)

    def window(depth):
        if depth == 0:
            return rng.choice(("a", "b", "c", "!a", "!b", "!c"))
        if rng.randrange(3) == 0:
            return f"X ({window(depth - 1)})"
        return f"({window(depth - 1)} {rng.choice(('&', '|'))} {window(depth - 1)})"
    result = []
    for i in range(count):
        w = window(rng.randrange(1, 4))
        result.append(rng.choice((f"G ({w})", f"F ({w})", f"G F ({w})",
                                  f"F G ({w})", f"G ({w}) & G F a",
                                  f"F ({w}) | F G b")))
    return list(dict.fromkeys(result))
