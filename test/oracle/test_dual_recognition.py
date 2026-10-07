#!/usr/bin/env python3
"""Exact explicit small games plus independent lasso-language checks of the dual."""

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import spot

from test_native_reduction_language import Game


def parity_winner(table, kind, moore):
    """Source oracle: hand-built parity monitor, independent of the reducer/Spot."""
    owners, priorities, edges, vertices = {}, {}, {}, {}
    pending = deque()

    def intern(key, owner, priority):
        if key not in vertices:
            vertex = len(vertices)
            vertices[key] = vertex
            owners[vertex], priorities[vertex], edges[vertex] = owner, priority, []
            pending.append(key)
        return vertices[key]

    def priority(state):
        return 0 if state is None else int(state) if kind == 'G' else int(not state)

    initial_state = None if kind == 'init' else False if kind == 'G' else True
    initial = intern(('state', initial_state), 0 if moore else 1, 0)
    while pending:
        key = pending.popleft()
        src = vertices[key]
        if key[0] == 'state':
            state = key[1]
            priorities[src] = priority(state)
            for first in (False, True):
                edges[src].append(intern(('choice', state, first), 1 if moore else 0,
                                         priority(state)))
        else:
            _, state, first = key
            for second in (False, True):
                i, o = (second, first) if moore else (first, second)
                value = bool(table & (1 << (2 * int(i) + int(o))))
                nxt = ((value if state is None else state) if kind == 'init'
                       else (state or not value) if kind == 'G' else value)
                edges[src].append(intern(('state', nxt), 0 if moore else 1, priority(nxt)))

    def attract(player, target, arena):
        result = set(target)
        while True:
            old = set(result)
            for vertex in arena - result:
                successors = set(edges[vertex]) & arena
                if (owners[vertex] == player and successors & result
                        or owners[vertex] != player and successors <= result):
                    result.add(vertex)
            if result == old:
                return result

    def zielonka(arena):
        if not arena:
            return set(), set()
        largest = max(priorities[v] for v in arena)
        player = largest % 2
        attr = attract(player, {v for v in arena if priorities[v] == largest}, arena)
        winners = list(zielonka(arena - attr))
        if not winners[1 - player]:
            winners[player] |= attr
            return tuple(winners)
        other = attract(1 - player, winners[1 - player], arena)
        winners = list(zielonka(arena - other))
        winners[1 - player] |= other
        return tuple(winners)

    return initial in zielonka(set(edges))[0]


def reduced_winner(game):
    """Reachable explicit generalized-Buechi game, with forall input exists output."""
    assert not game.fairness
    nu = sum(not n.startswith('controllable_') for n in game.input_names)
    nc = len(game.inputs) - nu
    initial = game.initial()
    states, pending, moves, goals = {initial}, deque([initial]), {}, {}
    while pending:
        state = pending.popleft()
        choices = []
        for u in range(1 << nu):
            responses = []
            for c in range(1 << nc):
                nxt, bad, justice, fairness = game.step(state, u | (c << nu))
                assert not bad and not fairness
                if state in goals:
                    assert goals[state] == justice  # State-based monitor acceptance.
                goals[state] = justice
                responses.append(nxt)
                if nxt not in states:
                    states.add(nxt)
                    pending.append(nxt)
            choices.append(responses)
        moves[state] = choices
        assert len(states) < 4096

    def pre(target):
        return {s for s in states if all(any(n in target for n in responses)
                                        for responses in moves[s])}

    z = set(states)
    while True:
        old_z = set(z)
        for j in range(len(goals[initial])):
            y = set()
            base = {s for s in pre(z) if goals[s][j]}
            while True:
                new = base | pre(y)
                if new == y:
                    break
                y = new
            z &= y
        if z == old_z:
            return initial in z


def tlsf(body, semantics='Mealy', target=None, sections=''):
    return f'''INFO {{ TITLE: "dual test" DESCRIPTION: "generated"
      SEMANTICS: {semantics} TARGET: {target or semantics} }}
    MAIN {{ INPUTS {{ i; }} OUTPUTS {{ o; }} {sections}
      GUARANTEE {{ {body}; }} }}'''.replace('GF', 'G F').replace('FG', 'F G')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('probe', type=Path)
    parser.add_argument('build', type=Path)
    args = parser.parse_args()
    probe = args.probe.resolve()
    root = args.build / 'dual-recognition-tests'
    root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=root) as scratch:
        directory = Path(scratch)
        counter = 0

        def run(source, strict=False, mode=None):
            nonlocal counter
            prefix = directory / str(counter)
            counter += 1
            spec = prefix.with_suffix('.tlsf')
            spec.write_text(source)
            result = subprocess.run([str(probe), str(spec), str(prefix)] +
                                    ([mode] if mode else ['strict'] if strict else []), check=True,
                                    capture_output=True, text=True, timeout=20)
            status = json.loads(result.stdout)
            construction_file = Path(str(prefix) + '.construction.json')
            if not construction_file.exists():
                return status, None, None
            construction = json.loads(construction_file.read_text())
            assert construction['source_sha256'] == hashlib.sha256(source.encode()).hexdigest()
            if status['status']:
                assert not Path(str(prefix) + '.aag').exists()
                return status, construction, None
            game_file = Path(str(prefix) + '.aag')
            metadata = json.loads(Path(str(prefix) + '.metadata.json').read_text())
            provenance = json.loads(Path(str(prefix) + '.provenance.json').read_text())
            assert metadata['semantics'] == 'exact' and metadata['recognition_only']
            assert metadata['game_sha256'] == hashlib.sha256(game_file.read_bytes()).hexdigest()
            assert metadata['construction_sha256'] == hashlib.sha256(
                construction_file.read_bytes()).hexdigest()
            assert provenance['construction'] == construction
            assert all(m['owner'] == 'deterministic' and m['side'] == 'guarantee'
                       and m['role'] == 'justice' and
                       m['source_origin'] == 'negated-objective'
                       for m in provenance['monitors'])
            return status, construction, Game(game_file.read_text())

        # Every Boolean function of the current round, under both original
        # move orders and both TLSF targets. This includes equality and its
        # rename/inversion controls; no expected answers enter solver code.
        checks = 0
        for table in range(16):
            terms = []
            for i in range(2):
                for o in range(2):
                    if table & (1 << (2 * i + o)):
                        terms.append(f"({'i' if i else '!i'} && {'o' if o else '!o'})")
            predicate = ' || '.join(terms) or 'false'
            for kind in ('init', 'G', 'FG'):
                for semantics in ('Mealy', 'Moore'):
                    for target in ('Mealy', 'Moore'):
                        status, construction, game = run(tlsf(f'{"" if kind == "init" else kind} ({predicate})',
                                                            semantics, target))
                        assert status['status'] == 0, status
                        assert status['constructed'] == 1
                        assert construction['target_adaptation_count'] == int(semantics != target)
                        assert construction['dual_input_push_count'] == int(target == 'Mealy')
                        assert construction['dual_timing'] == ('Moore' if target == 'Mealy'
                                                               else 'Mealy')
                        expected = not parity_winner(table, kind, semantics == 'Moore')
                        assert reduced_winner(game) == expected, (table, kind, semantics, target)
                        checks += 1

        # Equality sentinel: a dual allowed to see the current o wins by
        # choosing i != o, but that policy cannot satisfy the correct timing.
        eq = 0b1001
        assert parity_winner(eq, 'G', False)
        _, binding, correct = run(tlsf('G(o <-> i)'))
        assert not reduced_winner(correct)
        _, _, illegal = run(tlsf('G(o <-> i)', 'Moore'))
        assert reduced_winner(illegal)
        assert binding['dual_initial_quantifiers'] == 'exists original input forall original output'

        # Complement is not automatically a DBA/GR(1) objective.
        status, construction, game = run(tlsf('GF o'))
        assert status['stage'] == 'mp-class' and status['status'] == status['cause'] == 1
        assert construction and not game
        for source, strict in [(tlsf('FG o'), True),
                               (tlsf('FG o', 'Strict,Mealy', 'Mealy'), False)]:
            status, construction, game = run(source, strict)
            assert status['stage'] == 'dual-strict' and status['status'] == 1
            assert construction is None and game is None

        for mode, code, stage, constructed in (
                ('structure', 3, 'budget-structure', True),
                ('monitor', 3, None, True),
                ('deadline', 4, 'reduce', False),
                ('cancel', 5, 'reduce', False),
                ('snapshot', 6, 'source', False)):
            status, construction, game = run(tlsf('FG(o <-> i)'), mode=mode)
            assert status['status'] == status['cause'] == code, (mode, status)
            if stage:
                assert status['stage'] == stage, (mode, status)
            assert bool(construction) == constructed and game is None

        for semantics in ('Mealy', 'Moore'):
            _, _, renamed = run(tlsf('FG (o <-> i)', semantics)
                                .replace(' i;', ' sensor; extra_sensor;')
                                .replace(' o;', ' decision; extra_decision;')
                                .replace('(o <-> i)', '(decision <-> sensor)'))
            assert reduced_winner(renamed) == (semantics == 'Moore')

        # Full-objective lasso checks exercise initial, safety and assumption
        # handling independently of winning-set computations.
        for sections, body, expected_formula in [('', 'FG o', 'FG o'),
                               ('INITIALLY { i; } PRESET { o; }', 'FG (o <-> i)', 'i -> (o & FG(o <-> i))'),
                               ('REQUIRE { i; } ASSERT { o; }', 'FG o', '(G i) -> (G o & FG o)'),
                               ('ASSUME { GF i; }', 'FG o', '(GF i) -> (FG o)'),
                               ('ASSUME { false; }', 'FG o', '1'),
                               ('INITIALLY { i; } ASSERT { o; }', 'false', '!i')]:
            status, construction, game = run(tlsf(body, sections=sections))
            if status['status']:
                assert status['stage'] == 'mp-class', status
                continue
            if 'false' in sections:
                assert not reduced_winner(game)
            names = {row['name']: k for k, row in enumerate(construction['ownership'])}
            compiled = spot.formula(construction['compiled_objective'])
            original = spot.formula(construction['original_objective'])
            assert spot.are_equivalent(original, spot.formula(expected_formula))
            for first in range(4):
                for loop in range(4):
                    def letter(value):
                        return ' & '.join((name if value & (1 << bit) else '!' + name)
                                          for name, bit in names.items())
                    word = spot.parse_word(f'{letter(first)}; cycle{{{letter(loop)}}}')
                    actual = game.accepts([first], [loop])
                    assert actual == spot.translate(compiled).intersects(word.as_automaton())
                    # Undo the scheduling on the word, not on the objective.
                    # The first old output is the second compiled input;
                    # the first old input is the first compiled output.
                    shifted = (first & (1 << names['i'])) | (loop & (1 << names['o']))
                    original_word = spot.parse_word(
                        f'{letter(shifted)}; cycle{{{letter(loop)}}}')
                    assert actual != spot.translate(original).intersects(original_word.as_automaton())
        print(f'dual recognition: {checks} explicit games, sentinel, provenance, strict and lasso checks passed')


if __name__ == '__main__':
    main()
