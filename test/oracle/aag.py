"""Small explicit AAG interpreter and universal closed-loop GR(1) check."""

from collections import deque


class Circuit:
    def __init__(self, text):
        lines = iter(text.splitlines())
        fields = list(map(int, next(lines).split()[1:]))
        fields += [0] * (9 - len(fields))
        self.maximum, ni, nl, no, na, nb, nc, nj, nf = fields
        assert nb == nc == 0
        self.inputs = [int(next(lines)) for _ in range(ni)]
        self.latches = []
        for _ in range(nl):
            latch = list(map(int, next(lines).split()))
            if len(latch) == 2:
                latch.append(0)
            assert latch[2] in (0, 1)
            self.latches.append(latch)
        self.outputs = [int(next(lines)) for _ in range(no)]
        sizes = [int(next(lines)) for _ in range(nj)]
        self.justice = [[int(next(lines)) for _ in range(n)] for n in sizes]
        self.fairness = [int(next(lines)) for _ in range(nf)]
        self.gates = [tuple(map(int, next(lines).split())) for _ in range(na)]
        self.names = {"i": [None] * ni, "o": [None] * no, "l": [None] * nl}
        for line in lines:
            if line == "c":
                break
            if line[:1] in self.names and " " in line:
                label, name = line.split(maxsplit=1)
                self.names[label[0]][int(label[1:])] = name

    def initial(self):
        return sum(1 << i for i, latch in enumerate(self.latches) if latch[2])

    def step(self, state, letter):
        values = [False] * (self.maximum + 1)
        for i, literal in enumerate(self.inputs):
            values[literal // 2] = bool(letter & (1 << i))
        for i, (current, _next, _reset) in enumerate(self.latches):
            values[current // 2] = bool(state & (1 << i))

        def lit(number):
            return values[number // 2] != bool(number & 1)

        for lhs, left, right in self.gates:
            values[lhs // 2] = lit(left) and lit(right)
        successor = sum(1 << i for i, (_, nxt, _) in enumerate(self.latches) if lit(nxt))
        return (successor, [lit(x) for x in self.outputs],
                [all(lit(x) for x in group) for group in self.justice],
                [lit(x) for x in self.fairness])


def components(vertices, edges):
    """Iterative Kosaraju, including singleton components."""
    adjacency = {v: [] for v in vertices}
    reverse = {v: [] for v in vertices}
    for source, target, *_ in edges:
        adjacency[source].append(target)
        reverse[target].append(source)
    seen, order = set(), []
    for vertex in vertices:
        stack = [(vertex, False)]
        while stack:
            current, done = stack.pop()
            if done:
                order.append(current)
            elif current not in seen:
                seen.add(current)
                stack.append((current, True))
                stack.extend((nxt, False) for nxt in adjacency[current] if nxt not in seen)
    seen.clear()
    for vertex in reversed(order):
        if vertex in seen:
            continue
        component, stack = set(), [vertex]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            component.add(current)
            stack.extend(reverse[current])
        yield component


def verify_controller(game, controller, provenance, state_cap=10000):
    inputs = [row["name"] for row in provenance["inputs"]]
    outputs = [row["name"] for row in provenance["outputs"]]
    actual_inputs = controller.names["i"]
    actual_outputs = [name.removeprefix("controllable_")
                      if name not in outputs else name for name in controller.names["o"]]
    if (len(set(actual_inputs)) != len(actual_inputs) or
            len(set(actual_outputs)) != len(actual_outputs) or
            set(actual_inputs) != set(inputs) or set(actual_outputs) != set(outputs)):
        return "INVALID"
    initial = (game.initial(), controller.initial())
    seen, pending, edges = {initial}, deque([initial]), []
    while pending:
        gs, cs = source = pending.popleft()
        for letter in range(1 << len(inputs)):
            ctrl_letter = sum(1 << i for i, name in enumerate(actual_inputs)
                              if letter & (1 << inputs.index(name)))
            nxt_ctrl, emitted, _, _ = controller.step(cs, ctrl_letter)
            values = {name: bool(letter & (1 << i)) for i, name in enumerate(inputs)}
            values.update(zip(actual_outputs, emitted))
            game_letter = sum(1 << i for i, row in enumerate(provenance["inputs"] + provenance["outputs"])
                              if values[row["name"]])
            nxt_game, bad, justice, fairness = game.step(gs, game_letter)
            if any(bad):
                return "REFUTED"
            target = (nxt_game, nxt_ctrl)
            edges.append((source, target, justice, fairness))
            if target not in seen:
                seen.add(target)
                if len(seen) > state_cap:
                    return "UNKNOWN"
                pending.append(target)
    # A rejecting infinite run eventually avoids some guarantee justice,
    # while visiting every environment fairness infinitely often.
    for justice in range(len(game.justice)):
        restricted = [e for e in edges if not e[2][justice]]
        groups = list(components(seen, restricted))
        owner = {vertex: index for index, group in enumerate(groups) for vertex in group}
        internal_edges = [[] for _ in groups]
        for edge in restricted:
            index = owner[edge[0]]
            if index == owner[edge[1]]:
                internal_edges[index].append(edge)
        for component, internal in zip(groups, internal_edges):
            if (internal and (len(component) > 1 or any(e[0] == e[1] for e in internal)) and
                    all(any(e[3][i] for e in internal) for i in range(len(game.fairness)))):
                return "REFUTED"
    return "VERIFIED"
