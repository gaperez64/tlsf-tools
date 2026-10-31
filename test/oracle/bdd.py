"""Small stdlib ROBDD algebra for the independent certificate oracle."""

from functools import lru_cache


class Expr:
    def __init__(self, manager, root):
        self.manager, self.root = manager, root

    def __and__(self, other):
        return self.manager.combine("and", self, other)

    def __or__(self, other):
        return self.manager.combine("or", self, other)

    def __xor__(self, other):
        return self.manager.combine("xor", self, other)

    def __neg__(self):
        return Expr(self.manager, self.manager.negate(self.root))

    def __eq__(self, other):
        return isinstance(other, Expr) and self.manager is other.manager and self.root == other.root


class Bdds:
    def __init__(self, capacity=1_000_000, cache=100_000):
        self.capacity = capacity
        self.nodes = [(float("inf"), 0, 0), (float("inf"), 1, 1)]
        self.unique = {}
        self.bddfalse, self.bddtrue = Expr(self, 0), Expr(self, 1)
        self.apply = lru_cache(maxsize=cache)(self._apply)
        self.negate = lru_cache(maxsize=cache)(self._negate)

    def node(self, var, low, high):
        if low == high:
            return low
        key = var, low, high
        if key not in self.unique:
            assert len(self.nodes) < self.capacity, "certificate oracle BDD capacity"
            self.unique[key] = len(self.nodes)
            self.nodes.append(key)
        return self.unique[key]

    def bdd_setvarnum(self, number):
        assert number >= 0

    def bdd_ithvar(self, var):
        return Expr(self, self.node(var, 0, 1))

    def _negate(self, root):
        if root < 2:
            return 1 - root
        var, low, high = self.nodes[root]
        return self.node(var, self.negate(low), self.negate(high))

    def combine(self, op, left, right):
        assert left.manager is self and right.manager is self
        return Expr(self, self.apply(op, min(left.root, right.root), max(left.root, right.root)))

    def _apply(self, op, left, right):
        if right < 2:
            return int({"and": bool(left) and bool(right),
                        "or": bool(left) or bool(right),
                        "xor": bool(left) != bool(right)}[op])
        if left == right:
            return 0 if op == "xor" else left
        if left == 0:
            return 0 if op == "and" else right
        if left == 1:
            return right if op == "and" else 1 if op == "or" else self.negate(right)
        lv, ll, lh = self.nodes[left]
        rv, rl, rh = self.nodes[right]
        var = min(lv, rv)
        if lv != var:
            ll = lh = left
        if rv != var:
            rl = rh = right
        low = self.apply(op, min(ll, rl), max(ll, rl))
        high = self.apply(op, min(lh, rh), max(lh, rh))
        return self.node(var, low, high)

    def bdd_done(self):
        self.apply.cache_clear()
        self.negate.cache_clear()
