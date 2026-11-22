"""Keep proof correspondence locations on their intended C and Lean targets."""
from collections import Counter
from pathlib import Path
import re
import sys

# Stable source anchors, deliberately independent of line numbers. Every DPA
# and Lean location, including shorthand references and range endpoints, must
# point to one of these definitions or semantically relevant statements.
# Counts include repeated declarations; every occurrence needs a documented location.
ANCHORS = {
    'TlsfProofs/Dpa/Classes.lean': {
        'def HasTag (tag : Formula (Fin ap) → Prop) (x : Class ap) : Prop :=': 1,
        'def Protected (x : Class ap) (t : Formula (Fin ap)) : Prop :=': 1,
        'def subformulas : Formula α → List (Formula α)': 1,
        'noncomputable def reduce (x : Class ap) : Class ap :=': 1,
        'noncomputable def rho (x : Class ap) : Class ap :=': 1,
    },
    'TlsfProofs/Dpa/Converse.lean': {
        'inductive Pi2 : Formula α → Prop where': 1,
    },
    'TlsfProofs/Dpa/GeneralConverse.lean': {
        'theorem general_pi2_language (x : Class ap) (hx : NNFClass x) (hpi : HasTag Pi2 x)': 1,
    },
    'src/lib/dpa.c': {
        'uint32_t round = dpa_pair(c, c->acceptance, c->acceptance != 0);': 1,
        'c->max_priority = (c->components.n + 2) | 1u;': 1,
        'if (!c->started) {': 1,
        's->edges[0] = (TlsfDpaEdge){label, id, c->max_priority - !s->leaf};': 1,
    },
    'src/lib/dpa_dela.c': {
        'if (!c->buchi) {': 1,
        'static uint32_t seen_colours(TlsfDpa *c, uint32_t f, const uint64_t *colours) {': 1,
        'if (c->buchi) {': 1,
        'priority = round->rejecting;': 1,
        'result = dpa_dag(c, 2, 0, target, c->max_priority - !truth);': 1,
        'static uint32_t component(TlsfDpa *c, uint32_t f) {': 1,
        'static uint32_t joint(TlsfDpa *c, uint32_t tuple, uint32_t leaf,': 1,
        'static uint32_t terminal_condition(TlsfDpa *c, uint32_t f,': 1,
        'static uint32_t transition(TlsfDpa *c, uint32_t a, uint32_t r) {': 1,
        'uint32_t dpa_acceptance(TlsfDpa *c, uint32_t f) {': 1,
        'uint32_t dpa_dela_initial(TlsfDpa *c) {': 1,
        'uint32_t dpa_dela_step(TlsfDpa *c, uint32_t tuple, uint32_t leaf) {': 1,
        'uint32_t dpa_pair(TlsfDpa *c, uint32_t a, uint32_t r) {': 1,
    },
    'src/lib/dpa_formula.c': {
        'static uint32_t buchi_syntax(TlsfDpa *c, uint32_t id) {': 1,
        'static uint32_t term(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b) {': 1,
        'static uint32_t materialize(TlsfDpa *c, uint32_t f) {': 1,
        'static uint32_t wrap_next(TlsfDpa *c, uint32_t f, unsigned next) {': 1,
        'uint32_t dpa_atom(TlsfDpa *c, TlsfAstKind op, uint32_t a, uint32_t b) {': 1,
        'uint32_t dpa_dual(TlsfDpa *c, uint32_t f) {': 1,
        'bool dpa_admitted(TlsfDpa *c, uint32_t f) {': 1,
        'bool dpa_children(TlsfDpa *c, uint32_t f) {': 1,
        'bool dpa_has_tags(TlsfDpa *c, uint32_t f, unsigned mask) {': 1,
        'if (cosafety != (uint32_t)conjunction)': 1,
        'return grouped ? syntax_acceptance(c, id) : dpa_acceptance(c, f);': 1,
        'static bool check_admission(TlsfDpa *c, uint32_t f, uint64_t epoch) {': 1,
        'static bool groupable(TlsfDpa *c, uint32_t id, uint64_t epoch) {': 1,
        'static uint32_t factor_term(TlsfDpa *c, uint32_t id) {': 1,
        'static uint32_t formula_impl(TlsfDpa *c, const TlsfAstNode *n, bool neg,': 1,
        'static uint32_t map_impl(TlsfDpa *c, uint32_t f, unsigned mode, uint64_t epoch,': 2,
        'static uint32_t syntax_acceptance(TlsfDpa *c, uint32_t id) {': 1,
        'static uint32_t unfold_atom_care(TlsfDpa *c, DpaAtom *atom, uint32_t cube,': 1,
        'static uint32_t unfold_class_care(TlsfDpa *c, uint32_t f, uint32_t cube,': 1,
        'static unsigned tags_impl(TlsfDpa *c, uint32_t f) {': 1,
        'static void group_operands(TlsfDpa *c, uint32_t id, TlsfAstKind op,': 1,
        'static void protected_term(TlsfDpa *c, uint32_t id, bool *protect,': 1,
        'static void protected_x(TlsfDpa *c, uint32_t f, bool *protect, uint64_t epoch) {': 1,
        'static void tag_bounds(TlsfDpa *c, uint32_t f, unsigned *lo, unsigned *hi) {': 1,
        'uint32_t dpa_boolean(TlsfDpa *c, bool conjunction, uint32_t a, uint32_t b) {': 1,
        'uint32_t dpa_class(TlsfDpa *c, Bdd owned) {': 1,
        'uint32_t dpa_grouped_acceptance(TlsfDpa *c, uint32_t f) {': 1,
        'uint32_t dpa_ite(TlsfDpa *c, uint32_t v, uint32_t hi, uint32_t lo) {': 1,
        'uint32_t dpa_remainder(TlsfDpa *c, uint32_t f) {': 1,
        'uint32_t dpa_step_dag(TlsfDpa *c, uint32_t f) {': 1,
        'uint32_t dpa_unfold(TlsfDpa *c, uint32_t f) {': 1,
        'unsigned dpa_tags(TlsfDpa *c, uint32_t f) {': 1,
    },
    'src/lib/dpa_zielonka.c': {
        'return c->max_priority - priority;': 1,
        'static bool before(TlsfDpa *c, const uint64_t *a, const uint64_t *b) {': 1,
        'static uint32_t leftmost(TlsfDpa *c, uint32_t id) {': 1,
        'static uint32_t outside(TlsfDpa *c, const uint64_t *set,': 1,
        'static uint32_t path(TlsfDpa *c, uint32_t node, uint32_t parent, uint32_t pos) {': 1,
        'static uint32_t tree(TlsfDpa *c, const uint64_t *set) {': 1,
        'static void model(TlsfDpa *c, uint32_t f, uint64_t *set) {': 1,
        'uint32_t dpa_tree_step(TlsfDpa *c, uint32_t *leaf, const uint64_t *colours) {': 1,
        'void dpa_tree_init(TlsfDpa *c) {': 1,
    },
}

root = Path(sys.argv[1])
expected_locations = {}
for name, anchors in ANCHORS.items():
    path = root / ("proofs/" + name if name.startswith("TlsfProofs/") else name)
    lines = path.read_text().splitlines()
    occurrences = Counter(line.strip() for line in lines if line.strip() in anchors)
    assert occurrences == Counter(anchors), (name, "anchor occurrence counts changed",
                                             occurrences, anchors)
    expected_locations[name] = {i for i, line in enumerate(lines, 1)
                                if line.strip() in anchors}
documents = [root / "proofs/README.md"] + sorted(
    (root / "proofs/TlsfProofs/Dpa/Impl").glob("*.lean"))
# A shorthand location inherits the last named file in the same paragraph or
# table. This includes `:891`/`:914` and the Lean `:578`–`:596` range.
reference = re.compile(
    r"`(?P<name>(?:src/[\w/]+\.(?:c|cc|h)|(?:proofs/)?TlsfProofs/[\w/]+\.lean|print_ltlxba\.c))?"
    r":(?P<locations>\d+(?:[–,-]\d+)*)`")
count = anchored = 0
seen = {name: set() for name in ANCHORS}
covered = {}
for block in (block for document in documents
              for block in re.split(r"\n\s*\n", document.read_text())):
    name = None
    for match in reference.finditer(block):
        name = match["name"] or name
        if name and name.startswith("proofs/"):
            name = name.removeprefix("proofs/")
        locations = match["locations"]
        assert name is not None, f"orphan shorthand reference: {match[0]}"
        if name.startswith("TlsfProofs/"):
            path = root / "proofs" / name
        else:
            path = root / (name if name.startswith("src/") else "src/lib/" + name)
        lines = path.read_text().splitlines()
        for part in locations.split(","):
            bounds = [int(n) for n in re.split("[–-]", part)]
            assert 1 <= bounds[0] <= bounds[-1] <= len(lines), (name, locations)
            covered.setdefault(name, set()).update(range(bounds[0] - 1, bounds[-1]))
            for line in set(bounds):
                target = lines[line - 1].strip()
                if name in ANCHORS:
                    assert target in ANCHORS[name], (
                        f"{name}:{line} points to {target!r}, not a correspondence anchor")
                    seen[name].add(line)
                    anchored += 1
                if name == "src/tools/tlsfcompose/main.c":
                    assert 'fputs("ctl ", dst);' in target, (
                        f"{name}:{line} refers to {target!r}, not controller emission")
        count += 1
assert count, "no proof source references found"
assert seen == expected_locations, "a C/Lean anchor occurrence lost its documentation reference"
# The native witness and Lean bridge must occur within the documented ranges.
RANGE_ANCHORS = {
    "src/lib/env_witness.c": (
        "static int compile_node(",
        "static EnvWitnessResult evaluate(",
        "EnvWitnessResult env_witness_search(",
    ),
    "TlsfProofs/Pruning.lean": (
        "def environmentFormula ",
        "theorem environment_sat_iff ",
        "theorem envSat_of_word ",
    ),
}
for name, declarations in RANGE_ANCHORS.items():
    path = root / ("proofs/" + name if name.startswith("TlsfProofs/") else name)
    lines = path.read_text().splitlines()
    for declaration in declarations:
        assert any(declaration in lines[i] for i in covered.get(name, ())), (
            name, declaration, "missing from correspondence ranges")
print(f"checked {count} proof source references, {anchored} C/Lean targets; "
      "controller emission and native witness bridge found")
