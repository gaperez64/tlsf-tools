"""Require classification of every Node/BoundedTemporalMeta field, even in padding.

The C unit supplies compile-time layout checks and one-field mutations. This
source census closes the sizeof/offsetof gap for new small union arms.
Update it together with expand.c's field table, the unit, and SetDedup.lean.
"""
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
source = (root / "include/tlsf/ast.h").read_text()
source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)


def fields(body):
    # Braces separate anonymous struct/union arms; keep every leaf declaration,
    # including unfamiliar types, rather than searching only for known names.
    return [re.findall(r"\w+|[^\s]", s)
            for s in re.findall(r"[^;{}]+;", body)]


node = source.split("struct Node {", 1)[1].split("\n};", 1)[0]
expected_node = """
NodeKind kind;
uint32_t source_id;
const OriginBinding *origin_bindings;
bool resolved_signal;
const char *name;
int64_t ival;
Node *arg;
Node *lhs;
Node *rhs;
const char *callee;
Node **call_args;
uint16_t call_argc;
const char *bus_name;
Node *bus_index;
const char *sizeof_name;
Node *if_cond;
Node *if_then;
Node *if_else;
const char *qvar;
Node *qlo;
Node *qhi;
Node *qset;
Node *qbody;
bool qlo_strict;
bool qhi_strict;
Node **set_elems;
uint16_t set_size;
BoundedTemporalMeta bounded;
"""
meta = source.split("} BoundedTemporalMeta;", 1)[0].rsplit("typedef struct {", 1)[1]
expected_meta = """
BoundedTemporalOrigin origin;
int64_t lo;
int64_t hi;
Node *body;
bool strong;
"""
assert fields(node) == fields(expected_node), "classify changed Node fields for set deduplication"
assert fields(meta) == fields(expected_meta), "classify changed bounded metadata for set deduplication"

# The C switch is exhaustive (-Werror=switch); also require every admitted C
# kind to be represented by a Lean constructor/tag. absent represents nullptr.
kinds = re.findall(r"\bNODE_[A-Z_]+\b", source.split("typedef enum NodeKind {", 1)[1]
                   .split("} NodeKind;", 1)[0])
models = {
    "HNode": {
        "TRUE": "tt", "FALSE": "ff", "INT": "int", "AP": "ap",
        "INT_VAR": "intVar", "SIZEOF": "sizeof", "BUS_INDEX": "busIndex",
        "ITE": "ite", "NEXT_N": "nextN",
    },
    "UnaryKind": {
        "NOT": "neg", "X": "next", "X_STRONG": "strongNext",
        "F": "eventually", "G": "globally", "INT_NEG": "intNeg",
        "SET_SIZE": "setSize", "SET_MIN": "setMin", "SET_MAX": "setMax",
    },
    "BinaryKind": {
        "AND": "conj", "OR": "disj", "IMPL": "impl", "EQUIV": "equiv",
        "R": "release", "W": "weakUntil", "U": "until", "M": "strongRelease",
        "INT_ADD": "intAdd", "INT_SUB": "intSub", "INT_MUL": "intMul",
        "INT_DIV": "intDiv", "INT_MOD": "intMod", "CMP_EQ": "cmpEq",
        "CMP_NE": "cmpNe", "CMP_LT": "cmpLt", "CMP_LE": "cmpLe",
        "CMP_GT": "cmpGt", "CMP_GE": "cmpGe", "SET_UNION": "setUnion",
        "SET_INTER": "setInter", "SET_DIFF": "setDiff", "IN": "mem",
        "MATCH": "matchGuard",
    },
    "CallKind": {"DEF_CALL": "definition", "PATTERN": "pattern"},
    "QuantKind": {
        "FORALL": "forall", "EXISTS": "exists", "SUM": "sum",
        "PRODUCT": "product", "SET_BIG_UNION": "setBigUnion",
        "SET_BIG_INTER": "setBigInter",
    },
    "RangeKind": {"G_RANGE": "globally", "F_RANGE": "eventually"},
    "SetKind": {"SET": "literal", "SET_ENUM": "enumeration"},
}
mapped_kinds = ["NODE_" + k for model in models.values() for k in model]
assert len(kinds) == len(set(kinds)) == 55, "update the C/Lean kind census"
assert set(kinds) == set(mapped_kinds) | {"NODE_KIND_COUNT"}
lean = (root / "proofs/TlsfProofs/SetDedup.lean").read_text()
for name, model in models.items():
    declaration = lean.split(f"inductive {name} where", 1)[1]
    declaration = re.split(r"\bderiving\b|\binductive\b", declaration, maxsplit=1)[0]
    constructors = set(re.findall(r"\|\s*«?(\w+)", declaration))
    expected = set(model.values())
    if name == "HNode":
        expected |= {"absent", "unary", "binary", "call", "quant", "range", "set"}
    assert constructors == expected, (name, "update the Lean kind correspondence")
print("set_dedup_field_inventory: 27 Node fields, 5 metadata fields, 54 node kinds")
