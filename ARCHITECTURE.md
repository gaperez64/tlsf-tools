# tlsf-tools — Architecture & Remaining Tasks

## Overview

Two Unix-style command-line tools sharing a common library:

| Tool | Input | Output |
|---|---|---|
| `tlsf2ltl` | TLSF 1.1/1.2 spec | LTL formula in ltlxba format (for spot, ltl2ba, etc.) |
| `tlsf2tlsf` | TLSF 1.1/1.2 spec | Expanded basic TLSF (no GLOBAL section, flat formula lists) |

Both tools: parse → expand → (nnf + classify for `tlsf2ltl`) → print.

---

## Design decisions (locked)

- **C23**, LLVM style enforced via `.clang-format` / `.clang-tidy`
- **meson** build system, flex/bison via `custom_target()`, generated C stays in builddir
- **flex + bison** (LALR(1)) for the lexer/parser
- **Arena allocator**: all AST nodes, interned strings, spec structs live in a
  single slab-based bump allocator; teardown is one `arena_free()` call
- **String interning**: FNV-1a open-addressing hash table; pointer equality
  works for all identifier comparisons after interning
- **Safety/liveness split**: syntactic, after NNF — a formula is SAFETY if it
  contains no `NODE_F`, `NODE_U`, or `NODE_M` nodes anywhere in the tree
- **NNF before classification** (essential: `!(G p)` must become `F(!p)` before
  the safety check)
- **Expansion order**: parameters → definitions → bus unrolling → patterns
  (matches syfco)
- **ltlxba output**: fully parenthesised, not byte-for-byte syfco-compatible
  but accepted by spot / ltl2ba
- **Basic TLSF output**: INFO block preserved + MAIN with INPUTS, OUTPUTS, and
  all six formula subsections (INITIALLY, PRESET, REQUIRE, ASSERT, ASSUME,
  GUARANTEE); no GLOBAL section

---

## Repository layout

```
tlsf-tools/
├── .clang-format          LLVM style config
├── .clang-tidy            Check config (snake_case, bugprone, cert, etc.)
├── meson.build            Build definition
├── meson.options          User options (sanitize combo)
├── ARCHITECTURE.md        This file
│
├── include/tlsf/
│   ├── arena.h            Slab bump allocator API
│   ├── ast.h              LTL AST node types + constructors
│   ├── intern.h           String interning table API
│   ├── spec.h             Top-level TlsfSpec structure
│   ├── expand.h           Expansion pass API + ParamOverride type
│   ├── nnf.h              Negation normal form transform API
│   ├── classify.h         Safety/liveness classification API
│   ├── print_ltlxba.h     ltlxba printer API
│   └── print_tlsf.h       Basic TLSF printer API
│
├── src/
│   ├── arena.c            ✅ complete
│   ├── intern.c           ✅ complete
│   ├── ast.c              ✅ complete
│   ├── spec.c             ✅ complete
│   ├── nnf.c              ✅ complete
│   ├── classify.c         ✅ complete
│   ├── print_ltlxba.c     ✅ complete
│   ├── print_tlsf.c       ✅ complete
│   ├── main_tlsf2ltl.c    ✅ complete
│   ├── main_tlsf2tlsf.c   ✅ complete
│   ├── tlsf.l             ⚠️  needs fixes (see Task 1)
│   ├── tlsf.y             ⚠️  skeleton (see Task 2)
│   └── expand.c           ⚠️  skeleton (see Task 3)
│
└── test/
    └── arbiter_simple.tlsf  minimal smoke-test spec
```

---

## AST node taxonomy

```
NodeKind (include/tlsf/ast.h)
│
├── Atoms:        NODE_TRUE, NODE_FALSE, NODE_AP, NODE_INT
├── Boolean:      NODE_NOT, NODE_AND, NODE_OR, NODE_IMPL, NODE_EQUIV
├── LTL safety:   NODE_X, NODE_G, NODE_R (release), NODE_W (weak until)
├── LTL liveness: NODE_F, NODE_U (until), NODE_M (strong release)
├── LTLf only:    NODE_X_STRONG (X[!])
├── Int exprs:    NODE_INT_ADD/SUB/MUL/DIV/MOD/NEG, NODE_INT_VAR
├── Set exprs:    NODE_SET, NODE_SET_ENUM, NODE_FORALL, NODE_EXISTS
└── Pre-expand:   NODE_DEF_CALL, NODE_BUS_INDEX, NODE_PATTERN
```

NNF duality table (used in `nnf.c`):

| Positive | Negative (under ¬) |
|---|---|
| `U` | `R` |
| `R` | `U` |
| `W` | `M` |
| `M` | `W` |
| `G` | `F` |
| `F` | `G` |
| `X` | `X` (commutes) |
| `AND` | `OR` |
| `OR` | `AND` |

---

## Pipeline (per tool)

```
TLSF file
    │
    ▼  [tlsf.l + tlsf.y]
  TlsfSpec (raw AST, may contain DEF_CALL, BUS_INDEX, PATTERN, INT_VAR, ...)
    │
    ▼  [expand.c]  4 phases: params → defs → buses → patterns
  TlsfSpec (ground AST, no high-level nodes, GLOBAL section cleared)
    │
    ├─── tlsf2tlsf: [print_tlsf.c] ──► stdout/file  (basic TLSF)
    │
    ▼  [nnf.c]  to_nnf(arena, node, polarity=true)
  TlsfSpec (all formula lists in NNF)
    │
    ▼  [classify.c]  classify_spec()
  ClassifiedSpec (each guarantee/assert tagged SAFETY or LIVENESS)
    │
    └─── tlsf2ltl: [print_ltlxba.c] ──► stdout  (ltlxba LTL)
                   --safety    → PRINT_SAFETY
                   --liveness  → PRINT_LIVENESS
                   (default)   → PRINT_ALL
```

---

## Remaining tasks

### Task 1 — Fix `src/tlsf.l` (BLOCKER)

The lexer does not currently compile. Three concrete issues:

#### 1a. Single-letter temporal/boolean operator keywords conflict with IDENT

`X`, `F`, `G`, `U`, `R`, `W`, `M` are valid TLSF signal names as well as LTL
operators.  The current rules fire for any bare `X`, `F`, etc. in a formula
context, which is correct, but they also fire in signal declaration contexts
where an AP named `X` should remain an `AP`.

**Recommended fix**: remove the standalone keyword rules for single-letter
operators and handle them in the `IDENT` rule via a keyword lookup table
(same pattern as most LTL lexers).  Alternatively, use bison's contextual
token approach and let the grammar disambiguate.  The latter is simpler here
because TLSF's grammar is mostly unambiguous about where operators vs. APs
appear.

Concretely: keep the single-letter rules but accept that signal names cannot
be `X`, `F`, `G`, `U`, `R`, `W`, `M` (this is what syfco does — reserved
words).  The fix then is just to make sure the rules don't produce "unrecognized
rule" errors, which were caused by `nullptr` in action code and bad pattern
syntax — both fixed in the last revision of `tlsf.l`.

#### 1b. `"X[!]"` pattern

In flex, `"X[!]"` is a literal string match for `X[!]` — the brackets are
**not** character classes inside double quotes.  This is correct.  However,
the rule must appear **before** the `"X"` rule (flex uses first-match), which
it does in the current file.  Verify this compiles after 1a is resolved.

#### 1c. `Strict,Mealy` / `Finite,Moore` etc. semantics tokens

The patterns `"Strict"{WS}*","...` are **invalid flex syntax** — named
definitions (`{WS}`) cannot be interpolated inside a quoted string pattern.
The cleanest fix:

```lex
/* Option A: explicit alternatives (no whitespace around comma) */
"Strict,Mealy"      { return TOK_STRICT_MEALY; }
"Strict,Moore"      { return TOK_STRICT_MOORE; }
"Finite,Mealy"      { return TOK_FINITE_MEALY; }
"Finite,Moore"      { return TOK_FINITE_MOORE; }
```

In practice TLSF specs do not put whitespace around the comma in semantics
values, so this is fine. If whitespace tolerance is needed, use a regex pattern
(unquoted): `Strict[ \t]*,[ \t]*Mealy`.

#### 1d. `"//"` line comment rule

`"//".*/\n` uses a trailing context (`/\n`) which is valid flex but the `.*`
already consumes to end-of-line.  Simplify to:

```lex
"//"[^\n]*  { /* line comment */ }
```

---

### Task 2 — Complete `src/tlsf.y` grammar actions (CORE WORK)

The grammar structure and token declarations are complete.  The following
action bodies are stubs (`/* TODO */`) and need to be filled in:

#### 2a. Tag list (`tag_list` rule)

```c
// Allocate spec->info.tags as an arena array and append each string.
// Pattern: same as formula_list_push() but for const char *.
```

#### 2b. Parameter declarations (`param_entries` rule)

```c
// Grow spec->params (arena-allocated array of ParamDecl).
// Set .name (interned), .has_default, .default_val.
// Note: default values can be integer expressions, not just literals —
// store them as Node * for later evaluation in expand.c phase 1,
// or evaluate immediately if they're literals.
```

#### 2c. Definition declarations (`def_entries` rule)

```c
// Grow spec->defs (arena-allocated array of DefDecl).
// For parameterised definitions, collect the ident_list into an
// arena-allocated const char ** array.
// Store the formula body as a Node *.
```

#### 2d. Signal declarations (`signal_decl` rule)

```c
// The grammar currently does not distinguish INPUTS from OUTPUTS context.
// Fix: use a parser state flag (e.g. a bool in a local parse context struct
// threaded through %parse-param, or simply duplicate the rules for
// inputs_subsection vs outputs_subsection).
// Grow spec->inputs or spec->outputs accordingly.
// For bus signals, store bus_lo and bus_hi, set is_bus=true.
```

#### 2e. Formula subsection routing (`formula_list` rule)

```c
// The formula_list rule is shared across all six subsections.
// The grammar currently does not know which subsection it is in.
// Fix options:
//   A. Duplicate formula_list into six typed rules (verbose but clear).
//   B. Add a FormulaList *current_list pointer to a parse-param context
//      struct and set it at the start of each subsection rule.
// Option B is cleaner — define a ParseCtx struct:
//   typedef struct { TlsfSpec *spec; FormulaList *current_list; } ParseCtx;
// Pass ParseCtx * as the %parse-param instead of TlsfSpec *.
```

#### 2f. `NODE_DEF_CALL` construction (`ltl_expr` rule)

```c
// Build a NODE_DEF_CALL node from the call_arg_list.
// The call_arg_list rule needs to collect nodes into an arena array.
// Add a semantic value type for node lists (Node **) to the %union.
```

#### 2g. Quantifier rules (`NODE_FORALL` / `NODE_EXISTS`)

```c
// Build NODE_FORALL / NODE_EXISTS from quant_body + ltl_expr.
// quant_body needs to pass the bound variable name and set expression
// back up to the ltl_expr rule via a %type <...> declaration.
```

---

### Task 3 — Complete `src/expand.c` (CORE WORK)

The transform infrastructure (`transform_all_formulas`, `transform_node`) is
complete.  The four phase functions need their TODO bodies filled:

#### 3a. Phase 1: `resolve_parameters()`

- Integer expression evaluation: `NODE_INT_ADD/SUB/MUL/DIV/MOD/NEG` over
  `NODE_INT` and `NODE_INT_VAR` (parameter references).
- Build a name→value lookup (can be a simple linear scan over `spec->params`
  given typical spec sizes).
- Detect undefined parameters (ones with neither override nor default).

#### 3b. Phase 2: `inline_definitions()` — `inline_node()`

- Look up `n->callee` in `spec->defs` by interned pointer equality.
- Cycle detection: maintain a `const char *expanding[MAX_DEF_DEPTH]` stack
  and error out if the same name appears twice.
- Argument binding: build a temporary substitution map
  `formal_name → actual_node` (arena-allocated array of pairs).
- **Deep copy with substitution**: recursively copy the definition body,
  replacing `NODE_INT_VAR` nodes whose name matches a formal parameter with
  the corresponding actual node.  Use a fresh recursive descent (not
  `transform_node`) to avoid mutating shared definition bodies.

#### 3c. Phase 3: `unroll_buses()` — `unroll_node()`

- `NODE_BUS_INDEX`: evaluate `n->bus_index` (must be ground integer after
  phase 1+2); construct interned name `"<bus_name>_<i>"` via
  `snprintf` + `intern()`; return `NODE_AP`.
- `NODE_FORALL` over a range `{lo..hi}`: produce a conjunction
  `φ[x:=lo] ∧ φ[x:=lo+1] ∧ ... ∧ φ[x:=hi]` by copying the body `hi-lo+1`
  times with integer substitution.
- `NODE_EXISTS` over a range: produce a disjunction analogously.
- `NODE_SET` / `NODE_SET_ENUM`: enumerate elements and produce
  conjunction/disjunction as above.

#### 3d. Phase 4: `instantiate_patterns()` — `instantiate_node()`

TLSF 1.1 named patterns (from the syfco source / spec document):

| Pattern name | Arity | LTL expansion |
|---|---|---|
| `or(φ₁,...,φₙ)` | n | `φ₁ ∨ ... ∨ φₙ` |
| `and(φ₁,...,φₙ)` | n | `φ₁ ∧ ... ∧ φₙ` |
| `mux(s,φ₁,φ₀)` | 3 | `(s → φ₁) ∧ (¬s → φ₀)` |
| `toggle(s,lo,hi)` | 3 | see spec §3 |
| `rise(s)` | 1 | `¬s ∧ X s` |
| `fall(s)` | 1 | `s ∧ X ¬s` |
| `changed(s)` | 1 | `s ↔ X s` (negated) |

Consult the TLSF v1.1 paper (arXiv:1604.02284) Appendix B for the full list
and their precise LTL encodings.

---

### Task 4 — Lexer/parser wiring in `main_*.c`

The `main_*.c` files reference `tlsf_lex.h` and `tlsf_parse.h` for:
- `yylex_init` / `yylex_destroy`
- `yyset_extra` / `yyset_in`
- `yyparse`
- `yyscan_t`

These are generated by flex (`--header-file`) and bison (`--defines`).
Once Tasks 1 and 2 are complete and the build succeeds, verify:
- The `yyset_in(fp, scanner)` call correctly associates the FILE * with the
  scanner (reentrant flex API).
- Error recovery: bison's `error` token in the top-level `spec` rule calls
  `YYABORT`; verify this propagates `parse_result != 0` back to `main`.

---

### Task 5 — Remaining `spec.c` helpers

`formula_list_push()` uses a grow-by-doubling strategy but allocates a new
arena array each time (since the arena has no realloc).  This means old arrays
are wasted but still valid memory in the arena — acceptable for typical spec
sizes.  If very large specs are a concern, consider pre-sizing formula lists
based on a first-pass count.

Signal declaration arrays (`spec->inputs`, `spec->outputs`) currently have no
push helper.  Add:

```c
bool signal_list_push(TlsfSpec *s, SignalDecl **list, uint32_t *count,
                      uint32_t *cap, SignalDecl decl);
```

or inline the same grow-by-doubling pattern used in the bison actions.

---

### Task 6 — `print_ltlxba.c`: `X[!]` for LTLf specs

Currently `NODE_X_STRONG` emits `(X ...)` for compatibility.  Add a flag or
check `spec->info.semantics == SEM_MEALY_FINITE` to emit `(X[!] ...)` for
LTLf specs targeting spot (which understands `X[!]`).

---

### Task 7 — `.clang-tidy` suppressions for generated code

Flex and bison generate C that does not pass clang-tidy.  Add to
`meson.build`:

```meson
# Suppress tidy on generated files by passing --extra-arg to clang-tidy
# or by adding a per-file suppression in .clang-tidy via HeaderFilterRegex.
```

The current `HeaderFilterRegex` in `.clang-tidy` already excludes the
builddir, so generated files are not checked.  Verify this is sufficient once
the build is clean.

---

### Task 8 — Test suite

Add a `test/` directory with:
- `arbiter_simple.tlsf` (already present) — basic smoke test
- A parameterised spec exercising the GLOBAL section
- A bus spec exercising `signal[0..3]` unrolling
- A spec with all six subsections populated
- Expected output files (`.ltlxba`, `.basic.tlsf`) for regression testing

Wire into meson:
```meson
test('arbiter_round_trip',
  find_program('sh'),
  args: ['-c',
    tlsf2tlsf.full_path() + ' test/arbiter_simple.tlsf | diff - test/arbiter_simple.expected.tlsf'])
```

---

### Task 9 — `meson.options` / meson version warning

The build currently warns:
```
WARNING: Project specifies no minimum version but uses features added in 1.1
```
Fix by adding to `meson.build`:
```meson
meson.version().version_compare('>= 1.1')
```
or add `meson_version: '>= 1.1'` to the `project()` call.

Also rename `meson.options` → `meson_options.txt` for compatibility with
meson < 1.1 if broader portability is desired.

---

## Build instructions

```sh
# First-time setup
meson setup build

# Build
ninja -C build

# Build with ASan+UBSan
meson setup build-san -Dsanitize=address,undefined
ninja -C build-san

# Run clang-format (check only)
clang-format --dry-run --Werror src/*.c src/*.l src/*.y include/tlsf/*.h

# Apply clang-format
clang-format -i src/*.c src/*.l src/*.y include/tlsf/*.h

# Run clang-tidy (requires compile_commands.json from meson)
clang-tidy -p build src/arena.c src/intern.c src/ast.c src/spec.c \
           src/nnf.c src/classify.c src/expand.c \
           src/print_ltlxba.c src/print_tlsf.c \
           src/main_tlsf2ltl.c src/main_tlsf2tlsf.c
```

---

## Key references

- TLSF v1.2 paper: arXiv:2303.03839 (Jacobs, Pérez, Schlehuber-Caissier)
- TLSF v1.1 paper: arXiv:1604.02284 (Jacobs, Klein, Schirmer) — Appendix B has pattern definitions
- syfco source: https://github.com/reactive-systems/syfco (Haskell reference implementation)
- Preprocessing inspiration: arXiv:2401.11290
- ltlxba format: accepted by `ltl2ba`, `spot --formula`, `ltl3ba`
