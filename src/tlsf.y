%{
/* tlsf.y — TLSF v1.1/v1.2 parser */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
%}

/* Emitted into the generated header (tlsf_parse.h) and early in the parser
 * source, before YYSTYPE/YYLTYPE — so the union types and yyscan_t are known
 * everywhere the header is included. */
%code requires {
  #include "tlsf/spec.h"
  #include "tlsf/ast.h"
  #ifndef YY_TYPEDEF_YY_SCANNER_T
  #define YY_TYPEDEF_YY_SCANNER_T
  typedef void *yyscan_t;
  #endif
}

/* Emitted into the parser source after YYSTYPE/YYLTYPE are defined. */
%code {
  int  yylex(YYSTYPE *lval, YYLTYPE *lloc, yyscan_t scanner);
  void yyerror(YYLTYPE *lloc, yyscan_t scanner, TlsfSpec *spec,
               const char *msg);

  /* Append `item` to a nullptr-terminated Node* array, returning a fresh
   * array (the arena has no realloc; lists are short so the copy is cheap). */
  static Node **node_list_append(Arena *a, Node **old, Node *item) {
    size_t n = 0;
    while (old && old[n])
      n++;
    Node **arr = ARENA_ALLOC_N(a, Node *, n + 2);
    for (size_t i = 0; i < n; i++)
      arr[i] = old[i];
    arr[n] = item;
    arr[n + 1] = nullptr;
    return arr;
  }

  /* Append `s` to a nullptr-terminated const char* array. */
  static const char **slist_append(Arena *a, const char **old,
                                   const char *s) {
    size_t n = 0;
    while (old && old[n])
      n++;
    const char **arr = ARENA_ALLOC_N(a, const char *, n + 2);
    for (size_t i = 0; i < n; i++)
      arr[i] = old[i];
    arr[n] = s;
    arr[n + 1] = nullptr;
    return arr;
  }

  static uint16_t node_list_len(Node **arr) {
    uint16_t n = 0;
    while (arr && arr[n])
      n++;
    return n;
  }

  static uint16_t node_str_len(const char **arr) {
    uint16_t n = 0;
    while (arr && arr[n])
      n++;
    return n;
  }

  static Node *mk_ite(Arena *a, Node *cond, Node *then_, Node *else_) {
    Node *n = ARENA_ALLOC(a, Node);
    n->kind = NODE_ITE;
    n->if_cond = cond;
    n->if_then = then_;
    n->if_else = else_;
    return n;
  }

  static Node *mk_cmp(Arena *a, int kind, Node *lhs, Node *rhs) {
    Node *n = ARENA_ALLOC(a, Node);
    n->kind = (NodeKind)kind;
    n->lhs = lhs;
    n->rhs = rhs;
    return n;
  }

  static Node *mk_unary(Arena *a, NodeKind kind, Node *arg) {
    Node *n = ARENA_ALLOC(a, Node);
    n->kind = kind;
    n->arg = arg;
    return n;
  }

  static Node *mk_binary(Arena *a, NodeKind kind, Node *lhs, Node *rhs) {
    Node *n = ARENA_ALLOC(a, Node);
    n->kind = kind;
    n->lhs = lhs;
    n->rhs = rhs;
    return n;
  }

  static Node *mk_set(Arena *a, NodeKind kind, Node **elems) {
    Node *n = ARENA_ALLOC(a, Node);
    n->kind = kind;
    n->set_elems = elems;
    n->set_size = node_list_len(elems);
    return n;
  }

  /* Turn a comma-separated binder head into nested reductions, with the
   * leftmost binder outermost. */
  static Node *mk_reduction(NodeKind kind, Node **binders, Node *body) {
    uint16_t count = node_list_len(binders);
    for (uint16_t i = count; i > 0; i--) {
      Node *b = binders[i - 1];
      b->kind = kind;
      b->qbody = body;
      body = b;
    }
    return body;
  }

  /* Implicit invariant for an enum-typed signal: it always holds one of the
   * type's labels, i.e. G( (sig == L1) || (sig == L2) || ... ).  Each (sig ==
   * Li) expands to the positional bit match during expansion. */
  static Node *mk_enum_validity(TlsfSpec *spec, const EnumType *et,
                                const char *sig) {
    Arena *a = spec->arena;
    Node *acc = nullptr;
    for (uint16_t i = 0; i < et->label_count; i++) {
      const char *label = spec->enum_labels[et->label_start + i].name;
      Node *eq = mk_cmp(a, NODE_CMP_EQ, node_ap(a, sig), node_ap(a, label));
      acc = acc ? node_or(a, acc, eq) : eq;
    }
    return acc ? node_g(a, acc) : node_true(a);
  }
}

/* -------------------------------------------------------------------------
 * Bison options
 * --------------------------------------------------------------------- */
%define api.pure
%define parse.error detailed

/* TLSF case-definitions (`cond : value  cond : value  ...`) have no separator
 * between a case's value and the next case's guard, so the value `ltl_expr` is
 * juxtaposed against the next guard's `ltl_expr`.  The language is unambiguous
 * — a guard always contains a comparison operator (or is `otherwise`) and a
 * value never does — but proving which it is can require scanning past a whole
 * value expression to reach the comparison, i.e. unbounded lookahead.  LALR(1)
 * cannot do that, so a deterministic grammar would mis-resolve
 *     v - w      (value `v-w`)   vs   v   followed by guard `-w CMP ...`
 * and the `(` of a call vs. a parenthesised next guard.  A GLR parser explores
 * both and keeps the one that yields a valid parse, which is exactly correct
 * here.  The two conflict points (1 shift/reduce on TOK_LPAREN, 10
 * reduce/reduce on the binary-vs-unary `-` boundary) are asserted below so the
 * build stays clean and bison errors out if the grammar ever drifts. */
%glr-parser
%expect 53
%expect-rr 19

%param  { yyscan_t scanner }
%parse-param { TlsfSpec *spec }

%locations

/* -------------------------------------------------------------------------
 * Semantic value union
 * --------------------------------------------------------------------- */
%union {
  int64_t      ival;
  const char  *sval;
  Node        *node;
  Node       **node_list; /* nullptr-terminated array of nodes */
  const char **slist;     /* nullptr-terminated array of interned strings */
  uint32_t     uval;      /* list length scratch */
}

/* -------------------------------------------------------------------------
 * Token declarations
 * --------------------------------------------------------------------- */
%token <sval> TOK_IDENT TOK_STRING
%token <ival> TOK_INTEGER
%token        TOK_ERROR

/* Section / subsection keywords */
%token TOK_INFO TOK_GLOBAL TOK_MAIN
%token TOK_TITLE TOK_DESCRIPTION TOK_SEMANTICS TOK_TARGET TOK_TAGS
%token TOK_PARAMETERS TOK_DEFINITIONS TOK_ENUM
%token <sval> TOK_BITS
%token TOK_INPUTS TOK_OUTPUTS
%token TOK_INITIALLY TOK_PRESET TOK_REQUIRE TOK_ASSERT TOK_ASSUME TOK_GUARANTEE

/* Semantics / target values */
%token TOK_MEALY TOK_MOORE TOK_STRICT_MEALY TOK_STRICT_MOORE
%token TOK_FINITE_MEALY TOK_FINITE_MOORE

/* Boolean and LTL operators */
%token TOK_TRUE TOK_FALSE
%token TOK_NOT TOK_AND TOK_OR TOK_IMPL TOK_EQUIV
%token TOK_NEXT TOK_SNEXT TOK_FINALLY TOK_GLOBALLY
%token TOK_UNTIL TOK_RELEASE TOK_WEAK

/* Integer / comparison operators */
%token TOK_PLUS TOK_MINUS TOK_STAR TOK_SLASH TOK_PERCENT
%token TOK_EQ TOK_NEQ TOK_LT TOK_LEQ TOK_GT TOK_GEQ

/* Keyword operators */
%token TOK_SIZEOF TOK_SET_SIZE TOK_SET_MIN TOK_SET_MAX TOK_OTHERWISE
%token TOK_SET_UNION TOK_SET_INTER TOK_SET_DIFF TOK_IN TOK_MATCH

/* Punctuation */
%token TOK_LPAREN TOK_RPAREN TOK_LBRACKET TOK_RBRACKET
%token TOK_LBRACKET_STRONG TOK_RBRACKET_STRONG
%token TOK_LBRACE TOK_RBRACE
%token TOK_COMMA TOK_SEMI TOK_COLON TOK_ASSIGN TOK_DOTDOT TOK_BAR

/* -------------------------------------------------------------------------
 * Type declarations for non-terminals
 * --------------------------------------------------------------------- */
%type <node>      ltl_expr bound_spec cond cases set_literal
%type <ival>      lt_or_leq cmp_op
%type <sval>      signal_name
%type <slist>     ident_list
%type <node_list> call_arg_list nonempty_expr_list bound_list

/* -------------------------------------------------------------------------
 * Operator precedence (lowest → highest) — matches syfco / TLSF paper.
 * Temporal binary ops (W/U/R) bind looser than all propositional connectives,
 * contrary to standard LTL textbooks but consistent with syfco's parser:
 *   a && b W c  parses as  (a && b) W c
 *   a -> b W c  parses as  (a -> b) W c
 * --------------------------------------------------------------------- */
%right TOK_WEAK
%right TOK_UNTIL
%left  TOK_RELEASE
%right TOK_IMPL TOK_EQUIV
%left  TOK_OR
%left  TOK_AND
%precedence TOK_NOT TOK_GLOBALLY TOK_FINALLY TOK_NEXT TOK_SNEXT
%left  TOK_IN
%left  TOK_EQ TOK_NEQ TOK_LT TOK_LEQ TOK_GT TOK_GEQ
%left  TOK_SET_UNION
%left  TOK_SET_INTER
%right TOK_SET_DIFF
%left  TOK_PLUS TOK_MINUS
%right TOK_SLASH TOK_PERCENT
%left  TOK_STAR
%precedence TOK_UMINUS TOK_SET_SIZE TOK_SET_MIN TOK_SET_MAX

%%

/* =========================================================================
 * Top-level
 * ===================================================================== */

spec
  : info_section global_section_opt main_section
  | error { YYABORT; }
  ;

/* =========================================================================
 * INFO section
 * ===================================================================== */

info_section
  : TOK_INFO TOK_LBRACE info_fields TOK_RBRACE
  ;

info_fields
  : /* empty */
  | info_fields info_field
  ;

/* TLSF INFO fields are not semicolon-terminated; the bundled smoke test
 * uses trailing semicolons, so accept them optionally. */
semi_opt
  : /* empty */
  | TOK_SEMI
  ;

info_field
  : TOK_TITLE TOK_COLON TOK_STRING semi_opt
    { spec->info.title = $3; }

  | TOK_DESCRIPTION TOK_COLON TOK_STRING semi_opt
    { spec->info.description = $3; }

  | TOK_SEMANTICS TOK_COLON semantics_val semi_opt
    {}

  | TOK_TARGET TOK_COLON target_val semi_opt
    {}

  | TOK_TAGS TOK_COLON tag_list semi_opt
    {}
  ;

semantics_val
  : TOK_MEALY        { spec->info.semantics = SEM_MEALY; }
  | TOK_MOORE        { spec->info.semantics = SEM_MOORE; }
  | TOK_STRICT_MEALY { spec->info.semantics = SEM_MEALY_STRICT; }
  | TOK_STRICT_MOORE { spec->info.semantics = SEM_MOORE_STRICT; }
  | TOK_FINITE_MEALY { spec->info.semantics = SEM_MEALY_FINITE; }
  | TOK_FINITE_MOORE { spec->info.semantics = SEM_MOORE_FINITE; }
  ;

target_val
  : TOK_MEALY { spec->info.target = TARGET_MEALY; }
  | TOK_MOORE { spec->info.target = TARGET_MOORE; }
  ;

tag_list
  : TOK_STRING
    { if (!spec_add_tag(spec, $1)) YYNOMEM; }
  | tag_list TOK_COMMA TOK_STRING
    { if (!spec_add_tag(spec, $3)) YYNOMEM; }
  ;

/* =========================================================================
 * GLOBAL section (optional)
 * ===================================================================== */

global_section_opt
  : /* empty */
  | TOK_GLOBAL TOK_LBRACE global_decls TOK_RBRACE
  ;

global_decls
  : /* empty */
  | global_decls global_decl
  ;

global_decl
  : param_decl
  | def_decl
  ;

/* PARAMETERS { name [ = default ] ; ... } */
param_decl
  : TOK_PARAMETERS TOK_LBRACE param_entries TOK_RBRACE
  ;

param_entries
  : /* empty */
  | param_items
  ;

param_items
  : param_item
  | param_items TOK_SEMI param_item
  | param_items TOK_SEMI               /* trailing / stray ';' */
  ;

param_item
  : TOK_IDENT
    { if (!spec_add_param(spec, $1, false, 0)) YYNOMEM; }
  | TOK_IDENT TOK_ASSIGN TOK_INTEGER
    { if (!spec_add_param(spec, $1, true, $3)) YYNOMEM; }
  ;

/* DEFINITIONS { name [ ( params ) ] = body ; ... } */
def_decl
  : TOK_DEFINITIONS TOK_LBRACE def_entries TOK_RBRACE
  ;

def_entries
  : /* empty */
  | def_entries def_entry
  ;

def_entry
  : TOK_IDENT TOK_ASSIGN ltl_expr TOK_SEMI
    { if (!spec_add_def(spec, $1, nullptr, 0, $3)) YYNOMEM; }
  | TOK_IDENT TOK_ASSIGN cases TOK_SEMI
    { if (!spec_add_def(spec, $1, nullptr, 0, $3)) YYNOMEM; }
  | TOK_IDENT TOK_LPAREN ident_list TOK_RPAREN TOK_ASSIGN ltl_expr TOK_SEMI
    { if (!spec_add_def(spec, $1, $3, node_str_len($3), $6)) YYNOMEM; }
  | TOK_IDENT TOK_LPAREN ident_list TOK_RPAREN TOK_ASSIGN cases TOK_SEMI
    { if (!spec_add_def(spec, $1, $3, node_str_len($3), $6)) YYNOMEM; }
  /* enum NAME = LABEL: bits  LABEL: bits  ... ;  (NAME is unused; each label
     becomes a global bit-pattern matched by `bus == LABEL`). */
  | TOK_ENUM TOK_IDENT TOK_ASSIGN enum_labels TOK_SEMI
    { /* This enum's labels are those added since the previous enum type. */
      uint16_t prev_end = spec->enum_type_count
          ? (uint16_t)(spec->enum_types[spec->enum_type_count - 1].label_start +
                       spec->enum_types[spec->enum_type_count - 1].label_count)
          : 0;
      uint16_t end = spec->enum_label_count;
      uint32_t w = end > prev_end
          ? (uint32_t)strlen(spec->enum_labels[end - 1].bits)
          : 0;
      if (!spec_add_enum_type(spec, $2, w, prev_end,
                              (uint16_t)(end - prev_end)))
        YYNOMEM; }
  ;

enum_labels
  : TOK_IDENT TOK_COLON TOK_BITS
    { if (!spec_add_enum_label(spec, $1, $3)) YYNOMEM; }
  | enum_labels TOK_IDENT TOK_COLON TOK_BITS
    { if (!spec_add_enum_label(spec, $2, $4)) YYNOMEM; }
  ;

/* Definition guard chain:  cond : value  cond : value  ...  (right-nested ITE,
 * with a `false` default if no guard holds).
 *
 * TLSF separates a case's value from the next case's guard only by whitespace,
 * so `value <next-guard>` are two adjacent expressions.  This is not LALR(1)
 * conflict-free (it yields a handful of reduce/reduce conflicts on the binary
 * operators).  The conflicts are benign for well-formed specs: a guard is
 * `expr CMP expr` or `otherwise`, and a guard can never *begin* with a binary
 * operator, so bison's default resolution always ends the value at the right
 * point.  Verified by parsing/expanding the full SYNTCOMP corpus and checking
 * the result against syfco. */
cases
  : cond TOK_COLON ltl_expr
    { $$ = mk_ite(spec->arena, $1, $3, node_false(spec->arena)); }
  | cond TOK_COLON ltl_expr cases
    { $$ = mk_ite(spec->arena, $1, $3, $4); }
  ;

/* A guard is a comparison between integer expressions.  (TLSF definition
 * guards in practice are always comparisons, which keeps the value/guard
 * boundary unambiguous.) */
cond
  : ltl_expr cmp_op ltl_expr
    { $$ = mk_cmp(spec->arena, (int)$2, $1, $3); }
  | ltl_expr TOK_MATCH ltl_expr
    { $$ = mk_binary(spec->arena, NODE_MATCH, $1, $3); }
  | TOK_OTHERWISE
    { $$ = node_true(spec->arena); } /* catch-all default guard */
  ;

cmp_op
  : TOK_EQ  { $$ = NODE_CMP_EQ; }
  | TOK_NEQ { $$ = NODE_CMP_NE; }
  | TOK_LT  { $$ = NODE_CMP_LT; }
  | TOK_LEQ { $$ = NODE_CMP_LE; }
  | TOK_GT  { $$ = NODE_CMP_GT; }
  | TOK_GEQ { $$ = NODE_CMP_GE; }
  ;

ident_list
  : TOK_IDENT
    { $$ = slist_append(spec->arena, nullptr, $1); }
  | ident_list TOK_COMMA TOK_IDENT
    { $$ = slist_append(spec->arena, $1, $3); }
  ;

/* =========================================================================
 * MAIN section
 * ===================================================================== */

main_section
  : TOK_MAIN TOK_LBRACE main_subsections TOK_RBRACE
  ;

main_subsections
  : /* empty */
  | main_subsections main_subsection
  ;

main_subsection
  : inputs_subsection
  | outputs_subsection
  | initially_subsection
  | preset_subsection
  | require_subsection
  | assert_subsection
  | assume_subsection
  | guarantee_subsection
  ;

/* -------------------------------------------------------------------------
 * Signal declarations
 * --------------------------------------------------------------------- */

inputs_subsection
  : TOK_INPUTS TOK_LBRACE
    { spec->cur_is_output = false; }
    signal_decl_list TOK_RBRACE
  ;

outputs_subsection
  : TOK_OUTPUTS TOK_LBRACE
    { spec->cur_is_output = true; }
    signal_decl_list TOK_RBRACE
  ;

/* Separator-style list: ';' separates entries and a trailing ';' is optional
 * (TLSF lets the final entry omit it).  Empty lists are allowed. */
signal_decl_list
  : /* empty */
  | signal_decl_items
  ;

signal_decl_items
  : signal_decl
  | signal_decl_items TOK_SEMI signal_decl
  | signal_decl_items TOK_SEMI            /* trailing / stray ';' */
  ;

signal_decl
  : signal_name
    { if (!spec_add_signal(spec, spec->cur_is_output, $1, false,
                           nullptr, nullptr))
        YYNOMEM; }
  | signal_name TOK_LBRACKET ltl_expr TOK_DOTDOT ltl_expr TOK_RBRACKET
    { if (!spec_add_signal(spec, spec->cur_is_output, $1, true, $3, $5))
        YYNOMEM; }
  | signal_name TOK_LBRACKET ltl_expr TOK_RBRACKET
    { /* width form: name[N] declares indices 0..N-1 */
      Node *lo = node_int(spec->arena, 0);
      Node *hi = ARENA_ALLOC(spec->arena, Node);
      hi->kind = NODE_INT_SUB; hi->lhs = $3; hi->rhs = node_int(spec->arena, 1);
      if (!spec_add_signal(spec, spec->cur_is_output, $1, true, lo, hi))
        YYNOMEM; }
  /* enum-typed signal:  TYPE name;  declares a bus of the enum's bit width and
     adds the implicit "always a valid enum value" invariant — an assumption for
     an input, a guarantee for an output. */
  | TOK_IDENT signal_name
    { const EnumType *et = spec_find_enum_type(spec, $1);
      if (!et) {
        fprintf(stderr, "%d: unknown enum type '%s'\n", @1.first_line, $1);
        YYERROR;
      }
      Node *lo = node_int(spec->arena, 0);
      Node *hi = node_int(spec->arena, (int64_t)et->width - 1);
      if (!spec_add_signal(spec, spec->cur_is_output, $2, true, lo, hi))
        YYNOMEM;
      Node *valid = mk_enum_validity(spec, et, $2);
      FormulaList *list =
          spec->cur_is_output ? &spec->guarantee : &spec->assume;
      if (!formula_list_push(spec, list, valid))
        YYNOMEM; }
  ;

signal_name
  : TOK_IDENT  { $$ = $1; }
  ;

/* -------------------------------------------------------------------------
 * Formula subsections — env side
 * --------------------------------------------------------------------- */

initially_subsection
  : TOK_INITIALLY TOK_LBRACE
    { spec->cur_list = &spec->initially; } formula_list TOK_RBRACE
  ;

require_subsection
  : TOK_REQUIRE TOK_LBRACE
    { spec->cur_list = &spec->require; } formula_list TOK_RBRACE
  ;

assume_subsection
  : TOK_ASSUME TOK_LBRACE
    { spec->cur_list = &spec->assume; } formula_list TOK_RBRACE
  ;

/* Formula subsections — sys side */

preset_subsection
  : TOK_PRESET TOK_LBRACE
    { spec->cur_list = &spec->preset; } formula_list TOK_RBRACE
  ;

assert_subsection
  : TOK_ASSERT TOK_LBRACE
    { spec->cur_list = &spec->assert_; } formula_list TOK_RBRACE
  ;

guarantee_subsection
  : TOK_GUARANTEE TOK_LBRACE
    { spec->cur_list = &spec->guarantee; } formula_list TOK_RBRACE
  ;

formula_list
  : /* empty */
  | formula_items
  ;

formula_items
  : ltl_expr
    { if (!formula_list_push(spec, spec->cur_list, $1)) YYNOMEM; }
  | formula_items TOK_SEMI ltl_expr
    { if (!formula_list_push(spec, spec->cur_list, $3)) YYNOMEM; }
  | formula_items TOK_SEMI            /* trailing / stray ';' */
  ;

/* =========================================================================
 * LTL expression grammar
 *
 * Precedence is entirely handled by %left/%right declarations above, so
 * the grammar here is flat (single non-terminal).  Bison resolves the
 * shift-reduce conflicts by precedence.
 * ===================================================================== */

ltl_expr
  : TOK_TRUE
    { $$ = node_true(spec->arena); }
  | TOK_FALSE
    { $$ = node_false(spec->arena); }
  | TOK_IDENT
    { $$ = node_ap(spec->arena, $1); }

  /* Integer atoms / arithmetic.  TLSF has a single untyped expression
     grammar; numeric vs. boolean use is resolved during expansion.  An
     identifier in integer position is the bare TOK_IDENT (a NODE_AP) looked
     up as a variable by the evaluator. */
  | TOK_INTEGER
    { $$ = node_int(spec->arena, $1); }
  | TOK_SIZEOF TOK_IDENT
    { Node *n = ARENA_ALLOC(spec->arena, Node);
      n->kind = NODE_SIZEOF; n->sizeof_name = $2; $$ = n; }
  | TOK_SET_SIZE ltl_expr %prec TOK_SET_SIZE
    { $$ = mk_unary(spec->arena, NODE_SET_SIZE, $2); }
  | TOK_SET_MIN ltl_expr %prec TOK_SET_MIN
    { $$ = mk_unary(spec->arena, NODE_SET_MIN, $2); }
  | TOK_SET_MAX ltl_expr %prec TOK_SET_MAX
    { $$ = mk_unary(spec->arena, NODE_SET_MAX, $2); }
  | TOK_BAR ltl_expr TOK_BAR
    { $$ = mk_unary(spec->arena, NODE_SET_SIZE, $2); }
  | ltl_expr TOK_PLUS ltl_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_ADD; $$->lhs = $1; $$->rhs = $3; }
  | ltl_expr TOK_MINUS ltl_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_SUB; $$->lhs = $1; $$->rhs = $3; }
  | ltl_expr TOK_STAR ltl_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_MUL; $$->lhs = $1; $$->rhs = $3; }
  | ltl_expr TOK_SLASH ltl_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_DIV; $$->lhs = $1; $$->rhs = $3; }
  | ltl_expr TOK_PERCENT ltl_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_MOD; $$->lhs = $1; $$->rhs = $3; }
  | TOK_MINUS ltl_expr %prec TOK_UMINUS
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_NEG; $$->arg = $2; }

  /* Set expressions. */
  | set_literal
    { $$ = $1; }
  | ltl_expr TOK_SET_UNION ltl_expr
    { $$ = mk_binary(spec->arena, NODE_SET_UNION, $1, $3); }
  | ltl_expr TOK_SET_INTER ltl_expr
    { $$ = mk_binary(spec->arena, NODE_SET_INTER, $1, $3); }
  | ltl_expr TOK_SET_DIFF ltl_expr
    { $$ = mk_binary(spec->arena, NODE_SET_DIFF, $1, $3); }

  /* Bus signal indexing: name[expr] */
  | TOK_IDENT TOK_LBRACKET ltl_expr TOK_RBRACKET
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      n->kind      = NODE_BUS_INDEX;
      n->bus_name  = $1;
      n->bus_index = $3;
      $$ = n;
    }

  /* Definition / function call: name(arg, ...) */
  | TOK_IDENT TOK_LPAREN call_arg_list TOK_RPAREN
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      n->kind      = NODE_DEF_CALL;
      n->callee    = $1;
      n->call_args = $3;
      n->call_argc = node_list_len($3);
      $$ = n;
    }

  /* Parenthesised expression */
  | TOK_LPAREN ltl_expr TOK_RPAREN
    { $$ = $2; }

  /* Boolean connectives */
  | TOK_NOT ltl_expr
    { $$ = node_not(spec->arena, $2); }
  | ltl_expr TOK_AND ltl_expr
    { $$ = node_and(spec->arena, $1, $3); }
  | ltl_expr TOK_OR ltl_expr
    { $$ = node_or(spec->arena, $1, $3); }
  | ltl_expr TOK_IMPL ltl_expr
    { $$ = node_impl(spec->arena, $1, $3); }
  | ltl_expr TOK_EQUIV ltl_expr
    { $$ = node_equiv(spec->arena, $1, $3); }

  /* Formula-level equality: a bus compared against an enum label expands to a
     bit-match during expansion; integer == in this position folds to a
     constant.  (Only == / != appear at formula level; the ordered comparisons
     remain confined to definition guards.) */
  | ltl_expr TOK_EQ ltl_expr
    { $$ = mk_cmp(spec->arena, NODE_CMP_EQ, $1, $3); }
  | ltl_expr TOK_NEQ ltl_expr
    { $$ = mk_cmp(spec->arena, NODE_CMP_NE, $1, $3); }
  | ltl_expr TOK_LT ltl_expr
    { $$ = mk_cmp(spec->arena, NODE_CMP_LT, $1, $3); }
  | ltl_expr TOK_LEQ ltl_expr
    { $$ = mk_cmp(spec->arena, NODE_CMP_LE, $1, $3); }
  | ltl_expr TOK_GT ltl_expr
    { $$ = mk_cmp(spec->arena, NODE_CMP_GT, $1, $3); }
  | ltl_expr TOK_GEQ ltl_expr
    { $$ = mk_cmp(spec->arena, NODE_CMP_GE, $1, $3); }
  | ltl_expr TOK_IN ltl_expr
    { $$ = mk_binary(spec->arena, NODE_IN, $1, $3); }

  /* Unary temporal */
  | TOK_NEXT ltl_expr
    { $$ = node_x(spec->arena, $2); }
  | TOK_NEXT TOK_LBRACKET ltl_expr TOK_RBRACKET ltl_expr %prec TOK_NEXT
    { $$ = node_next_n(spec->arena, $3, $5); }
  | TOK_NEXT TOK_LBRACKET_STRONG ltl_expr TOK_RBRACKET ltl_expr %prec TOK_NEXT
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr, "%d:%d: parse error: strong bounded X is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_next_n(spec->arena, $3, $5); $$->bounded.strong = true; }
  | TOK_NEXT TOK_LBRACKET ltl_expr TOK_RBRACKET_STRONG ltl_expr %prec TOK_NEXT
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr, "%d:%d: parse error: strong bounded X is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_next_n(spec->arena, $3, $5); $$->bounded.strong = true; }
  | TOK_SNEXT ltl_expr
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr,
                "%d:%d: parse error: X[!] is only valid under finite "
                "semantics\n",
                @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_x_strong(spec->arena, $2); }
  | TOK_FINALLY ltl_expr
    { $$ = node_f(spec->arena, $2); }
  | TOK_FINALLY TOK_LBRACKET ltl_expr TOK_COLON ltl_expr TOK_RBRACKET ltl_expr
    %prec TOK_FINALLY
    { $$ = node_f_range(spec->arena, $3, $5, $7); }
  | TOK_FINALLY TOK_LBRACKET_STRONG ltl_expr TOK_COLON ltl_expr TOK_RBRACKET ltl_expr
    %prec TOK_FINALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr, "%d:%d: parse error: strong bounded F is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_f_range(spec->arena, $3, $5, $7); $$->bounded.strong = true; }
  | TOK_FINALLY TOK_LBRACKET ltl_expr TOK_COLON ltl_expr TOK_RBRACKET_STRONG ltl_expr
    %prec TOK_FINALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr, "%d:%d: parse error: strong bounded F is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_f_range(spec->arena, $3, $5, $7); $$->bounded.strong = true; }
  | TOK_GLOBALLY ltl_expr
    { $$ = node_g(spec->arena, $2); }
  | TOK_GLOBALLY TOK_LBRACKET ltl_expr TOK_COLON ltl_expr TOK_RBRACKET ltl_expr
    %prec TOK_GLOBALLY
    { $$ = node_g_range(spec->arena, $3, $5, $7); }
  | TOK_GLOBALLY TOK_LBRACKET_STRONG ltl_expr TOK_COLON ltl_expr TOK_RBRACKET ltl_expr
    %prec TOK_GLOBALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr, "%d:%d: parse error: strong bounded G is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_g_range(spec->arena, $3, $5, $7); $$->bounded.strong = true; }
  | TOK_GLOBALLY TOK_LBRACKET ltl_expr TOK_COLON ltl_expr TOK_RBRACKET_STRONG ltl_expr
    %prec TOK_GLOBALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(stderr, "%d:%d: parse error: strong bounded G is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      $$ = node_g_range(spec->arena, $3, $5, $7); $$->bounded.strong = true; }

  /* Binary temporal */
  | ltl_expr TOK_UNTIL ltl_expr
    { $$ = node_u(spec->arena, $1, $3); }
  | ltl_expr TOK_RELEASE ltl_expr
    { $$ = node_r(spec->arena, $1, $3); }
  | ltl_expr TOK_WEAK ltl_expr
    { $$ = node_w(spec->arena, $1, $3); }

  /* Generalized reductions over one or more range/set binders. */
  | TOK_AND TOK_LBRACKET bound_list TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_FORALL, $3, $5); }
  | TOK_OR TOK_LBRACKET bound_list TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_EXISTS, $3, $5); }
  | TOK_PLUS TOK_LBRACKET bound_list TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_SUM, $3, $5); }
  | TOK_STAR TOK_LBRACKET bound_list TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_PRODUCT, $3, $5); }
  | TOK_SET_UNION TOK_LBRACKET bound_list TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_SET_BIG_UNION, $3, $5); }
  | TOK_SET_INTER TOK_LBRACKET bound_list TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_SET_BIG_INTER, $3, $5); }
  ;

set_literal
  : TOK_LBRACE TOK_RBRACE
    { $$ = mk_set(spec->arena, NODE_SET, nullptr); }
  | TOK_LBRACE nonempty_expr_list TOK_RBRACE
    { $$ = mk_set(spec->arena, NODE_SET, $2); }
  | TOK_LBRACE ltl_expr TOK_COMMA ltl_expr TOK_DOTDOT ltl_expr TOK_RBRACE
    { Node **xs = node_list_append(spec->arena, nullptr, $2);
      xs = node_list_append(spec->arena, xs, $4);
      xs = node_list_append(spec->arena, xs, $6);
      $$ = mk_set(spec->arena, NODE_SET_ENUM, xs); }
  ;

nonempty_expr_list
  : ltl_expr
    { $$ = node_list_append(spec->arena, nullptr, $1); }
  | nonempty_expr_list TOK_COMMA ltl_expr
    { $$ = node_list_append(spec->arena, $1, $3); }
  ;

bound_list
  : bound_spec
    { $$ = node_list_append(spec->arena, nullptr, $1); }
  | bound_list TOK_COMMA bound_spec
    { $$ = node_list_append(spec->arena, $1, $3); }
  ;

/* Quantifier bound: lo (<|<=) var (<|<=) hi.  Builds a partial quantifier
 * node (kind set later by the caller); qbody is filled in afterwards. */
bound_spec
  : ltl_expr lt_or_leq[loS] TOK_IDENT[v] lt_or_leq[hiS] ltl_expr
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      n->qvar = $v;
      n->qlo = $1;
      n->qhi = $5;
      n->qlo_strict = $loS;
      n->qhi_strict = $hiS;
      $$ = n;
    }
  | TOK_IDENT[v] TOK_IN ltl_expr
    { Node *n = ARENA_ALLOC(spec->arena, Node);
      n->qvar = $v;
      n->qset = $3;
      $$ = n; }
  ;

lt_or_leq
  : TOK_LT  { $$ = 1; }  /* strict */
  | TOK_LEQ { $$ = 0; }  /* non-strict */
  ;

/* Call argument list — zero or more ltl/int expressions */
call_arg_list
  : /* empty */
    { $$ = nullptr; }
  | ltl_expr
    { $$ = node_list_append(spec->arena, nullptr, $1); }
  | call_arg_list TOK_COMMA ltl_expr
    { $$ = node_list_append(spec->arena, $1, $3); }
  ;

%%

/* =========================================================================
 * Error reporting
 * ===================================================================== */

void yyerror(YYLTYPE *lloc, yyscan_t scanner,
             TlsfSpec *spec, const char *msg) {
  (void)scanner;
  (void)spec;
  fprintf(stderr, "%d:%d: parse error: %s\n",
          lloc->first_line, lloc->first_column, msg);
}
