%{
/* tlsf.y — TLSF v1.1/v1.2 parser */
#include <stdio.h>
#include <stdlib.h>
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
}

/* -------------------------------------------------------------------------
 * Bison options
 * --------------------------------------------------------------------- */
%define api.pure full
%define parse.error detailed
%define parse.lac full

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
%token TOK_PARAMETERS TOK_DEFINITIONS
%token TOK_INPUTS TOK_OUTPUTS
%token TOK_INITIALLY TOK_PRESET TOK_REQUIRE TOK_ASSERT TOK_ASSUME TOK_GUARANTEE

/* Semantics / target values */
%token TOK_MEALY TOK_MOORE TOK_STRICT_MEALY TOK_STRICT_MOORE
%token TOK_FINITE_MEALY TOK_FINITE_MOORE

/* Boolean and LTL operators */
%token TOK_TRUE TOK_FALSE
%token TOK_NOT TOK_AND TOK_OR TOK_IMPL TOK_EQUIV
%token TOK_NEXT TOK_SNEXT TOK_FINALLY TOK_GLOBALLY
%token TOK_UNTIL TOK_RELEASE TOK_WEAK TOK_STRONG_REL

/* Integer / comparison operators */
%token TOK_PLUS TOK_MINUS TOK_STAR TOK_SLASH TOK_PERCENT
%token TOK_EQ TOK_NEQ TOK_LT TOK_LEQ TOK_GT TOK_GEQ

/* Keyword operators */
%token TOK_SIZEOF

/* Punctuation */
%token TOK_LPAREN TOK_RPAREN TOK_LBRACKET TOK_RBRACKET
%token TOK_LBRACE TOK_RBRACE
%token TOK_COMMA TOK_SEMI TOK_COLON TOK_ASSIGN TOK_DOTDOT

/* -------------------------------------------------------------------------
 * Type declarations for non-terminals
 * --------------------------------------------------------------------- */
%type <node>      ltl_expr bound_spec
%type <ival>      lt_or_leq
%type <sval>      signal_name
%type <slist>     ident_list
%type <node_list> call_arg_list

/* -------------------------------------------------------------------------
 * Operator precedence (lowest → highest)
 * Mirrors syfco's LTL expression grammar.
 * --------------------------------------------------------------------- */
%right TOK_IMPL TOK_EQUIV
%left  TOK_OR
%left  TOK_AND
%right TOK_UNTIL TOK_RELEASE TOK_WEAK TOK_STRONG_REL
%right TOK_GLOBALLY TOK_FINALLY TOK_NEXT TOK_SNEXT
%right TOK_NOT

/* Integer expression precedence */
%left  TOK_PLUS TOK_MINUS
%left  TOK_STAR TOK_SLASH TOK_PERCENT
%right TOK_UMINUS   /* pseudo-token for unary minus */

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
  | param_entries TOK_IDENT TOK_SEMI
    { if (!spec_add_param(spec, $2, false, 0)) YYNOMEM; }
  | param_entries TOK_IDENT TOK_ASSIGN TOK_INTEGER TOK_SEMI
    { if (!spec_add_param(spec, $2, true, $4)) YYNOMEM; }
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
  | TOK_IDENT TOK_LPAREN ident_list TOK_RPAREN TOK_ASSIGN ltl_expr TOK_SEMI
    {
      uint16_t argc = 0;
      while ($3 && $3[argc])
        argc++;
      if (!spec_add_def(spec, $1, $3, argc, $6)) YYNOMEM;
    }
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

signal_decl_list
  : /* empty */
  | signal_decl_list signal_decl TOK_SEMI
  | signal_decl_list TOK_SEMI            /* stray/empty entry (syfco tolerates) */
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
  | formula_list ltl_expr TOK_SEMI
    { if (!formula_list_push(spec, spec->cur_list, $2)) YYNOMEM; }
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

  /* Unary temporal */
  | TOK_NEXT ltl_expr
    { $$ = node_x(spec->arena, $2); }
  | TOK_SNEXT ltl_expr
    { $$ = node_x_strong(spec->arena, $2); }
  | TOK_FINALLY ltl_expr
    { $$ = node_f(spec->arena, $2); }
  | TOK_GLOBALLY ltl_expr
    { $$ = node_g(spec->arena, $2); }

  /* Binary temporal */
  | ltl_expr TOK_UNTIL ltl_expr
    { $$ = node_u(spec->arena, $1, $3); }
  | ltl_expr TOK_RELEASE ltl_expr
    { $$ = node_r(spec->arena, $1, $3); }
  | ltl_expr TOK_WEAK ltl_expr
    { $$ = node_w(spec->arena, $1, $3); }
  | ltl_expr TOK_STRONG_REL ltl_expr
    { $$ = node_m(spec->arena, $1, $3); }

  /* Bounded big-operators:  &&[lo R v R hi] body  /  ||[lo R v R hi] body */
  | TOK_AND TOK_LBRACKET bound_spec TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $3->kind = NODE_FORALL; $3->qbody = $5; $$ = $3; }
  | TOK_OR TOK_LBRACKET bound_spec TOK_RBRACKET ltl_expr %prec TOK_GLOBALLY
    { $3->kind = NODE_EXISTS; $3->qbody = $5; $$ = $3; }
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
