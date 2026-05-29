%{
/* tlsf.y — TLSF v1.1/v1.2 parser */
#include "tlsf/spec.h"
#include "tlsf/ast.h"

#include <stdio.h>
#include <stdlib.h>

/* Forward declarations filled in by flex */
int  yylex(YYSTYPE *lval, YYLTYPE *lloc, yyscan_t scanner);
void yyerror(YYLTYPE *lloc, yyscan_t scanner, TlsfSpec *spec,
             const char *msg);
%}

/* -------------------------------------------------------------------------
 * Bison options
 * --------------------------------------------------------------------- */
%define api.pure full
%define api.token.prefix {TOK_}
%define parse.error detailed
%define parse.lac full

%param  { yyscan_t scanner }
%parse-param { TlsfSpec *spec }

%locations

/* -------------------------------------------------------------------------
 * Semantic value union
 * --------------------------------------------------------------------- */
%union {
  int64_t     ival;
  const char *sval;
  Node       *node;
  Node      **node_list; /* arena-allocated array, terminated by nullptr */
  uint32_t    uval;      /* list length scratch */
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

/* Punctuation */
%token TOK_LPAREN TOK_RPAREN TOK_LBRACKET TOK_RBRACKET
%token TOK_LBRACE TOK_RBRACE
%token TOK_COMMA TOK_SEMI TOK_COLON TOK_ASSIGN TOK_DOTDOT

/* -------------------------------------------------------------------------
 * Type declarations for non-terminals
 * --------------------------------------------------------------------- */
%type <node>      ltl_expr int_expr
%type <sval>      signal_name

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

info_field
  : TOK_TITLE TOK_COLON TOK_STRING TOK_SEMI
    { spec->info.title = $3; }

  | TOK_DESCRIPTION TOK_COLON TOK_STRING TOK_SEMI
    { spec->info.description = $3; }

  | TOK_SEMANTICS TOK_COLON semantics_val TOK_SEMI
    {}

  | TOK_TARGET TOK_COLON target_val TOK_SEMI
    {}

  | TOK_TAGS TOK_COLON tag_list TOK_SEMI
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
  : /* empty */
  | tag_list TOK_COMMA TOK_STRING
    { /* TODO: append $3 to spec->info.tags */ }
  | TOK_STRING
    { /* TODO: initialise spec->info.tags with $1 */ }
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
    { /* TODO: register parameter $2 with no default */ }
  | param_entries TOK_IDENT TOK_ASSIGN TOK_INTEGER TOK_SEMI
    { /* TODO: register parameter $2 with default $4 */ }
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
    { /* TODO: register nullary definition $1 = $3 */ }
  | TOK_IDENT TOK_LPAREN ident_list TOK_RPAREN TOK_ASSIGN ltl_expr TOK_SEMI
    { /* TODO: register parameterised definition $1($3) = $6 */ }
  ;

ident_list
  : TOK_IDENT
  | ident_list TOK_COMMA TOK_IDENT
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
  : TOK_INPUTS TOK_LBRACE signal_decl_list TOK_RBRACE
  ;

outputs_subsection
  : TOK_OUTPUTS TOK_LBRACE signal_decl_list TOK_RBRACE
  ;

signal_decl_list
  : /* empty */
  | signal_decl_list signal_decl TOK_SEMI
  ;

signal_decl
  : signal_name
    { /* TODO: add scalar signal $1 to appropriate list */ }
  | signal_name TOK_LBRACKET TOK_INTEGER TOK_DOTDOT TOK_INTEGER TOK_RBRACKET
    { /* TODO: add bus signal $1[$3..$5] */ }
  ;

signal_name
  : TOK_IDENT  { $$ = $1; }
  ;

/* -------------------------------------------------------------------------
 * Formula subsections — env side
 * --------------------------------------------------------------------- */

initially_subsection
  : TOK_INITIALLY TOK_LBRACE formula_list[fl] TOK_RBRACE
  ;

require_subsection
  : TOK_REQUIRE TOK_LBRACE formula_list TOK_RBRACE
  ;

assume_subsection
  : TOK_ASSUME TOK_LBRACE formula_list TOK_RBRACE
  ;

/* Formula subsections — sys side */

preset_subsection
  : TOK_PRESET TOK_LBRACE formula_list TOK_RBRACE
  ;

assert_subsection
  : TOK_ASSERT TOK_LBRACE formula_list TOK_RBRACE
  ;

guarantee_subsection
  : TOK_GUARANTEE TOK_LBRACE formula_list TOK_RBRACE
  ;

formula_list
  : /* empty */
  | formula_list ltl_expr TOK_SEMI
    { /* TODO: determine subsection and call formula_list_push() */ }
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

  /* Bus signal indexing: name[expr] */
  | TOK_IDENT TOK_LBRACKET int_expr TOK_RBRACKET
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      n->kind      = NODE_BUS_INDEX;
      n->bus_name  = $1;
      n->bus_index = $3;
      $$ = n;
    }

  /* Definition / function call: name(arg, ...) */
  | TOK_IDENT TOK_LPAREN call_arg_list TOK_RPAREN
    { /* TODO: build NODE_DEF_CALL */ $$ = nullptr; }

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

  /* Quantified expressions (TLSF sets) */
  | TOK_GLOBALLY TOK_LBRACKET quant_body TOK_RBRACKET ltl_expr
    { /* TODO: NODE_FORALL */ $$ = nullptr; }
  | TOK_FINALLY TOK_LBRACKET quant_body TOK_RBRACKET ltl_expr
    { /* TODO: NODE_EXISTS */ $$ = nullptr; }
  ;

/* Call argument list — zero or more ltl/int expressions */
call_arg_list
  : /* empty */
  | call_arg_list TOK_COMMA ltl_expr
  | ltl_expr
  ;

/* Quantifier binding: var : set_expr */
quant_body
  : TOK_IDENT TOK_COLON set_expr
  ;

/* =========================================================================
 * Integer expression grammar
 * ===================================================================== */

int_expr
  : TOK_INTEGER
    { $$ = node_int(spec->arena, $1); }
  | TOK_IDENT
    { /* integer variable reference */
      Node *n = ARENA_ALLOC(spec->arena, Node);
      n->kind = NODE_INT_VAR;
      n->name = $1;
      $$ = n;
    }
  | TOK_LPAREN int_expr TOK_RPAREN
    { $$ = $2; }
  | int_expr TOK_PLUS  int_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_ADD; $$->lhs = $1; $$->rhs = $3; }
  | int_expr TOK_MINUS int_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_SUB; $$->lhs = $1; $$->rhs = $3; }
  | int_expr TOK_STAR  int_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_MUL; $$->lhs = $1; $$->rhs = $3; }
  | int_expr TOK_SLASH int_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_DIV; $$->lhs = $1; $$->rhs = $3; }
  | int_expr TOK_PERCENT int_expr
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_MOD; $$->lhs = $1; $$->rhs = $3; }
  | TOK_MINUS int_expr %prec TOK_UMINUS
    { $$ = ARENA_ALLOC(spec->arena, Node);
      $$->kind = NODE_INT_NEG; $$->arg = $2; }
  ;

/* =========================================================================
 * Set expression grammar
 * ===================================================================== */

set_expr
  : TOK_LBRACE int_expr TOK_DOTDOT int_expr TOK_RBRACE
    { /* range {lo..hi} — TODO */ }
  | TOK_LBRACE set_elem_list TOK_RBRACE
    { /* explicit set — TODO */ }
  | TOK_IDENT
    { /* set variable — TODO */ }
  ;

set_elem_list
  : int_expr
  | set_elem_list TOK_COMMA int_expr
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
