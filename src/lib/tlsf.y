%{
/* Clear freed pointers: GLR startup failure otherwise frees a stale pointer. */
#define YYFREE(p) (free(p), (p) = nullptr)
/* tlsf.y — TLSF v1.1/v1.2 parser */
#include <stdio.h>
#include "diagnostic.h"
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
  typedef struct TlsfParseInput TlsfParseInput;
}

%code provides {
  int tlsf_parse(yyscan_t scanner, TlsfSpec *spec);
}

/* Emitted into the parser source after YYSTYPE/YYLTYPE are defined. */
%code {
  int yylex(YYSTYPE *lval, YYLTYPE *lloc, yyscan_t scanner);
  void yyerror(YYLTYPE *lloc, TlsfParseInput *input, TlsfSpec *spec,
               const char *msg);

  /* The six operator spellings also denote reductions when followed by '['.
   * Label that notation with one token of lexical lookahead, including across
   * comments/newlines handled by the existing lexer. This never chooses a case
   * boundary or builds an expression; ordinary precedence below does that.
   * Distinct heads let it shift binary continuations without swallowing the
   * next case's reduction. The flat expression grammar also preserves prefix
   * composition such as MIN CUP[k IN {1}] {k} (tiers would exclude that form).
   * Storage belongs to this parse, not the scanner or a global token replay. */
  struct TlsfParseInput {
    yyscan_t scanner;
    bool pending;
    int token;
    YYSTYPE value;
    YYLTYPE location;
  };

  static int expression_lex(YYSTYPE *value, YYLTYPE *location,
                            TlsfParseInput *input) {
    int token;
    if (input->pending) {
      token = input->token;
      *value = input->value;
      *location = input->location;
      input->pending = false;
    } else {
      token = yylex(value, location, input->scanner);
    }
    int head;
    switch (token) {
    case TOK_PLUS:      head = TOK_SUM_HEAD; break;
    case TOK_STAR:      head = TOK_PRODUCT_HEAD; break;
    case TOK_AND:       head = TOK_FORALL_HEAD; break;
    case TOK_OR:        head = TOK_EXISTS_HEAD; break;
    case TOK_SET_UNION: head = TOK_UNION_HEAD; break;
    case TOK_SET_INTER: head = TOK_INTER_HEAD; break;
    default: return token;
    }
    input->value = (YYSTYPE){0};
    input->location = *location;
    input->token = yylex(&input->value, &input->location, input->scanner);
    input->pending = true;
    return input->token == TOK_LBRACKET ? head : token;
  }
  #define yylex expression_lex

  /* Append `item` to a nullptr-terminated Node* array, returning a fresh
   * array (the arena has no realloc; lists are short so the copy is cheap). */
  static Node **node_list_append(Arena *a, Node **old, Node *item) {
    size_t n = 0;
    while (old && old[n])
      n++;
    Node **arr = ARENA_ALLOC_N(a, Node *, n + 2);
    if (!arr)
      return nullptr;
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
    if (!arr)
      return nullptr;
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
    if (!n)
      return nullptr;
    n->kind = NODE_ITE;
    n->if_cond = cond;
    n->if_then = then_;
    n->if_else = else_;
    return n;
  }

  static Node *mk_cmp(Arena *a, int kind, Node *lhs, Node *rhs) {
    Node *n = ARENA_ALLOC(a, Node);
    if (!n)
      return nullptr;
    n->kind = (NodeKind)kind;
    n->lhs = lhs;
    n->rhs = rhs;
    return n;
  }

  static Node *mk_unary(Arena *a, NodeKind kind, Node *arg) {
    Node *n = ARENA_ALLOC(a, Node);
    if (!n)
      return nullptr;
    n->kind = kind;
    n->arg = arg;
    return n;
  }

  static Node *mk_binary(Arena *a, NodeKind kind, Node *lhs, Node *rhs) {
    Node *n = ARENA_ALLOC(a, Node);
    if (!n)
      return nullptr;
    n->kind = kind;
    n->lhs = lhs;
    n->rhs = rhs;
    return n;
  }

  static Node *mk_set(Arena *a, NodeKind kind, Node **elems) {
    Node *n = ARENA_ALLOC(a, Node);
    if (!n)
      return nullptr;
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

  static const char *join_enum_values(TlsfSpec *spec, const char *lhs,
                                      const char *rhs) {
    size_t lhs_len = strlen(lhs);
    size_t rhs_len = strlen(rhs);
    char *joined = ARENA_ALLOC_N(spec->arena, char, lhs_len + rhs_len + 2u);
    if (!joined)
      return nullptr;
    memcpy(joined, lhs, lhs_len);
    joined[lhs_len] = ',';
    memcpy(joined + lhs_len + 1u, rhs, rhs_len + 1u);
    return intern(spec->intern, joined);
  }

  static uint32_t enum_value_width(const char *values) {
    return (uint32_t)strcspn(values, ",");
  }

  static bool enum_values_have_width(const char *values, uint32_t width) {
    const char *at = values;
    while (*at) {
      const char *end = strchr(at, ',');
      size_t length = end ? (size_t)(end - at) : strlen(at);
      if (length != width)
        return false;
      at = end ? end + 1 : at + length;
    }
    return true;
  }

  /* Implicit validity of an enum-typed signal.  The caller places this raw
   * state formula in REQUIRE (input) or ASSERT (output), as prescribed by TLSF;
   * the selected standard/strict semantics supplies the temporal context. */
  static Node *mk_enum_validity(TlsfSpec *spec, const EnumType *et,
                                const char *sig) {
    Arena *a = spec->arena;
    Node *acc = nullptr;
    for (uint16_t i = 0; i < et->label_count; i++) {
      const char *label = spec->enum_labels[et->label_start + i].name;
      /* Preserve GCC's right-first node allocation order. */
      Node *rhs = node_ap(a, label);
      Node *lhs = node_ap(a, sig);
      if (!rhs || !lhs)
        return nullptr;
      Node *eq = mk_cmp(a, NODE_CMP_EQ, lhs, rhs);
      if (!eq)
        return nullptr;
      acc = acc ? node_or(a, acc, eq) : eq;
      if (!acc)
        return nullptr;
    }
    return acc ? acc : node_true(a);
  }
}

/* -------------------------------------------------------------------------
 * Bison options
 * --------------------------------------------------------------------- */
/* GLR cleanup also visits fields left unset by partial initialization. */
%initial-action { yystack.yytops = (yyGLRStateSet){0}; }
%define api.pure
%define parse.error detailed

/* Three shift/reduce conflicts, zero reduce/reduce; no dynamic precedence.
 * LT and LEQ retain a comparison versus the first range-binder delimiter in
 * bound_spec until the later identifier/comparison delimiters decide it.
 * COMMA retains {first,second,...} versus {first,second..last} until '..' or
 * the following comma/brace. If complete parses still tie (e.g. two possible
 * range-binder identifiers), reject explicitly instead of selecting by order.
 * Binary/reduction starts are lexically distinct above; case completion and
 * identifier-call '(' use ordinary static precedence. */
%glr-parser
%expect 3
%expect-rr 0

%param  { TlsfParseInput *input }
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
/* Reduction notation, distinguished from the same binary spelling. */
%token TOK_SUM_HEAD TOK_PRODUCT_HEAD TOK_FORALL_HEAD TOK_EXISTS_HEAD
%token TOK_UNION_HEAD TOK_INTER_HEAD

/* Punctuation */
%token TOK_LPAREN TOK_RPAREN TOK_LBRACKET TOK_RBRACKET
%token TOK_LBRACKET_STRONG TOK_RBRACKET_STRONG
%token TOK_LBRACE TOK_RBRACE
%token TOK_COMMA TOK_SEMI TOK_COLON TOK_ASSIGN TOK_DOTDOT TOK_BAR

/* -------------------------------------------------------------------------
 * Type declarations for non-terminals
 * --------------------------------------------------------------------- */
%type <node>      ltl_expr expr bound_spec cases guarded_expr single_case case_head set_literal
%type <ival>      lt_or_leq
%type <sval>      signal_name enum_values
%type <slist>     ident_list
%type <node_list> call_arg_list nonempty_expr_list bound_list

/* -------------------------------------------------------------------------
 * Operator precedence (lowest → highest): TLSF v1.1 Table 1, p.118.
 * W binds tighter than U, which binds tighter than R. All three bind looser
 * than implication/equivalence. The extensions X[n], X[!n], X[!], F/G ranges
 * retain unary temporal precedence; unary minus retains numeric precedence.
 * --------------------------------------------------------------------- */
%precedence TOK_EXPR
%precedence TOK_LPAREN
%left  TOK_MATCH
%left  TOK_RELEASE
%right TOK_UNTIL
%right TOK_WEAK
%right TOK_IMPL TOK_EQUIV
%left  TOK_OR
%left  TOK_AND
%precedence TOK_NOT TOK_GLOBALLY TOK_FINALLY TOK_NEXT TOK_SNEXT
%left  TOK_IN
%left  TOK_EQ TOK_NEQ TOK_LT TOK_LEQ TOK_GT TOK_GEQ
%left  TOK_SET_UNION
%left  TOK_SET_INTER
%right TOK_SET_DIFF
%precedence TOK_BIG_SET
%left  TOK_PLUS TOK_MINUS
%right TOK_SLASH TOK_PERCENT
%left  TOK_STAR
%precedence TOK_UMINUS TOK_SET_SIZE TOK_SET_MIN TOK_SET_MAX TOK_BIG_NUM

%%

/* =========================================================================
 * Top-level
 * ===================================================================== */

spec
  : info_section global_section_opt main_section
  | error { if (arena_failed(spec->arena)) YYNOMEM; YYABORT; }
  ;

/* =========================================================================
 * INFO section
 * ===================================================================== */

info_section
  : TOK_INFO TOK_LBRACE info_fields TOK_RBRACE
  ;

info_fields
  : %empty
  | info_fields info_field
  ;

/* TLSF INFO fields are not semicolon-terminated; the bundled smoke test
 * uses trailing semicolons, so accept them optionally. */
semi_opt
  : %empty
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
  : %empty
  | TOK_GLOBAL TOK_LBRACE global_decls TOK_RBRACE
  ;

global_decls
  : %empty
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
  : %empty
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
  : %empty
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
  /* enum NAME = LABEL: valuation[,valuation...] ... ;  Each valuation is a
     width-bearing word over 0, 1, and *. */
  | TOK_ENUM TOK_IDENT TOK_ASSIGN enum_labels TOK_SEMI
    { /* This enum's labels are those added since the previous enum type. */
      uint16_t prev_end = spec->enum_type_count
          ? (uint16_t)(spec->enum_types[spec->enum_type_count - 1].label_start +
                       spec->enum_types[spec->enum_type_count - 1].label_count)
          : 0;
      uint16_t end = spec->enum_label_count;
      uint32_t w = end > prev_end
          ? enum_value_width(spec->enum_labels[prev_end].bits)
          : 0;
      for (uint16_t label = prev_end; label < end; ++label)
        if (!enum_values_have_width(spec->enum_labels[label].bits, w)) {
          fprintf(tlsf_diagnostic_stream(), "%d: enum '%s' has inconsistent valuation widths\n",
                  @2.first_line, $2);
          YYERROR;
        }
      if (!spec_add_enum_type(spec, $2, w, prev_end,
                              (uint16_t)(end - prev_end)))
        YYNOMEM; }
  ;

enum_labels
  : TOK_IDENT TOK_COLON enum_values
    { if (!spec_add_enum_label(spec, $1, $3)) YYNOMEM; }
  | enum_labels TOK_IDENT TOK_COLON enum_values
    { if (!spec_add_enum_label(spec, $2, $4)) YYNOMEM; }
  ;

enum_values
  : TOK_BITS
    { $$ = $1; }
  | enum_values TOK_COMMA TOK_BITS
    { if (!($$ = join_enum_values(spec, $1, $3))) YYNOMEM; }
  ;

/* TLSF v1.1 §4.6 gives cases no separator, (ec)+. Longest match:
 * finish a guard/value only when its expression cannot continue. TOK_EXPR is
 * below every expression operator and '(' (identifier calls); single_case
 * therefore shifts continuations. A following ':' extends guarded_expr with
 * Table 1 row 19's left association, including within a case list. Delimiters
 * can force an earlier boundary: (value) (guard) : value. */
cases
  : guarded_expr guarded_expr
    { if (!($$ = mk_ite(spec->arena, $1->if_cond, $1->if_then, $2))) YYNOMEM; }
  | guarded_expr cases
    { if (!($$ = mk_ite(spec->arena, $1->if_cond, $1->if_then, $2))) YYNOMEM; }
  ;

single_case
  : case_head expr %prec TOK_EXPR
    { Node *otherwise = node_false(spec->arena);
      if (!otherwise ||
          !($$ = mk_ite(spec->arena, $1, $2, otherwise))) YYNOMEM; }
  ;

case_head
  : expr TOK_COLON
    { $$ = $1; }
  | TOK_OTHERWISE TOK_COLON
    { if (!($$ = node_true(spec->arena))) YYNOMEM; }
  ;

guarded_expr
  : single_case
    { $$ = $1; }
  | guarded_expr TOK_COLON expr %prec TOK_EXPR
    { Node *otherwise = node_false(spec->arena);
      if (!otherwise ||
          !($$ = mk_ite(spec->arena, $1, $3, otherwise))) YYNOMEM; }
  ;

ident_list
  : TOK_IDENT
    { if (!($$ = slist_append(spec->arena, nullptr, $1))) YYNOMEM; }
  | ident_list TOK_COMMA TOK_IDENT
    { if (!($$ = slist_append(spec->arena, $1, $3))) YYNOMEM; }
  ;

/* =========================================================================
 * MAIN section
 * ===================================================================== */

main_section
  : TOK_MAIN TOK_LBRACE main_subsections TOK_RBRACE
  ;

main_subsections
  : %empty
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
  : %empty
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
      if (!lo || !hi)
        YYNOMEM;
      hi->kind = NODE_INT_SUB; hi->lhs = $3;
      if (!(hi->rhs = node_int(spec->arena, 1))) YYNOMEM;
      if (!spec_add_signal(spec, spec->cur_is_output, $1, true, lo, hi))
        YYNOMEM; }
  /* enum-typed signal: TYPE name; declares a bus of the enum's bit width and
     adds the spec-defined implicit validity constraint: a global requirement
     for an input and a global invariant for an output. */
  | TOK_IDENT signal_name
    { const EnumType *et = spec_find_enum_type(spec, $1);
      if (!et) {
        fprintf(tlsf_diagnostic_stream(), "%d: unknown enum type '%s'\n", @1.first_line, $1);
        YYERROR;
      }
      Node *lo = node_int(spec->arena, 0);
      Node *hi = node_int(spec->arena, (int64_t)et->width - 1);
      if (!lo || !hi) YYNOMEM;
      if (!spec_add_signal(spec, spec->cur_is_output, $2, true, lo, hi))
        YYNOMEM;
      SignalDecl *signals =
          spec->cur_is_output ? spec->outputs : spec->inputs;
      uint32_t count =
          spec->cur_is_output ? spec->output_count : spec->input_count;
      signals[count - 1u].origin_is_enum = true;
      Node *valid = mk_enum_validity(spec, et, $2);
      if (!valid) YYNOMEM;
      FormulaList *list =
          spec->cur_is_output ? &spec->assert_ : &spec->require;
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
  : %empty
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
 * ':' is structurally left-associative in guarded_expr. All other operators
 * use the flat expr grammar and Table 1 declarations above, preserving prefix
 * composition even across levels (e.g. MIN CUP[...] {...}). A chained ':'
 * stays in the current case. Parentheses/calls/sets/indices admit ltl_expr.
 * ===================================================================== */

ltl_expr
  : expr
    { $$ = $1; }
  | guarded_expr %prec TOK_EXPR
    { $$ = $1; }
  ;

expr
  : TOK_TRUE
    { if (!($$ = node_true(spec->arena))) YYNOMEM; }
  | TOK_FALSE
    { if (!($$ = node_false(spec->arena))) YYNOMEM; }
  | TOK_IDENT %prec TOK_EXPR
    { if (!($$ = node_ap(spec->arena, $1))) YYNOMEM; }

  /* Integer atoms / arithmetic.  TLSF has a single untyped expression
     grammar; numeric vs. boolean use is resolved during expansion.  An
     identifier in integer position is the bare TOK_IDENT (a NODE_AP) looked
     up as a variable by the evaluator. */
  | TOK_INTEGER
    { if (!($$ = node_int(spec->arena, $1))) YYNOMEM; }
  | TOK_SIZEOF TOK_IDENT
    { Node *n = ARENA_ALLOC(spec->arena, Node);
      if (!n) YYNOMEM;
      n->kind = NODE_SIZEOF; n->sizeof_name = $2; $$ = n; }
  | TOK_SET_SIZE expr %prec TOK_SET_SIZE
    { if (!($$ = mk_unary(spec->arena, NODE_SET_SIZE, $2))) YYNOMEM; }
  | TOK_SET_MIN expr %prec TOK_SET_MIN
    { if (!($$ = mk_unary(spec->arena, NODE_SET_MIN, $2))) YYNOMEM; }
  | TOK_SET_MAX expr %prec TOK_SET_MAX
    { if (!($$ = mk_unary(spec->arena, NODE_SET_MAX, $2))) YYNOMEM; }
  | TOK_BAR ltl_expr TOK_BAR
    { if (!($$ = mk_unary(spec->arena, NODE_SET_SIZE, $2))) YYNOMEM; }
  | expr TOK_PLUS expr
    { if (!($$ = mk_binary(spec->arena, NODE_INT_ADD, $1, $3))) YYNOMEM; }
  | expr TOK_MINUS expr
    { if (!($$ = mk_binary(spec->arena, NODE_INT_SUB, $1, $3))) YYNOMEM; }
  | expr TOK_STAR expr
    { if (!($$ = mk_binary(spec->arena, NODE_INT_MUL, $1, $3))) YYNOMEM; }
  | expr TOK_SLASH expr
    { if (!($$ = mk_binary(spec->arena, NODE_INT_DIV, $1, $3))) YYNOMEM; }
  | expr TOK_PERCENT expr
    { if (!($$ = mk_binary(spec->arena, NODE_INT_MOD, $1, $3))) YYNOMEM; }
  | TOK_MINUS expr %prec TOK_UMINUS
    { if (!($$ = mk_unary(spec->arena, NODE_INT_NEG, $2))) YYNOMEM; }

  /* Set expressions. */
  | set_literal
    { $$ = $1; }
  | expr TOK_SET_UNION expr
    { if (!($$ = mk_binary(spec->arena, NODE_SET_UNION, $1, $3))) YYNOMEM; }
  | expr TOK_SET_INTER expr
    { if (!($$ = mk_binary(spec->arena, NODE_SET_INTER, $1, $3))) YYNOMEM; }
  | expr TOK_SET_DIFF expr
    { if (!($$ = mk_binary(spec->arena, NODE_SET_DIFF, $1, $3))) YYNOMEM; }

  /* Bus signal indexing: name[expr] */
  | TOK_IDENT TOK_LBRACKET ltl_expr TOK_RBRACKET
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      if (!n) YYNOMEM;
      n->kind      = NODE_BUS_INDEX;
      n->bus_name  = $1;
      n->bus_index = $3;
      $$ = n;
    }

  /* Definition / function call: name(arg, ...) */
  | TOK_IDENT TOK_LPAREN call_arg_list TOK_RPAREN
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      if (!n) YYNOMEM;
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
  | TOK_NOT expr
    { if (!($$ = node_not(spec->arena, $2))) YYNOMEM; }
  | expr TOK_AND expr
    { if (!($$ = node_and(spec->arena, $1, $3))) YYNOMEM; }
  | expr TOK_OR expr
    { if (!($$ = node_or(spec->arena, $1, $3))) YYNOMEM; }
  | expr TOK_IMPL expr
    { if (!($$ = node_impl(spec->arena, $1, $3))) YYNOMEM; }
  | expr TOK_EQUIV expr
    { if (!($$ = node_equiv(spec->arena, $1, $3))) YYNOMEM; }

  /* Formula-level equality: a bus compared against an enum label expands to a
     bit-match during expansion; integer == in this position folds to a
     constant.  (Only == / != appear at formula level; the ordered comparisons
     remain confined to definition guards.) */
  | expr TOK_EQ expr
    { if (!($$ = mk_cmp(spec->arena, NODE_CMP_EQ, $1, $3))) YYNOMEM; }
  | expr TOK_NEQ expr
    { if (!($$ = mk_cmp(spec->arena, NODE_CMP_NE, $1, $3))) YYNOMEM; }
  | expr TOK_LT expr
    { if (!($$ = mk_cmp(spec->arena, NODE_CMP_LT, $1, $3))) YYNOMEM; }
  | expr TOK_LEQ expr
    { if (!($$ = mk_cmp(spec->arena, NODE_CMP_LE, $1, $3))) YYNOMEM; }
  | expr TOK_GT expr
    { if (!($$ = mk_cmp(spec->arena, NODE_CMP_GT, $1, $3))) YYNOMEM; }
  | expr TOK_GEQ expr
    { if (!($$ = mk_cmp(spec->arena, NODE_CMP_GE, $1, $3))) YYNOMEM; }
  | expr TOK_IN expr
    { if (!($$ = mk_binary(spec->arena, NODE_IN, $1, $3))) YYNOMEM; }

  /* Table 1's two loosest expression operators. */
  | expr TOK_MATCH expr
    { if (!($$ = mk_binary(spec->arena, NODE_MATCH, $1, $3))) YYNOMEM; }

  /* Unary temporal */
  | TOK_NEXT expr
    { if (!($$ = node_x(spec->arena, $2))) YYNOMEM; }
  | TOK_NEXT TOK_LBRACKET ltl_expr TOK_RBRACKET expr %prec TOK_NEXT
    { if (!($$ = node_next_n(spec->arena, $3, $5))) YYNOMEM; }
  | TOK_NEXT TOK_LBRACKET_STRONG ltl_expr TOK_RBRACKET expr %prec TOK_NEXT
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: strong bounded X is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_next_n(spec->arena, $3, $5))) YYNOMEM; $$->bounded.strong = true; }
  | TOK_NEXT TOK_LBRACKET ltl_expr TOK_RBRACKET_STRONG expr %prec TOK_NEXT
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: strong bounded X is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_next_n(spec->arena, $3, $5))) YYNOMEM; $$->bounded.strong = true; }
  | TOK_SNEXT expr
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(),
                "%d:%d: parse error: X[!] is only valid under finite "
                "semantics\n",
                @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_x_strong(spec->arena, $2))) YYNOMEM; }
  | TOK_FINALLY expr
    { if (!($$ = node_f(spec->arena, $2))) YYNOMEM; }
  /* Read the outermost ':' as the temporal range delimiter. The structural
   * pair in guarded_expr carries the two numerical bounds without introducing
   * another colon-versus-delimiter ambiguity. */
  | TOK_FINALLY TOK_LBRACKET guarded_expr TOK_RBRACKET expr
    %prec TOK_FINALLY
    { if (!($$ = node_f_range(spec->arena, $3->if_cond, $3->if_then, $5))) YYNOMEM; }
  | TOK_FINALLY TOK_LBRACKET_STRONG guarded_expr TOK_RBRACKET expr
    %prec TOK_FINALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: strong bounded F is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_f_range(spec->arena, $3->if_cond, $3->if_then, $5))) YYNOMEM; $$->bounded.strong = true; }
  | TOK_FINALLY TOK_LBRACKET guarded_expr TOK_RBRACKET_STRONG expr
    %prec TOK_FINALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: strong bounded F is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_f_range(spec->arena, $3->if_cond, $3->if_then, $5))) YYNOMEM; $$->bounded.strong = true; }
  | TOK_GLOBALLY expr
    { if (!($$ = node_g(spec->arena, $2))) YYNOMEM; }
  | TOK_GLOBALLY TOK_LBRACKET guarded_expr TOK_RBRACKET expr
    %prec TOK_GLOBALLY
    { if (!($$ = node_g_range(spec->arena, $3->if_cond, $3->if_then, $5))) YYNOMEM; }
  | TOK_GLOBALLY TOK_LBRACKET_STRONG guarded_expr TOK_RBRACKET expr
    %prec TOK_GLOBALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: strong bounded G is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_g_range(spec->arena, $3->if_cond, $3->if_then, $5))) YYNOMEM; $$->bounded.strong = true; }
  | TOK_GLOBALLY TOK_LBRACKET guarded_expr TOK_RBRACKET_STRONG expr
    %prec TOK_GLOBALLY
    { if (!semantics_is_finite(spec->info.semantics)) {
        fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: strong bounded G is only valid "
                "under finite semantics\n", @1.first_line, @1.first_column);
        YYERROR;
      }
      if (!($$ = node_g_range(spec->arena, $3->if_cond, $3->if_then, $5))) YYNOMEM; $$->bounded.strong = true; }

  /* Binary temporal */
  | expr TOK_UNTIL expr
    { if (!($$ = node_u(spec->arena, $1, $3))) YYNOMEM; }
  | expr TOK_RELEASE expr
    { if (!($$ = node_r(spec->arena, $1, $3))) YYNOMEM; }
  | expr TOK_WEAK expr
    { if (!($$ = node_w(spec->arena, $1, $3))) YYNOMEM; }

  /* Generalized reductions over one or more range/set binders. */
  | TOK_FORALL_HEAD TOK_LBRACKET bound_list TOK_RBRACKET expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_FORALL, $3, $5); }
  | TOK_EXISTS_HEAD TOK_LBRACKET bound_list TOK_RBRACKET expr %prec TOK_GLOBALLY
    { $$ = mk_reduction(NODE_EXISTS, $3, $5); }
  | TOK_SUM_HEAD TOK_LBRACKET bound_list TOK_RBRACKET expr %prec TOK_BIG_NUM
    { $$ = mk_reduction(NODE_SUM, $3, $5); }
  | TOK_PRODUCT_HEAD TOK_LBRACKET bound_list TOK_RBRACKET expr %prec TOK_BIG_NUM
    { $$ = mk_reduction(NODE_PRODUCT, $3, $5); }
  | TOK_UNION_HEAD TOK_LBRACKET bound_list TOK_RBRACKET expr %prec TOK_BIG_SET
    { $$ = mk_reduction(NODE_SET_BIG_UNION, $3, $5); }
  | TOK_INTER_HEAD TOK_LBRACKET bound_list TOK_RBRACKET expr %prec TOK_BIG_SET
    { $$ = mk_reduction(NODE_SET_BIG_INTER, $3, $5); }
  ;

set_literal
  : TOK_LBRACE TOK_RBRACE
    { if (!($$ = mk_set(spec->arena, NODE_SET, nullptr))) YYNOMEM; }
  | TOK_LBRACE nonempty_expr_list TOK_RBRACE
    { if (!($$ = mk_set(spec->arena, NODE_SET, $2))) YYNOMEM; }
  | TOK_LBRACE ltl_expr TOK_COMMA ltl_expr TOK_DOTDOT ltl_expr TOK_RBRACE
    { Node **xs = node_list_append(spec->arena, nullptr, $2);
      if (!xs) YYNOMEM;
      if (!(xs = node_list_append(spec->arena, xs, $4))) YYNOMEM;
      if (!(xs = node_list_append(spec->arena, xs, $6))) YYNOMEM;
      if (!($$ = mk_set(spec->arena, NODE_SET_ENUM, xs))) YYNOMEM; }
  ;

nonempty_expr_list
  : ltl_expr
    { if (!($$ = node_list_append(spec->arena, nullptr, $1))) YYNOMEM; }
  | nonempty_expr_list TOK_COMMA ltl_expr
    { if (!($$ = node_list_append(spec->arena, $1, $3))) YYNOMEM; }
  ;

bound_list
  : bound_spec
    { if (!($$ = node_list_append(spec->arena, nullptr, $1))) YYNOMEM; }
  | bound_list TOK_COMMA bound_spec
    { if (!($$ = node_list_append(spec->arena, $1, $3))) YYNOMEM; }
  ;

/* Quantifier bound: lo (<|<=) var (<|<=) hi.  Builds a partial quantifier
 * node (kind set later by the caller); qbody is filled in afterwards.
 * TLSF §4.7 requires numerical bounds; §4.6 guards belong to function cases. */
bound_spec
  : expr lt_or_leq[loS] TOK_IDENT[v] lt_or_leq[hiS] expr
    {
      Node *n = ARENA_ALLOC(spec->arena, Node);
      if (!n) YYNOMEM;
      n->qvar = $v;
      n->qlo = $1;
      n->qhi = $5;
      n->qlo_strict = $loS;
      n->qhi_strict = $hiS;
      $$ = n;
    }
  | TOK_IDENT[v] TOK_IN ltl_expr
    { Node *n = ARENA_ALLOC(spec->arena, Node);
      if (!n) YYNOMEM;
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
  : %empty
    { $$ = nullptr; }
  | ltl_expr
    { if (!($$ = node_list_append(spec->arena, nullptr, $1))) YYNOMEM; }
  | call_arg_list TOK_COMMA ltl_expr
    { if (!($$ = node_list_append(spec->arena, $1, $3))) YYNOMEM; }
  ;

%%

/* =========================================================================
 * Error reporting
 * ===================================================================== */

void yyerror(YYLTYPE *lloc, TlsfParseInput *input,
             TlsfSpec *spec, const char *msg) {
  (void)input;
  (void)spec;
  if (strcmp(msg, "syntax is ambiguous") == 0)
    msg = "ambiguous function case boundary or expression";
  fprintf(tlsf_diagnostic_stream(), "%d:%d: parse error: %s\n",
          lloc->first_line, lloc->first_column, msg);
}

int tlsf_parse(yyscan_t scanner, TlsfSpec *spec) {
  TlsfParseInput input = {.scanner = scanner};
  return yyparse(&input, spec);
}
