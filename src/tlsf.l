%top{
/* Emitted at the very top of the generated lexer, before any system header,
 * so that POSIX declarations (e.g. fileno(3), used by flex) are visible even
 * under a strict -std=c23 compile. */
#define _POSIX_C_SOURCE 200809L
}

%{
/* tlsf.l — TLSF v1.1/v1.2 lexer */
#include "tlsf/ast.h"
#include "tlsf/spec.h"
#include "tlsf_parse.h"

#include <stdlib.h>
#include <string.h>

/* Location tracking */
#define YY_USER_ACTION                                                         \
  yylloc->first_line   = yylloc->last_line   = yylineno;                       \
  yylloc->first_column = yylloc->last_column = yycolumn;                       \
  yycolumn += (int)yyleng;

static int comment_depth = 0;
%}

%option reentrant bison-bridge bison-locations
%option noyywrap nounput noinput
%option yylineno
%option extra-type="TlsfSpec *"

%x BLOCK_COMMENT

ALPHA       [a-zA-Z_]
ALNUM       [a-zA-Z0-9_]
DIGIT       [0-9]
INT         {DIGIT}+
IDENT       {ALPHA}{ALNUM}*
WS          [ \t\r\n]+
STRLIT      \"([^\"\\]|\\.)*\"

%%

{WS}                { /* skip */ }
"//"[^\n]*          { /* line comment */ }

"/*"                { comment_depth = 1; BEGIN(BLOCK_COMMENT); }
<BLOCK_COMMENT>"/*" { comment_depth++; }
<BLOCK_COMMENT>"*/" {
                      if (--comment_depth == 0)
                        BEGIN(INITIAL);
                    }
<BLOCK_COMMENT>\n   { /* track newlines */ }
<BLOCK_COMMENT>.    { /* skip */ }

  /* --- Section / subsection keywords --- */
"INFO"              { return TOK_INFO; }
"GLOBAL"            { return TOK_GLOBAL; }
"MAIN"              { return TOK_MAIN; }
"TITLE"             { return TOK_TITLE; }
"DESCRIPTION"       { return TOK_DESCRIPTION; }
"SEMANTICS"         { return TOK_SEMANTICS; }
"TARGET"            { return TOK_TARGET; }
"TAGS"              { return TOK_TAGS; }
"PARAMETERS"        { return TOK_PARAMETERS; }
"DEFINITIONS"       { return TOK_DEFINITIONS; }
"INPUTS"            { return TOK_INPUTS; }
"OUTPUTS"           { return TOK_OUTPUTS; }
"INITIALLY"         { return TOK_INITIALLY; }
"PRESET"            { return TOK_PRESET; }
"REQUIRE"           { return TOK_REQUIRE; }
"ASSERT"            { return TOK_ASSERT; }
"ASSUME"            { return TOK_ASSUME; }
"GUARANTEE"         { return TOK_GUARANTEE; }
"ASSUMPTIONS"       { return TOK_ASSUME; }
"GUARANTEES"        { return TOK_GUARANTEE; }
"INVARIANTS"        { return TOK_ASSERT; }

  /* --- Semantics / target: must come before IDENT rule --- */
  /* Multi-word values first (longest match wins, but be explicit). Named
     definitions cannot be interpolated inside quoted strings, so use
     unquoted regex with explicit whitespace classes around the comma. */
Strict[ \t]*,[ \t]*Mealy   { return TOK_STRICT_MEALY; }
Strict[ \t]*,[ \t]*Moore   { return TOK_STRICT_MOORE; }
Finite[ \t]*,[ \t]*Mealy   { return TOK_FINITE_MEALY; }
Finite[ \t]*,[ \t]*Moore   { return TOK_FINITE_MOORE; }
"Mealy"             { return TOK_MEALY; }
"Moore"             { return TOK_MOORE; }

  /* --- Boolean / LTL atoms --- */
"true"              { return TOK_TRUE; }
"false"             { return TOK_FALSE; }

  /* --- Keyword operators --- */
"SIZEOF"            { return TOK_SIZEOF; }

  /* --- LTL operators (single-char temporal first to avoid prefix match) ---
     X[!] must be matched before X. */
"X""[!]"            { return TOK_SNEXT; }
"X"                 { return TOK_NEXT; }
"F"                 { return TOK_FINALLY; }
"G"                 { return TOK_GLOBALLY; }
"U"                 { return TOK_UNTIL; }
"R"                 { return TOK_RELEASE; }
"W"                 { return TOK_WEAK; }
"M"                 { return TOK_STRONG_REL; }

  /* --- Boolean operators --- */
"!"                 { return TOK_NOT; }
"&&"                { return TOK_AND; }
"||"                { return TOK_OR; }
"->"                { return TOK_IMPL; }
"<->"               { return TOK_EQUIV; }

  /* --- Integer / comparison operators --- */
"+"                 { return TOK_PLUS; }
"-"                 { return TOK_MINUS; }
"*"                 { return TOK_STAR; }
"/"                 { return TOK_SLASH; }
"%"                 { return TOK_PERCENT; }
"=="                { return TOK_EQ; }
"!="                { return TOK_NEQ; }
"<="                { return TOK_LEQ; }
">="                { return TOK_GEQ; }
"<"                 { return TOK_LT; }
">"                 { return TOK_GT; }

  /* --- Punctuation --- */
"{"                 { return TOK_LBRACE; }
"}"                 { return TOK_RBRACE; }
"("                 { return TOK_LPAREN; }
")"                 { return TOK_RPAREN; }
"["                 { return TOK_LBRACKET; }
"]"                 { return TOK_RBRACKET; }
","                 { return TOK_COMMA; }
";"                 { return TOK_SEMI; }
":"                 { return TOK_COLON; }
"="                 { return TOK_ASSIGN; }
".."                { return TOK_DOTDOT; }

  /* --- Integer literals --- */
{INT}               {
                      yylval->ival = strtoll(yytext, NULL, 10);
                      return TOK_INTEGER;
                    }

  /* --- String literals (INFO field values) --- */
{STRLIT}            {
                      yylval->sval = intern_n(
                          yyextra->intern,
                          yytext + 1,
                          (size_t)(yyleng - 2));
                      return TOK_STRING;
                    }

  /* --- Identifiers (must come after all keyword rules) --- */
{IDENT}             {
                      yylval->sval = intern(yyextra->intern, yytext);
                      return TOK_IDENT;
                    }

  /* --- Error catch-all --- */
.                   {
                      fprintf(stderr, "%d:%d: unexpected character '%c'\n",
                              yylineno, yycolumn, yytext[0]);
                      return TOK_ERROR;
                    }

%%
