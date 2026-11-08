#include "case_boundaries.h"

#include "tlsf_parse.h"
#include "tlsf_lex.h"
#include "tlsf_boundary_parse.h"

#include <stdlib.h>
#include <string.h>

/* Both grammars declare real lexer tokens in the frozen order. The normal
 * parser's extra boundary and precedence-only tokens come afterwards. */
static_assert((int)TOK_IDENT == (int)B_TOK_IDENT);
static_assert((int)TOK_BAR == (int)B_TOK_BAR);
static_assert(sizeof(YYSTYPE) == sizeof(TLSF_BOUNDARY_STYPE));
static_assert(sizeof(YYLTYPE) == sizeof(TLSF_BOUNDARY_LTYPE));

typedef struct {
  int kind;
  YYSTYPE value;
  YYLTYPE location;
  bool boundary;
} CaseToken;

struct CaseTokens {
  CaseToken *items;
  size_t count, capacity, cursor;
  bool boundary_emitted;
};

typedef struct CaseMark {
  Node *body;
  struct CaseMark *tail, *next;
  int line, column;
} CaseMark;

typedef struct {
  CaseTokens *tokens;
  size_t begin, end, cursor;
  CaseMark *marks;
} BoundaryInput;

int tlsf_case_lex(YYSTYPE *value, YYLTYPE *location, yyscan_t scanner);
int tlsf_boundary_lex(TLSF_BOUNDARY_STYPE *value, TLSF_BOUNDARY_LTYPE *location,
                      yyscan_t scanner);

CaseTokens *case_tokens_read(void *scanner) {
  CaseTokens *tokens = calloc(1, sizeof(*tokens));
  if (!tokens)
    return nullptr;
  for (;;) {
    if (tokens->count == tokens->capacity) {
      size_t capacity = tokens->capacity ? tokens->capacity * 2 : 128;
      if (capacity < tokens->capacity ||
          capacity > SIZE_MAX / sizeof(CaseToken)) {
        case_tokens_free(tokens);
        return nullptr;
      }
      CaseToken *items = realloc(tokens->items, capacity * sizeof(*items));
      if (!items) {
        case_tokens_free(tokens);
        return nullptr;
      }
      tokens->items = items;
      tokens->capacity = capacity;
    }
    CaseToken *token = &tokens->items[tokens->count++];
    *token = (CaseToken){0};
    /* Flex leaves the location untouched at EOF (and on some failures).
     * Match Bison's reuse of the previous location between lexer calls. */
    token->location = tokens->count > 1
                          ? tokens->items[tokens->count - 2].location
                          : (YYLTYPE){1, 1, 1, 1};
    token->kind = yylex(&token->value, &token->location, scanner);
    if (!token->kind || token->kind == TOK_ERROR)
      return tokens;
  }
}

void case_tokens_free(CaseTokens *tokens) {
  if (tokens) {
    free(tokens->items);
    free(tokens);
  }
}

int tlsf_case_lex(YYSTYPE *value, YYLTYPE *location, yyscan_t scanner) {
  CaseTokens *tokens = scanner;
  if (tokens->cursor == tokens->count)
    return 0;
  const CaseToken *token = &tokens->items[tokens->cursor];
  *location = token->location;
  if (token->boundary && !tokens->boundary_emitted) {
    tokens->boundary_emitted = true;
    return TOK_CASE_BOUNDARY;
  }
  *value = token->value;
  ++tokens->cursor;
  tokens->boundary_emitted = false;
  return token->kind;
}

/* Parse each definition in the original full grammar, rather than changing
 * its start symbol or extracting expression productions: either change can
 * alter LALR state merging and hence main's conflict resolution. A finite
 * wrapper permits all supported strong temporal syntax. No names or values
 * are resolved by this pass. Original token locations remain intact. */
static const int prefix[] = {
    TOK_INFO,   TOK_LBRACE,      TOK_SEMANTICS, TOK_COLON,  TOK_FINITE_MEALY,
    TOK_TARGET, TOK_COLON,       TOK_MEALY,     TOK_RBRACE, TOK_GLOBAL,
    TOK_LBRACE, TOK_DEFINITIONS, TOK_LBRACE,
};
static const int suffix[] = {
    TOK_RBRACE, TOK_RBRACE, TOK_MAIN, TOK_LBRACE, TOK_RBRACE, 0,
};

int tlsf_boundary_lex(TLSF_BOUNDARY_STYPE *value, TLSF_BOUNDARY_LTYPE *location,
                      yyscan_t scanner) {
  BoundaryInput *input = scanner;
  size_t cursor = input->cursor++;
  size_t prefix_count = sizeof(prefix) / sizeof(*prefix);
  size_t body_count = input->end - input->begin;
  memset(value, 0, sizeof(*value));
  memcpy(location, &input->tokens->items[input->begin].location,
         sizeof(*location));
  if (cursor < prefix_count)
    return prefix[cursor];
  cursor -= prefix_count;
  if (cursor < body_count) {
    const CaseToken *token = &input->tokens->items[input->begin + cursor];
    memcpy(value, &token->value, sizeof(*value));
    memcpy(location, &token->location, sizeof(*location));
    return token->kind;
  }
  cursor -= body_count;
  return cursor < sizeof(suffix) / sizeof(*suffix) ? suffix[cursor] : 0;
}

static CaseMark *find_mark(CaseMark *marks, Node *body) {
  for (; marks; marks = marks->next)
    if (marks->body == body)
      return marks;
  return nullptr;
}

bool case_boundary_record(void *scanner, Arena *arena, Node *body, Node *tail,
                          int line, int column) {
  BoundaryInput *input = scanner;
  CaseMark *mark = ARENA_ALLOC(arena, CaseMark);
  if (!mark)
    return false;
  *mark = (CaseMark){.body = body,
                     .tail = find_mark(input->marks, tail),
                     .next = input->marks,
                     .line = line,
                     .column = column};
  input->marks = mark;
  return true;
}

static bool partition_definition(CaseTokens *tokens, size_t begin, size_t end) {
  TlsfSpec *reference = spec_new();
  if (!reference)
    return false;
  BoundaryInput input = {.tokens = tokens, .begin = begin, .end = end};
  int rc = tlsf_boundary_parse(&input, reference);
  bool ok = rc != 2 && !arena_failed(reference->arena);
  if (rc == 0 && reference->def_count == 1) {
    CaseMark *mark = find_mark(input.marks, reference->defs[0].body);
    for (; mark; mark = mark->tail)
      for (size_t i = begin; i < end; ++i) {
        CaseToken *token = &tokens->items[i];
        if (token->location.first_line == mark->line &&
            token->location.first_column == mark->column) {
          token->boundary = true;
          break;
        }
      }
  }
  spec_free(reference);
  return ok;
}

static int delimiter(int token) {
  return (token == TOK_LPAREN || token == TOK_LBRACKET ||
          token == TOK_LBRACKET_STRONG || token == TOK_LBRACE) -
         (token == TOK_RPAREN || token == TOK_RBRACKET ||
          token == TOK_RBRACKET_STRONG || token == TOK_RBRACE);
}

bool case_tokens_partition(CaseTokens *tokens) {
  for (size_t i = 0; i + 1 < tokens->count; ++i) {
    if (tokens->items[i].kind != TOK_DEFINITIONS ||
        tokens->items[i + 1].kind != TOK_LBRACE)
      continue;
    size_t begin = i + 2;
    int depth = 0;
    unsigned colons = 0;
    for (i = begin; i < tokens->count; ++i) {
      int token = tokens->items[i].kind;
      if (token == TOK_RBRACE && !depth)
        break;
      depth += delimiter(token);
      if (token == TOK_COLON && !depth)
        ++colons;
      if (token == TOK_SEMI && !depth) {
        if (colons > 1 && tokens->items[begin].kind == TOK_IDENT &&
            !partition_definition(tokens, begin, i + 1))
          return false;
        begin = i + 1;
        colons = 0;
      }
    }
  }
  return true;
}
