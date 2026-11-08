#ifndef TLSF_CASE_BOUNDARIES_H
#define TLSF_CASE_BOUNDARIES_H

#include "tlsf/ast.h"

typedef struct CaseTokens CaseTokens;

CaseTokens *case_tokens_read(void *scanner);
bool case_tokens_partition(CaseTokens *tokens);
void case_tokens_free(CaseTokens *tokens);

/* Called only by the frozen compatibility grammar. */
bool case_boundary_record(void *input, Arena *arena, Node *body, Node *tail,
                          int line, int column);

#endif
