#ifndef TLSF_AST_INTERNAL_H
#define TLSF_AST_INTERNAL_H
#include "tlsf/ast_api.h"
#include "tlsf/spec.h"

// Takes ownership of spec only on success; retains a lowercase clone of root.
TlsfAst *tlsf_ast_take_conversion(TlsfSpec *spec, const Node *root);
#endif
