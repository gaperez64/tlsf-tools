#ifndef TLSF_AST_API_H
#define TLSF_AST_API_H

/// Public, implementation-independent view of an expanded TLSF formula AST.
/// Nodes are borrowed from a TlsfAst owner and remain valid until that owner
/// is freed.  No internal parser or arena layout is exposed.

#include "tlsf/decompose.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct TlsfAst TlsfAst;
typedef struct TlsfAstNode TlsfAstNode;

typedef enum TlsfAstKind {
  TLSF_AST_TRUE,
  TLSF_AST_FALSE,
  TLSF_AST_AP,
  TLSF_AST_NOT,
  TLSF_AST_AND,
  TLSF_AST_OR,
  TLSF_AST_IMPL,
  TLSF_AST_EQUIV,
  TLSF_AST_X,
  TLSF_AST_X_STRONG,
  TLSF_AST_F,
  TLSF_AST_G,
  TLSF_AST_U,
  TLSF_AST_R,
  TLSF_AST_W,
  TLSF_AST_M,
  TLSF_AST_KIND_COUNT,
} TlsfAstKind;

typedef struct TlsfAstOptions {
  bool lower_strong_release;
} TlsfAstOptions;

/// Parse, expand, classify, and decompose a specification.  These convenience
/// entry points preserve the existing decomposition options and retain M.
[[nodiscard]] TlsfAst *
tlsf_ast_from_file(FILE *fp, const TlsfDecomposeOptions *decompose_options);
[[nodiscard]] TlsfAst *
tlsf_ast_from_string(const char *text,
                     const TlsfDecomposeOptions *decompose_options);

/// Extended constructors for consumers that want M lowered to U/AND.
[[nodiscard]] TlsfAst *
tlsf_ast_from_file_ex(FILE *fp, const TlsfDecomposeOptions *decompose_options,
                      const TlsfAstOptions *ast_options);
[[nodiscard]] TlsfAst *
tlsf_ast_from_string_ex(const char *text,
                        const TlsfDecomposeOptions *decompose_options,
                        const TlsfAstOptions *ast_options);

void tlsf_ast_free(TlsfAst *ast);

[[nodiscard]] const TlsfAstNode *tlsf_ast_root(const TlsfAst *ast);
[[nodiscard]] uint32_t tlsf_ast_cluster_count(const TlsfAst *ast);
[[nodiscard]] const TlsfAstNode *tlsf_ast_cluster_root(const TlsfAst *ast,
                                                       uint32_t index);
[[nodiscard]] const TlsfDecomposeResult *tlsf_ast_result(const TlsfAst *ast);

[[nodiscard]] TlsfAstKind tlsf_ast_node_kind(const TlsfAstNode *node);
[[nodiscard]] const char *tlsf_ast_node_ap_name(const TlsfAstNode *node);
[[nodiscard]] uint32_t tlsf_ast_node_child_count(const TlsfAstNode *node);
[[nodiscard]] const TlsfAstNode *tlsf_ast_node_child(const TlsfAstNode *node,
                                                     uint32_t index);

typedef struct TlsfAstVisitor {
  void *(*visit_true)(void *ctx);
  void *(*visit_false)(void *ctx);
  void *(*visit_ap)(void *ctx, const char *name);
  void *(*visit_not)(void *ctx, void *arg);
  void *(*visit_x)(void *ctx, void *arg);
  void *(*visit_x_strong)(void *ctx, void *arg);
  void *(*visit_f)(void *ctx, void *arg);
  void *(*visit_g)(void *ctx, void *arg);
  void *(*visit_and)(void *ctx, void *lhs, void *rhs);
  void *(*visit_or)(void *ctx, void *lhs, void *rhs);
  void *(*visit_impl)(void *ctx, void *lhs, void *rhs);
  void *(*visit_equiv)(void *ctx, void *lhs, void *rhs);
  void *(*visit_u)(void *ctx, void *lhs, void *rhs);
  void *(*visit_r)(void *ctx, void *lhs, void *rhs);
  void *(*visit_w)(void *ctx, void *lhs, void *rhs);
  void *(*visit_m)(void *ctx, void *lhs, void *rhs);
  void *(*visit_default)(void *ctx, const TlsfAstNode *node);
} TlsfAstVisitor;

/// Visit children first, then dispatch the node callback.  A null callback
/// uses visit_default.  Any null result aborts the walk and propagates null.
[[nodiscard]] void *tlsf_ast_accept(const TlsfAstNode *node,
                                    const TlsfAstVisitor *visitor, void *ctx);

#ifdef __cplusplus
}
#endif

#endif // TLSF_AST_API_H
