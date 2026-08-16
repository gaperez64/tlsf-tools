// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L

#include "tlsf/ast_api.h"

#include "decompose_internal.h"
#include "tlsf/classify.h"
#include "tlsf/pipeline.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/residual_plan.h"
#include "tlsf/rewrite.h"

#include <stdlib.h>
#include <string.h>

struct TlsfAst {
  TlsfPipeline *pipeline;
  ResidualPlan *residual_plan;
  TlsfDecomposeResult *result;
  Node *root;
  Node **cluster_roots;
  uint32_t cluster_count;
};

static const TlsfAstNode *public_node(const Node *node) {
  return (const TlsfAstNode *)node;
}

static const Node *internal_node(const TlsfAstNode *node) {
  return (const Node *)node;
}

void tlsf_ast_free(TlsfAst *ast) {
  if (!ast)
    return;
  tlsf_decompose_result_free(ast->result);
  free(ast->cluster_roots);
  residual_plan_free(ast->residual_plan);
  tlsf_pipeline_free(ast->pipeline);
  free(ast);
}

TlsfAst *tlsf_ast_from_file_ex(FILE *fp,
                               const TlsfDecomposeOptions *decompose_options,
                               const TlsfAstOptions *ast_options) {
  if (!fp)
    return nullptr;
  TlsfAst *ast = calloc(1, sizeof *ast);
  if (!ast)
    return nullptr;
  TlsfPipelineOptions pipeline_options = {
      .split = decompose_options && decompose_options->split,
      .certify = true,
      .template_mask = TPL_ALL,
      .overwrite_semantics =
          decompose_options ? decompose_options->overwrite_semantics : nullptr,
      .overwrite_target =
          decompose_options ? decompose_options->overwrite_target : nullptr,
      .tool_name = "tlsf-ast",
  };
  ast->pipeline = tlsf_pipeline_load(fp, &pipeline_options);
  if (!ast->pipeline)
    goto fail;

  ResidualPlanOptions residual_options = {
      .skip_local_aiger = false,
      .simplify_weak = true,
  };
  TlsfPipeline *pipeline = ast->pipeline;
  ast->residual_plan =
      residual_plan_build(pipeline->spec, pipeline->cover, pipeline->csnf,
                          pipeline->composition, residual_options);
  if (!ast->residual_plan)
    goto fail;
  ast->result = tlsf_decompose_result_from_plan(
      pipeline->spec, pipeline->cover, pipeline->csnf, pipeline->composition,
      ast->residual_plan, decompose_options);
  if (!ast->result)
    goto fail;

  ClassifiedSpec *classified = classify_spec(pipeline->spec);
  if (!classified)
    goto fail;
  ast->root = build_spec_formula(pipeline->spec, classified, PRINT_ALL);
  if (!ast->root)
    goto fail;

  ast->cluster_count = ast->residual_plan->nclusters;
  if (ast->cluster_count) {
    ast->cluster_roots = calloc(ast->cluster_count, sizeof *ast->cluster_roots);
    if (!ast->cluster_roots)
      goto fail;
  }
  bool *seen =
      calloc(pipeline->cover->aps.count ? pipeline->cover->aps.count : 1,
             sizeof *seen);
  if (!seen)
    goto fail;
  for (uint32_t index = 0; index < ast->cluster_count; index++) {
    uint32_t key = ast->residual_plan->keys[index];
    bool output_free = key == pipeline->cover->aps.count;
    ast->cluster_roots[index] = residual_plan_build_cluster(
        pipeline->spec, pipeline->cover, ast->residual_plan, key,
        /*all=*/false, /*prune=*/!output_free, seen);
    if (!ast->cluster_roots[index]) {
      free(seen);
      goto fail;
    }
  }
  free(seen);

  if (ast_options && ast_options->lower_strong_release) {
    ast->root =
        apply_rewrites(pipeline->spec->arena, ast->root, RW_NO_STRONG_RELEASE);
    if (!ast->root)
      goto fail;
    for (uint32_t i = 0; i < ast->cluster_count; i++) {
      ast->cluster_roots[i] = apply_rewrites(
          pipeline->spec->arena, ast->cluster_roots[i], RW_NO_STRONG_RELEASE);
      if (!ast->cluster_roots[i])
        goto fail;
    }
  }
  return ast;

fail:
  tlsf_ast_free(ast);
  return nullptr;
}

TlsfAst *tlsf_ast_from_file(FILE *fp,
                            const TlsfDecomposeOptions *decompose_options) {
  return tlsf_ast_from_file_ex(fp, decompose_options, nullptr);
}

TlsfAst *tlsf_ast_from_string_ex(const char *text,
                                 const TlsfDecomposeOptions *decompose_options,
                                 const TlsfAstOptions *ast_options) {
  if (!text)
    return nullptr;
  FILE *fp = fmemopen((void *)text, strlen(text), "r");
  if (!fp)
    return nullptr;
  TlsfAst *ast = tlsf_ast_from_file_ex(fp, decompose_options, ast_options);
  fclose(fp);
  return ast;
}

TlsfAst *tlsf_ast_from_string(const char *text,
                              const TlsfDecomposeOptions *decompose_options) {
  return tlsf_ast_from_string_ex(text, decompose_options, nullptr);
}

const TlsfAstNode *tlsf_ast_root(const TlsfAst *ast) {
  return ast ? public_node(ast->root) : nullptr;
}

uint32_t tlsf_ast_cluster_count(const TlsfAst *ast) {
  return ast ? ast->cluster_count : 0;
}

const TlsfAstNode *tlsf_ast_cluster_root(const TlsfAst *ast, uint32_t index) {
  return ast && index < ast->cluster_count
             ? public_node(ast->cluster_roots[index])
             : nullptr;
}

const TlsfDecomposeResult *tlsf_ast_result(const TlsfAst *ast) {
  return ast ? ast->result : nullptr;
}

TlsfAstKind tlsf_ast_node_kind(const TlsfAstNode *node) {
  if (!node)
    return TLSF_AST_KIND_COUNT;
  switch (internal_node(node)->kind) {
  case NODE_TRUE:
    return TLSF_AST_TRUE;
  case NODE_FALSE:
    return TLSF_AST_FALSE;
  case NODE_AP:
    return TLSF_AST_AP;
  case NODE_NOT:
    return TLSF_AST_NOT;
  case NODE_AND:
    return TLSF_AST_AND;
  case NODE_OR:
    return TLSF_AST_OR;
  case NODE_IMPL:
    return TLSF_AST_IMPL;
  case NODE_EQUIV:
    return TLSF_AST_EQUIV;
  case NODE_X:
    return TLSF_AST_X;
  case NODE_X_STRONG:
    return TLSF_AST_X_STRONG;
  case NODE_F:
    return TLSF_AST_F;
  case NODE_G:
    return TLSF_AST_G;
  case NODE_U:
    return TLSF_AST_U;
  case NODE_R:
    return TLSF_AST_R;
  case NODE_W:
    return TLSF_AST_W;
  case NODE_M:
    return TLSF_AST_M;
  default:
    return TLSF_AST_KIND_COUNT;
  }
}

const char *tlsf_ast_node_ap_name(const TlsfAstNode *node) {
  const Node *internal = internal_node(node);
  return internal && internal->kind == NODE_AP ? internal->name : nullptr;
}

uint32_t tlsf_ast_node_child_count(const TlsfAstNode *node) {
  switch (tlsf_ast_node_kind(node)) {
  case TLSF_AST_NOT:
  case TLSF_AST_X:
  case TLSF_AST_X_STRONG:
  case TLSF_AST_F:
  case TLSF_AST_G:
    return 1;
  case TLSF_AST_AND:
  case TLSF_AST_OR:
  case TLSF_AST_IMPL:
  case TLSF_AST_EQUIV:
  case TLSF_AST_U:
  case TLSF_AST_R:
  case TLSF_AST_W:
  case TLSF_AST_M:
    return 2;
  default:
    return 0;
  }
}

const TlsfAstNode *tlsf_ast_node_child(const TlsfAstNode *node,
                                       uint32_t index) {
  const Node *internal = internal_node(node);
  uint32_t count = tlsf_ast_node_child_count(node);
  if (!internal || index >= count)
    return nullptr;
  return public_node(count == 1   ? internal->arg
                     : index == 0 ? internal->lhs
                                  : internal->rhs);
}

static void *accept_default(const TlsfAstNode *node,
                            const TlsfAstVisitor *visitor, void *ctx) {
  return visitor->visit_default ? visitor->visit_default(ctx, node) : nullptr;
}

void *tlsf_ast_accept(const TlsfAstNode *node, const TlsfAstVisitor *visitor,
                      void *ctx) {
  if (!node || !visitor)
    return nullptr;
  TlsfAstKind kind = tlsf_ast_node_kind(node);
  if (kind == TLSF_AST_KIND_COUNT)
    return nullptr;
  void *lhs = nullptr;
  void *rhs = nullptr;
  uint32_t children = tlsf_ast_node_child_count(node);
  if (children > 0) {
    lhs = tlsf_ast_accept(tlsf_ast_node_child(node, 0), visitor, ctx);
    if (!lhs)
      return nullptr;
  }
  if (children > 1) {
    rhs = tlsf_ast_accept(tlsf_ast_node_child(node, 1), visitor, ctx);
    if (!rhs)
      return nullptr;
  }

#define CALL_LEAF(slot)                                                        \
  return visitor->slot ? visitor->slot(ctx) : accept_default(node, visitor, ctx)
#define CALL_UNARY(slot)                                                       \
  return visitor->slot ? visitor->slot(ctx, lhs)                               \
                       : accept_default(node, visitor, ctx)
#define CALL_BINARY(slot)                                                      \
  return visitor->slot ? visitor->slot(ctx, lhs, rhs)                          \
                       : accept_default(node, visitor, ctx)
  switch (kind) {
  case TLSF_AST_TRUE:
    CALL_LEAF(visit_true);
  case TLSF_AST_FALSE:
    CALL_LEAF(visit_false);
  case TLSF_AST_AP:
    return visitor->visit_ap
               ? visitor->visit_ap(ctx, tlsf_ast_node_ap_name(node))
               : accept_default(node, visitor, ctx);
  case TLSF_AST_NOT:
    CALL_UNARY(visit_not);
  case TLSF_AST_X:
    CALL_UNARY(visit_x);
  case TLSF_AST_X_STRONG:
    CALL_UNARY(visit_x_strong);
  case TLSF_AST_F:
    CALL_UNARY(visit_f);
  case TLSF_AST_G:
    CALL_UNARY(visit_g);
  case TLSF_AST_AND:
    CALL_BINARY(visit_and);
  case TLSF_AST_OR:
    CALL_BINARY(visit_or);
  case TLSF_AST_IMPL:
    CALL_BINARY(visit_impl);
  case TLSF_AST_EQUIV:
    CALL_BINARY(visit_equiv);
  case TLSF_AST_U:
    CALL_BINARY(visit_u);
  case TLSF_AST_R:
    CALL_BINARY(visit_r);
  case TLSF_AST_W:
    CALL_BINARY(visit_w);
  case TLSF_AST_M:
    CALL_BINARY(visit_m);
  case TLSF_AST_KIND_COUNT:
    return nullptr;
  }
#undef CALL_LEAF
#undef CALL_UNARY
#undef CALL_BINARY
  return nullptr;
}
