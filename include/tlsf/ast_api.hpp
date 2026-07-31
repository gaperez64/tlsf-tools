#ifndef TLSF_AST_API_HPP
#define TLSF_AST_API_HPP

#include "tlsf/ast_api.h"
#include "tlsf/decompose.hpp"

#include <cstddef>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace tlsf::ast {

enum class Kind {
  True = TLSF_AST_TRUE,
  False = TLSF_AST_FALSE,
  Ap = TLSF_AST_AP,
  Not = TLSF_AST_NOT,
  And = TLSF_AST_AND,
  Or = TLSF_AST_OR,
  Implies = TLSF_AST_IMPL,
  Equiv = TLSF_AST_EQUIV,
  X = TLSF_AST_X,
  StrongX = TLSF_AST_X_STRONG,
  F = TLSF_AST_F,
  G = TLSF_AST_G,
  U = TLSF_AST_U,
  R = TLSF_AST_R,
  W = TLSF_AST_W,
  M = TLSF_AST_M,
};

class Tree {
public:
  Tree() = default;

  [[nodiscard]] explicit operator bool() const noexcept {
    return node_ != nullptr;
  }

  [[nodiscard]] Kind kind() const {
    require_node();
    TlsfAstKind value = tlsf_ast_node_kind(node_);
    if (value == TLSF_AST_KIND_COUNT)
      throw std::logic_error("invalid TLSF AST node kind");
    return static_cast<Kind>(value);
  }

  [[nodiscard]] std::string name() const {
    require_node();
    const char *value = tlsf_ast_node_ap_name(node_);
    if (!value)
      throw std::logic_error("TLSF AST node is not an atomic proposition");
    return value;
  }

  [[nodiscard]] std::size_t size() const {
    require_node();
    return tlsf_ast_node_child_count(node_);
  }

  [[nodiscard]] Tree operator[](std::size_t index) const {
    require_node();
    const TlsfAstNode *child =
        tlsf_ast_node_child(node_, static_cast<uint32_t>(index));
    if (!child)
      throw std::out_of_range("TLSF AST child index out of range");
    return Tree(child);
  }

  [[nodiscard]] const TlsfAstNode *native_handle() const noexcept {
    return node_;
  }

private:
  friend class Ast;
  explicit Tree(const TlsfAstNode *node) : node_(node) {}

  void require_node() const {
    if (!node_)
      throw std::logic_error("empty TLSF AST tree");
  }

  const TlsfAstNode *node_ = nullptr;
};

template <class T> class Visitor {
public:
  virtual ~Visitor() = default;

  [[nodiscard]] T visit(Tree tree) {
    switch (tree.kind()) {
    case Kind::True:
      return visitTrue();
    case Kind::False:
      return visitFalse();
    case Kind::Ap:
      return visitAp(tree.name());
    case Kind::Not:
      return visitNot(visit(tree[0]));
    case Kind::X:
      return visitX(visit(tree[0]));
    case Kind::StrongX:
      return visitStrongX(visit(tree[0]));
    case Kind::F:
      return visitF(visit(tree[0]));
    case Kind::G:
      return visitG(visit(tree[0]));
    case Kind::And:
      return visitAnd(visit(tree[0]), visit(tree[1]));
    case Kind::Or:
      return visitOr(visit(tree[0]), visit(tree[1]));
    case Kind::Implies:
      return visitImplies(visit(tree[0]), visit(tree[1]));
    case Kind::Equiv:
      return visitEquiv(visit(tree[0]), visit(tree[1]));
    case Kind::U:
      return visitU(visit(tree[0]), visit(tree[1]));
    case Kind::R:
      return visitR(visit(tree[0]), visit(tree[1]));
    case Kind::W:
      return visitW(visit(tree[0]), visit(tree[1]));
    case Kind::M:
      return visitM(visit(tree[0]), visit(tree[1]));
    }
    throw std::logic_error("invalid TLSF AST node kind");
  }

protected:
  [[nodiscard]] virtual T defaultResult() { return T{}; }
  [[nodiscard]] virtual T visitTrue() { return defaultResult(); }
  [[nodiscard]] virtual T visitFalse() { return defaultResult(); }
  [[nodiscard]] virtual T visitAp(const std::string &) {
    return defaultResult();
  }
  [[nodiscard]] virtual T visitNot(T) { return defaultResult(); }
  [[nodiscard]] virtual T visitX(T) { return defaultResult(); }
  [[nodiscard]] virtual T visitStrongX(T) { return defaultResult(); }
  [[nodiscard]] virtual T visitF(T) { return defaultResult(); }
  [[nodiscard]] virtual T visitG(T) { return defaultResult(); }
  [[nodiscard]] virtual T visitAnd(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitOr(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitImplies(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitEquiv(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitU(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitR(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitW(T, T) { return defaultResult(); }
  [[nodiscard]] virtual T visitM(T, T) { return defaultResult(); }
};

struct AstOptions {
  bool lower_strong_release = false;
};

class Ast {
public:
  explicit Ast(const std::string &spec, const tlsf::Options &options = {},
               const AstOptions &ast_options = {}) {
    TlsfDecomposeOptions c_options = {};
    c_options.split = options.split;
    c_options.lowercase = options.lowercase;
    c_options.format = static_cast<TlsfDecomposeFormat>(options.format);
    c_options.overwrite_semantics = options.overwrite_semantics.empty()
                                        ? nullptr
                                        : options.overwrite_semantics.c_str();
    c_options.overwrite_target = options.overwrite_target.empty()
                                     ? nullptr
                                     : options.overwrite_target.c_str();
    TlsfAstOptions c_ast_options = {};
    c_ast_options.lower_strong_release = ast_options.lower_strong_release;
    owner_.reset(
        tlsf_ast_from_string_ex(spec.c_str(), &c_options, &c_ast_options));
    if (!owner_)
      throw std::runtime_error("TLSF AST construction failed");
  }

  Ast(Ast &&) noexcept = default;
  Ast &operator=(Ast &&) noexcept = default;
  Ast(const Ast &) = delete;
  Ast &operator=(const Ast &) = delete;

  [[nodiscard]] Tree root() const { return Tree(tlsf_ast_root(owner_.get())); }

  [[nodiscard]] std::vector<Tree> clusters() const {
    std::vector<Tree> values;
    uint32_t count = tlsf_ast_cluster_count(owner_.get());
    values.reserve(count);
    for (uint32_t i = 0; i < count; ++i)
      values.emplace_back(Tree(tlsf_ast_cluster_root(owner_.get(), i)));
    return values;
  }

  [[nodiscard]] std::vector<std::string> inputs() const {
    const TlsfDecomposeResult *value = raw_result();
    return tlsf::detail::copy_strings(value->inputs, value->n_inputs);
  }

  [[nodiscard]] std::vector<std::string> outputs() const {
    const TlsfDecomposeResult *value = raw_result();
    return tlsf::detail::copy_strings(value->outputs, value->n_outputs);
  }

  [[nodiscard]] tlsf::Result result() const {
    const TlsfDecomposeResult *raw = raw_result();
    tlsf::Result value;
    value.preprocessed_ltl = raw->preprocessed_ltl ? raw->preprocessed_ltl : "";
    value.inputs = tlsf::detail::copy_strings(raw->inputs, raw->n_inputs);
    value.outputs = tlsf::detail::copy_strings(raw->outputs, raw->n_outputs);
    value.semantics = raw->semantics ? raw->semantics : "";
    value.target = raw->target ? raw->target : "";
    value.gr_level = raw->gr_level;
    value.verdict = static_cast<tlsf::Verdict>(raw->verdict);
    value.verdict_trust = static_cast<tlsf::Trust>(raw->verdict_trust);
    value.residual_trust = static_cast<tlsf::Trust>(raw->residual_trust);
    value.clusters.reserve(raw->n_clusters);
    for (uint32_t i = 0; i < raw->n_clusters; ++i) {
      const TlsfDecomposeCluster &source = raw->clusters[i];
      tlsf::Cluster cluster;
      cluster.ltl = source.ltl ? source.ltl : "";
      cluster.inputs =
          tlsf::detail::copy_strings(source.inputs, source.n_inputs);
      cluster.outputs =
          tlsf::detail::copy_strings(source.outputs, source.n_outputs);
      value.clusters.push_back(std::move(cluster));
    }
    return value;
  }

  [[nodiscard]] const TlsfDecomposeResult *raw_result() const {
    return tlsf_ast_result(owner_.get());
  }

private:
  struct Deleter {
    void operator()(TlsfAst *value) const { tlsf_ast_free(value); }
  };
  std::unique_ptr<TlsfAst, Deleter> owner_;
};

} // namespace tlsf::ast

#endif // TLSF_AST_API_HPP
