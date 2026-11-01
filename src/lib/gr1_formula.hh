// Private immutable formula values for reduction and provenance. The native
// Node view is borrowed by the DPA constructor, which copies its input.
#ifndef TLSF_GR1_FORMULA_HH
#define TLSF_GR1_FORMULA_HH
#include "yyjson_cpp.hh"
#include <algorithm>
#include <cctype>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

namespace gr1_formula {
enum class Op { tt, ff, ap, Not, And, Or, Implies, Equiv, X, F, G, U, R, W, M };
class Formula {
  struct Value;
  std::shared_ptr<const Value> value;
  explicit Formula(std::shared_ptr<const Value> v) : value(std::move(v)) {}

public:
  Formula() = default;
  static Formula make(Op op, std::vector<Formula> children = {},
                      std::string name = {});
  static Formula ap(std::string name) {
    return make(Op::ap, {}, std::move(name));
  }
  static Formula tt() { return make(Op::tt); }
  static Formula ff() { return make(Op::ff); }
  static Formula G(Formula f) { return make(Op::G, {f}); }
  static Formula X(Formula f) { return make(Op::X, {f}); }
  Op kind() const;
  bool is_tt() const { return kind() == Op::tt; }
  bool is_ff() const { return kind() == Op::ff; }
  bool is_boolean() const;
  const std::string &ap_name() const;
  const std::string &key() const;
  const Node *node() const;
  const std::vector<Formula> &children() const;
  auto begin() const { return children().begin(); }
  auto end() const { return children().end(); }
  Formula operator[](size_t i) const { return children().at(i); }
};
struct Formula::Value {
  Op op;
  std::string name, key;
  std::vector<Formula> children;
  Node node{};
  Formula binary;
};
inline Op Formula::kind() const { return value->op; }
inline const std::string &Formula::ap_name() const { return value->name; }
inline const std::string &Formula::key() const { return value->key; }
inline const Node *Formula::node() const { return &value->node; }
inline const std::vector<Formula> &Formula::children() const {
  return value->children;
}
inline bool Formula::is_boolean() const {
  return kind() <= Op::Equiv &&
         std::all_of(begin(), end(), [](Formula f) { return f.is_boolean(); });
}
inline Formula Formula::make(Op op, std::vector<Formula> children,
                             std::string name) {
  if (op == Op::Not) {
    if (children[0].is_tt())
      return ff();
    if (children[0].is_ff())
      return tt();
    if (children[0].kind() == Op::Not)
      return children[0][0];
  }
  if (op == Op::G || op == Op::F || op == Op::X) {
    if (children[0].is_tt() || children[0].is_ff())
      return children[0];
    if (op != Op::X && children[0].kind() == op)
      return children[0];
  }
  if (op == Op::And || op == Op::Or) {
    bool conjunction = op == Op::And;
    std::vector<Formula> flat;
    auto collect = [&](auto &self, Formula f) -> void {
      if (f.kind() == op)
        for (auto child : f)
          self(self, child);
      else
        flat.push_back(f);
    };
    for (auto f : children)
      collect(collect, f);
    children.clear();
    for (auto f : flat) {
      if ((conjunction && f.is_ff()) || (!conjunction && f.is_tt()))
        return f;
      if ((conjunction && f.is_tt()) || (!conjunction && f.is_ff()))
        continue;
      if (std::none_of(children.begin(), children.end(),
                       [&](Formula old) { return old.key() == f.key(); }))
        children.push_back(f);
    }
    if (children.empty())
      return conjunction ? tt() : ff();
    if (children.size() == 1)
      return children[0];
  }
  if (op == Op::W && children[0].is_ff())
    return children[1];
  if (op == Op::Equiv) {
    if (children[0].key() == children[1].key())
      return tt();
    if (children[0].is_tt())
      return children[1];
    if (children[1].is_tt())
      return children[0];
    if (children[0].is_ff())
      return make(Op::Not, {children[1]});
    if (children[1].is_ff())
      return make(Op::Not, {children[0]});
  }
  if (op == Op::Implies) {
    if (children[0].is_tt())
      return children[1];
    if (children[0].is_ff() || children[1].is_tt() ||
        children[0].key() == children[1].key())
      return tt();
    if (children[1].is_ff())
      return make(Op::Not, {children[0]});
  }
  auto v = std::make_shared<Value>();
  v->op = op;
  v->name = std::move(name);
  v->children = std::move(children);
  static const NodeKind kinds[] = {NODE_TRUE, NODE_FALSE, NODE_AP,   NODE_NOT,
                                   NODE_AND,  NODE_OR,    NODE_IMPL, NODE_EQUIV,
                                   NODE_X,    NODE_F,     NODE_G,    NODE_U,
                                   NODE_R,    NODE_W,     NODE_M};
  v->node.kind = kinds[unsigned(op)];
  v->key = std::to_string(unsigned(op)) + ":" + v->name + "(";
  for (auto f : v->children)
    v->key += f.key() + ",";
  v->key += ")";
  if (op == Op::ap)
    v->node.name = v->name.c_str();
  else if (v->children.size() == 1)
    v->node.arg = const_cast<Node *>(v->children[0].node());
  else if (v->children.size() > 1) {
    // Store a binary Node tree even for flattened Boolean values.
    Formula lhs = v->children[0];
    if (v->children.size() > 2) {
      std::vector<Formula> prefix(v->children.begin(), v->children.end() - 1);
      // Avoid flattening again while constructing the borrowed Node view.
      Formula prev = prefix[0];
      for (size_t i = 1; i < prefix.size(); ++i) {
        auto pair = std::make_shared<Value>();
        pair->op = op;
        pair->children = {prev, prefix[i]};
        pair->node.kind = kinds[unsigned(op)];
        pair->node.lhs = const_cast<Node *>(prev.node());
        pair->node.rhs = const_cast<Node *>(pair->children[1].node());
        prev = Formula(pair);
      }
      lhs = prev;
      v->binary = lhs;
    }
    v->node.lhs = const_cast<Node *>(lhs.node());
    v->node.rhs = const_cast<Node *>(v->children.back().node());
  }
  return Formula(v);
}
inline Formula from_node(const Node *n) {
  if (!n)
    throw std::runtime_error("null formula");
  switch (n->kind) {
  case NODE_TRUE:
    return Formula::tt();
  case NODE_FALSE:
    return Formula::ff();
  case NODE_AP:
    return Formula::ap(n->name);
  default:
    break;
  }
  Op op;
  switch (n->kind) {
  case NODE_NOT:
    op = Op::Not;
    break;
  case NODE_AND:
    op = Op::And;
    break;
  case NODE_OR:
    op = Op::Or;
    break;
  case NODE_IMPL:
    op = Op::Implies;
    break;
  case NODE_EQUIV:
    op = Op::Equiv;
    break;
  case NODE_X:
    op = Op::X;
    break;
  case NODE_F:
    op = Op::F;
    break;
  case NODE_G:
    op = Op::G;
    break;
  case NODE_U:
    op = Op::U;
    break;
  case NODE_R:
    op = Op::R;
    break;
  case NODE_W:
    op = Op::W;
    break;
  case NODE_M:
    op = Op::M;
    break;
  default:
    throw std::runtime_error("non-ground infinite formula");
  }
  if (op == Op::Not || op == Op::X || op == Op::F || op == Op::G)
    return Formula::make(op, {from_node(n->arg)});
  return Formula::make(op, {from_node(n->lhs), from_node(n->rhs)});
}
using Replacements = std::map<std::string, Formula>;
inline Formula relabel(Formula f, const Replacements *map) {
  if (f.kind() == Op::ap) {
    auto it = map->find(f.ap_name());
    return it == map->end() ? f : it->second;
  }
  std::vector<Formula> children;
  for (auto child : f)
    children.push_back(relabel(child, map));
  return Formula::make(f.kind(), children);
}
// Only the printer's ground infix grammar is parsed, for frontend provenance.
class Parser {
  const std::string &text;
  size_t pos = 0;
  void space() {
    while (pos < text.size() && std::isspace((unsigned char)text[pos]))
      ++pos;
  }
  bool take(const char *s) {
    space();
    size_t n = std::char_traits<char>::length(s);
    if (text.compare(pos, n, s))
      return false;
    pos += n;
    return true;
  }
  Formula primary() {
    if (take("!"))
      return Formula::make(Op::Not, {primary()});
    if (take("(")) {
      auto f = expr(0);
      if (!take(")"))
        throw std::runtime_error("formula parenthesis");
      return f;
    }
    space();
    if (pos < text.size() &&
        (text[pos] == 'G' || text[pos] == 'F' || text[pos] == 'X') &&
        (pos + 1 == text.size() ||
         !std::isalnum((unsigned char)text[pos + 1]))) {
      char c = text[pos++];
      return Formula::make(c == 'G'   ? Op::G
                           : c == 'F' ? Op::F
                                      : Op::X,
                           {primary()});
    }
    if (pos < text.size() && text[pos] == '"') {
      size_t start = pos++;
      while (pos < text.size()) {
        if (text[pos] == '\\' && pos + 1 < text.size()) {
          pos += 2;
          continue;
        }
        if (text[pos++] == '"')
          break;
      }
      auto decoded = tlsf_json::parse(text.substr(start, pos - start));
      return Formula::ap(std::string(decoded.as_string()));
    }
    size_t start = pos;
    while (pos < text.size() &&
           (std::isalnum((unsigned char)text[pos]) || text[pos] == '_' ||
            text[pos] == '@' || text[pos] == '\''))
      ++pos;
    if (start == pos)
      throw std::runtime_error("formula atom");
    auto name = text.substr(start, pos - start);
    if (name == "true" || name == "1")
      return Formula::tt();
    if (name == "false" || name == "0")
      return Formula::ff();
    return Formula::ap(name);
  }
  Formula expr(unsigned min) {
    auto lhs = primary();
    for (;;) {
      space();
      size_t saved = pos;
      Op op;
      unsigned prec;
      if (take("<->")) {
        op = Op::Equiv;
        prec = 1;
      } else if (take("->")) {
        op = Op::Implies;
        prec = 2;
      } else if (take("||") || take("|")) {
        op = Op::Or;
        prec = 3;
      } else if (take("&&") || take("&")) {
        op = Op::And;
        prec = 4;
      } else if (take("U")) {
        op = Op::U;
        prec = 5;
      } else if (take("R")) {
        op = Op::R;
        prec = 5;
      } else if (take("W")) {
        op = Op::W;
        prec = 5;
      } else if (take("M")) {
        op = Op::M;
        prec = 5;
      } else
        break;
      if (prec < min) {
        pos = saved;
        break;
      }
      lhs = Formula::make(op, {lhs, expr(prec + (op == Op::Implies ? 0 : 1))});
    }
    return lhs;
  }

public:
  explicit Parser(const std::string &s) : text(s) {}
  Formula parse() {
    auto f = expr(0);
    space();
    if (pos != text.size())
      throw std::runtime_error("trailing formula text");
    return f;
  }
};
inline Formula parse_formula(const std::string &s) { return Parser(s).parse(); }
} // namespace gr1_formula
#endif
