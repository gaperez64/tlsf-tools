#include "env_witness.h"

#include <string.h>

enum { MAX_NODES = 128 };

typedef struct {
  NodeKind kind;
  unsigned lhs, rhs, ap;
} Instruction;

typedef struct {
  Instruction nodes[MAX_NODES];
  unsigned roots[MAX_NODES];
  Role roles[MAX_NODES];
  const char *aps[ENV_WITNESS_MAX_APS];
  unsigned count, root_count, ap_count, syntax_left;
} Program;

// Postorder compilation bounds recursion and accepts only expanded LTL.
// Bounded-origin metadata is immaterial: the ordinary AST is its expansion.
static int compile_node(Program *p, const Node *n) {
  if (!n || !p->syntax_left)
    return -1;
  --p->syntax_left;
  Instruction op = {.kind = n->kind};
  int lhs = 0, rhs = 0;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
    break;
  case NODE_AP:
    if (!n->name)
      return -1;
    while (op.ap < p->ap_count && strcmp(p->aps[op.ap], n->name) != 0)
      ++op.ap;
    if (op.ap == p->ap_count) {
      if (p->ap_count == ENV_WITNESS_MAX_APS)
        return -1;
      p->aps[p->ap_count++] = n->name;
    }
    break;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    lhs = compile_node(p, n->arg);
    break;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    lhs = compile_node(p, n->lhs);
    rhs = compile_node(p, n->rhs);
    break;
  default:
    return -1;
  }
  if (lhs < 0 || rhs < 0)
    return -1;
  op.lhs = (unsigned)lhs;
  op.rhs = (unsigned)rhs;
  unsigned id = p->count++;
  p->nodes[id] = op;
  return (int)id;
}

static bool compile_environment(Program *p, const SectionPatternView *d) {
  if (!d || d->count > MAX_NODES || (d->count && !d->entries))
    return false;
  for (unsigned i = 0; i < d->count; ++i) {
    Role r = d->entries[i].role;
    if (r != TLSF_ROLE_INITIALLY && r != TLSF_ROLE_REQUIRE &&
        r != TLSF_ROLE_ASSUME)
      return false;
    int root = compile_node(p, d->entries[i].formula);
    if (root < 0)
      return false;
    p->roots[p->root_count] = (unsigned)root;
    p->roles[p->root_count++] = r;
  }
  return true;
}

// Bit j describes satisfaction at position j, including the prefix. The
// successor of the last position is loop, never an artificial finite end.
static unsigned next(unsigned values, const EnvLasso *w) {
  return (values >> 1) | (((values >> w->loop) & 1u) << (w->length - 1));
}

static bool spend(uint32_t *budget) {
  if (!*budget)
    return false;
  --*budget;
  return true;
}

static EnvWitnessResult evaluate(const Program *p, const EnvLasso *w,
                                 uint32_t *budget) {
  unsigned values[MAX_NODES] = {0};
  unsigned mask = (1u << w->length) - 1;
  for (unsigned i = 0; i < p->count; ++i) {
    if (!spend(budget))
      return ENV_WITNESS_UNKNOWN;
    Instruction op = p->nodes[i];
    unsigned a = values[op.lhs], b = values[op.rhs], v = 0;
    switch (op.kind) {
    case NODE_TRUE:
      v = mask;
      break;
    case NODE_FALSE:
      break;
    case NODE_AP:
      for (unsigned ap = 0; ap < w->ap_count; ++ap)
        if (strcmp(p->aps[op.ap], w->aps[ap]) == 0)
          for (unsigned j = 0; j < w->length; ++j)
            v |= ((unsigned)(w->letters[j] >> ap) & 1u) << j;
      break;
    case NODE_NOT:
      v = mask ^ a;
      break;
    case NODE_AND:
      v = a & b;
      break;
    case NODE_OR:
      v = a | b;
      break;
    case NODE_IMPL:
      v = (mask ^ a) | b;
      break;
    case NODE_EQUIV:
      v = mask ^ (a ^ b);
      break;
    case NODE_X:
    case NODE_X_STRONG:
      v = next(a, w);
      break;
    case NODE_F:
    case NODE_G:
    case NODE_U:
    case NODE_R:
    case NODE_W:
    case NODE_M: {
      // Least fixed points: F, U, M. Greatest fixed points: G, R, W.
      // On this finite successor graph monotone iteration terminates, and
      // equals infinite-word LTL, even for cycles without an eventuality.
      bool greatest =
          op.kind == NODE_G || op.kind == NODE_R || op.kind == NODE_W;
      bool release = op.kind == NODE_R || op.kind == NODE_M;
      if (op.kind == NODE_F) {
        b = a;
        a = mask;
      } else if (op.kind == NODE_G) {
        b = a;
        a = 0;
      }
      v = greatest ? mask : 0;
      for (;;) {
        if (!spend(budget))
          return ENV_WITNESS_UNKNOWN;
        unsigned successor = next(v, w);
        unsigned updated = release || op.kind == NODE_G ? b & (a | successor)
                                                        : b | (a & successor);
        if (updated == v)
          break;
        v = updated;
      }
      break;
    }
    default:
      return ENV_WITNESS_UNKNOWN;
    }
    values[i] = v;
  }
  for (unsigned i = 0; i < p->root_count; ++i) {
    if (!spend(budget))
      return ENV_WITNESS_UNKNOWN;
    unsigned required = p->roles[i] == TLSF_ROLE_REQUIRE ? mask : 1;
    if ((values[p->roots[i]] & required) != required)
      return ENV_WITNESS_UNKNOWN;
  }
  return ENV_WITNESS_SATISFIABLE;
}

EnvWitnessResult env_lasso_check(const SectionPatternView *dropped,
                                 const EnvLasso *word, uint32_t work_budget) {
  if (!word || !word->length || word->length > ENV_WITNESS_MAX_LENGTH ||
      word->loop >= word->length || word->ap_count > ENV_WITNESS_MAX_APS ||
      !word->letters || (word->ap_count && !word->aps))
    return ENV_WITNESS_UNKNOWN;
  for (unsigned i = 0; i < word->ap_count; ++i) {
    if (!word->aps[i])
      return ENV_WITNESS_UNKNOWN;
    for (unsigned j = 0; j < i; ++j)
      if (strcmp(word->aps[i], word->aps[j]) == 0)
        return ENV_WITNESS_UNKNOWN;
  }
  Program p = {.syntax_left = MAX_NODES};
  if (!compile_environment(&p, dropped))
    return ENV_WITNESS_UNKNOWN;
  return evaluate(&p, word, &work_budget);
}

EnvWitnessResult env_witness_search(const SectionPatternView *dropped,
                                    uint32_t work_budget) {
  Program p = {.syntax_left = MAX_NODES};
  if (!compile_environment(&p, dropped))
    return ENV_WITNESS_UNKNOWN;
  uint8_t letters[ENV_WITNESS_MAX_LENGTH];
  EnvLasso w = {.aps = p.aps, .letters = letters, .ap_count = p.ap_count};
  for (w.length = 1; w.length <= ENV_WITNESS_MAX_LENGTH; ++w.length) {
    uint64_t end = UINT64_C(1) << (p.ap_count * w.length);
    for (w.loop = 0; w.loop < w.length; ++w.loop)
      for (uint64_t bits = 0; bits < end; ++bits) {
        if (!spend(&work_budget))
          return ENV_WITNESS_UNKNOWN;
        for (unsigned j = 0; j < w.length; ++j)
          letters[j] = (uint8_t)(bits >> (p.ap_count * j));
        if (evaluate(&p, &w, &work_budget) == ENV_WITNESS_SATISFIABLE)
          return ENV_WITNESS_SATISFIABLE;
      }
  }
  return ENV_WITNESS_UNKNOWN;
}
