#include "tlsf/liveness_class.h"

typedef struct {
  uint32_t n_eventual;
  uint32_t n_response;
  uint32_t n_recurrence;
  uint32_t n_until;
  bool has_nested_temporal;
  bool unknown;
} LiveAcc;

static bool has_temporal(const Node *n) {
  if (!n)
    return false;
  if (node_kind_is_temporal(n->kind))
    return true;
  switch (n->kind) {
  case NODE_NOT:
    return has_temporal(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return has_temporal(n->lhs) || has_temporal(n->rhs);
  default:
    return false;
  }
}

static bool has_liveness_temporal(const Node *n) {
  if (!n)
    return false;
  switch (n->kind) {
  case NODE_F:
  case NODE_U:
  case NODE_M:
    return true;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_G:
    return has_liveness_temporal(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_R:
  case NODE_W:
    return has_liveness_temporal(n->lhs) || has_liveness_temporal(n->rhs);
  default:
    return false;
  }
}

static bool current_bool_ok(const Node *n) {
  if (!n || node_kind_is_high_level(n->kind))
    return false;
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
    return true;
  case NODE_NOT:
    return current_bool_ok(n->arg);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
    return current_bool_ok(n->lhs) && current_bool_ok(n->rhs);
  default:
    return false;
  }
}

static void mark_temporal_body(LiveAcc *acc, const Node *n) {
  if (has_temporal(n))
    acc->has_nested_temporal = true;
  else
    acc->unknown = true;
}

static bool classify_rec(const Node *n, LiveAcc *acc) {
  if (!n) {
    acc->unknown = true;
    return false;
  }

  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AP:
  case NODE_INT:
    return true;
  case NODE_NOT:
    if (has_liveness_temporal(n->arg)) {
      acc->has_nested_temporal = true;
      return false;
    }
    return true;
  case NODE_AND:
    return classify_rec(n->lhs, acc) & classify_rec(n->rhs, acc);
  case NODE_IMPL:
    // TLSF residuals often retain the shape assumptions -> guarantee.  Treat
    // the guarantee side as the liveness obligation and ignore assumptions for
    // the obligation counters.
    return classify_rec(n->rhs, acc);
  case NODE_G:
    if (n->arg->kind == NODE_F) {
      if (current_bool_ok(n->arg->arg)) {
        acc->n_recurrence++;
        return true;
      }
      mark_temporal_body(acc, n->arg->arg);
      return false;
    }
    if (n->arg->kind == NODE_IMPL && current_bool_ok(n->arg->lhs) &&
        n->arg->rhs->kind == NODE_F) {
      if (current_bool_ok(n->arg->rhs->arg)) {
        acc->n_response++;
        return true;
      }
      mark_temporal_body(acc, n->arg->rhs->arg);
      return false;
    }
    if (has_liveness_temporal(n->arg)) {
      acc->has_nested_temporal = true;
      return false;
    }
    return true;
  case NODE_F:
    if (current_bool_ok(n->arg)) {
      acc->n_eventual++;
      return true;
    }
    mark_temporal_body(acc, n->arg);
    return false;
  case NODE_U:
    if (current_bool_ok(n->lhs) && current_bool_ok(n->rhs)) {
      acc->n_until++;
      return true;
    }
    mark_temporal_body(acc, n);
    return false;
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_R:
  case NODE_W:
    if (has_liveness_temporal(n)) {
      acc->has_nested_temporal = true;
      return false;
    }
    return true;
  case NODE_OR:
  case NODE_EQUIV:
  case NODE_M:
    if (has_liveness_temporal(n)) {
      acc->has_nested_temporal = has_temporal(n);
      acc->unknown = !acc->has_nested_temporal;
      return false;
    }
    return true;
  default:
    if (node_kind_is_high_level(n->kind)) {
      acc->unknown = true;
      return false;
    }
    return true;
  }
}

LivenessSummary liveness_classify(const Node *root) {
  LiveAcc acc = {0};
  (void)classify_rec(root, &acc);

  LivenessSummary out = {
      .n_eventual = acc.n_eventual,
      .n_response = acc.n_response,
      .n_recurrence = acc.n_recurrence,
      .n_until = acc.n_until,
      .has_nested_temporal = acc.has_nested_temporal,
  };

  uint32_t classes = 0;
  classes += acc.n_eventual ? 1u : 0u;
  classes += acc.n_response ? 1u : 0u;
  classes += acc.n_recurrence ? 1u : 0u;
  classes += acc.n_until ? 1u : 0u;

  if (acc.has_nested_temporal) {
    out.kind = LIVE_NESTED_UNSUPPORTED;
  } else if (acc.unknown) {
    out.kind = LIVE_UNKNOWN;
  } else if (classes == 0) {
    out.kind = LIVE_NONE;
  } else if (classes > 1) {
    out.kind = LIVE_MIXED_BUCHI;
  } else if (acc.n_recurrence) {
    out.kind = LIVE_GF_ATOM_OR_BOOL;
  } else if (acc.n_response) {
    out.kind = LIVE_RESPONSE;
  } else if (acc.n_eventual) {
    out.kind = LIVE_EVENTUAL;
  } else {
    out.kind = LIVE_UNTIL;
  }
  return out;
}

const char *liveness_class_name(LivenessClass k) {
  switch (k) {
  case LIVE_NONE:
    return "none";
  case LIVE_GF_ATOM_OR_BOOL:
    return "gf_atom_or_bool";
  case LIVE_RESPONSE:
    return "response";
  case LIVE_EVENTUAL:
    return "eventual";
  case LIVE_UNTIL:
    return "until";
  case LIVE_MIXED_BUCHI:
    return "mixed_buchi";
  case LIVE_NESTED_UNSUPPORTED:
    return "nested_unsupported";
  case LIVE_UNKNOWN:
  default:
    return "unknown";
  }
}
