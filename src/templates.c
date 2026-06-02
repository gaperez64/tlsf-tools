#define _POSIX_C_SOURCE 200809L
#include "tlsf/templates.h"

#include "tlsf/print_ltlxba.h"

#include <stdlib.h>
#include <string.h>

const char *const TEMPLATE_NAMES[] = {"definition",
                                      "delayed-definition",
                                      "guarded-next-assignment",
                                      "mutex",
                                      "pure-recurrence",
                                      "round-robin",
                                      "response",
                                      "arbiter"};
const int TEMPLATE_NAMES_COUNT = 8;

// ---------------------------------------------------------------------------
// CSNF model
// ---------------------------------------------------------------------------

typedef struct {
  const char *name; // template name
  CsnfStatus status;
  const char *cert; // certificate type, or nullptr
  uint32_t *cids;   // member constraint ids
  uint32_t ncids;
  // artifacts (borrowed Node* into the cover arena; indices into cov->aps):
  int32_t dec_output; // definition decoder output (-1 none)
  const Node *dec_theta;
  int32_t nsf_output; // guarded-next assigned output (-1 none)
  const Node **nsf_guards;
  uint32_t nsf_nguards;
  int32_t *cyc_outputs; // round-robin one-hot cycle outputs
  uint32_t cyc_n;
} Block;

struct Csnf {
  ConstraintCover *cov;
  Block *blocks;
  uint32_t nblocks, bcap;
  bool *solved;  // per constraint: in a SOLVED block
  bool *claimed; // per constraint: already placed in some block
  uint32_t nconstraints;
};

static Block *new_block(Csnf *c) {
  if (c->nblocks == c->bcap) {
    uint32_t ncap = c->bcap ? c->bcap * 2 : 8;
    Block *nb = realloc(c->blocks, ncap * sizeof(Block));
    if (!nb)
      return nullptr; // OOM: caller skips this block
    c->blocks = nb;
    c->bcap = ncap;
  }
  Block *b = &c->blocks[c->nblocks++];
  *b = (Block){.dec_output = -1, .nsf_output = -1};
  return b;
}

// ---------------------------------------------------------------------------
// Syntactic helpers
// ---------------------------------------------------------------------------

static bool occurs_in(const Node *n, const char *name) {
  switch (n->kind) {
  case NODE_AP:
    return n->name == name;
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    return occurs_in(n->arg, name);
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    return occurs_in(n->lhs, name) || occurs_in(n->rhs, name);
  default:
    return false;
  }
}

// Collect the top-level conjunctive literals of a guard into pos/neg sets.
static void guard_literals(ConstraintCover *cov, const Node *n, ApSet *pos,
                           ApSet *neg) {
  if (n->kind == NODE_AND) {
    guard_literals(cov, n->lhs, pos, neg);
    guard_literals(cov, n->rhs, pos, neg);
  } else if (n->kind == NODE_AP) {
    int32_t i = ap_table_find(&cov->aps, n->name);
    if (i >= 0)
      apset_set(pos, (uint32_t)i);
  } else if (n->kind == NODE_NOT && n->arg->kind == NODE_AP) {
    int32_t i = ap_table_find(&cov->aps, n->arg->name);
    if (i >= 0)
      apset_set(neg, (uint32_t)i);
  }
}

static bool sets_intersect(const ApSet *a, const ApSet *b) {
  for (uint32_t i = 0; i < a->nbits; i++)
    if (apset_test(a, i) && apset_test(b, i))
      return true;
  return false;
}

// Parse G(alpha -> X o) / G(alpha -> X !o); returns guard, output index, sign.
static bool parse_guarded_next(ConstraintCover *cov, const Constraint *c,
                               const Node **alpha, int32_t *out, bool *neg) {
  if (c->formula->kind != NODE_G || c->formula->arg->kind != NODE_IMPL)
    return false;
  const Node *body = c->formula->arg;
  if (body->rhs->kind != NODE_X)
    return false;
  const Node *t = body->rhs->arg;
  *neg = false;
  if (t->kind == NODE_NOT) {
    *neg = true;
    t = t->arg;
  }
  if (t->kind != NODE_AP)
    return false;
  int32_t i = ap_table_find(&cov->aps, t->name);
  if (i < 0 || !(ap_table_flags(&cov->aps, (uint32_t)i) & AP_FLAG_OUTPUT))
    return false;
  *alpha = body->lhs;
  *out = i;
  return true;
}

static bool has_cand(const Constraint *c, const char *name) {
  for (uint16_t i = 0; i < c->candidate_count; i++)
    if (strcmp(c->candidates[i], name) == 0)
      return true;
  return false;
}

// ---------------------------------------------------------------------------
// Certification
// ---------------------------------------------------------------------------

static void certify_round_robin(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_ROUND_ROBIN))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t b = 0; b < cov->block_count; b++) {
    TemplateBlock *tb = &cov->blocks[b];
    if (strcmp(tb->template_name, "round_robin_candidate") != 0)
      continue;

    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "round-robin";
    blk->ncids = tb->count;
    blk->cids = malloc(tb->count * sizeof(uint32_t));
    memcpy(blk->cids, tb->constraint_ids, tb->count * sizeof(uint32_t));

    // Recurrence outputs in this block.
    int32_t *outs = malloc(tb->count * sizeof(int32_t));
    uint32_t no = 0;
    for (uint32_t k = 0; k < tb->count; k++) {
      Constraint *m = &cov->items[tb->constraint_ids[k]];
      if (m->rec_output >= 0)
        outs[no++] = m->rec_output;
    }

    // Side condition: those outputs occur in no constraint outside the block.
    bool disjoint = true;
    if (certify) {
      for (uint32_t i = 0; i < cov->count && disjoint; i++) {
        bool inblk = false;
        for (uint32_t k = 0; k < tb->count; k++)
          if (tb->constraint_ids[k] == i)
            inblk = true;
        if (inblk)
          continue;
        for (uint32_t j = 0; j < no; j++)
          if (apset_test(&cov->items[i].outputs, (uint32_t)outs[j])) {
            disjoint = false;
            break;
          }
      }
    }

    if (certify && disjoint) {
      blk->status = CSNF_SOLVED;
      blk->cert = "round_robin_scheduler";
      blk->cyc_outputs = outs;
      blk->cyc_n = no;
      for (uint32_t k = 0; k < tb->count; k++) {
        c->solved[tb->constraint_ids[k]] = true;
        c->claimed[tb->constraint_ids[k]] = true;
      }
    } else {
      blk->status = CSNF_CANDIDATE;
      blk->cyc_outputs = outs;
      blk->cyc_n = no;
      for (uint32_t k = 0; k < tb->count; k++)
        c->claimed[tb->constraint_ids[k]] = true; // mutex consumed regardless
    }
  }
}

static void certify_definition(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_DEFINITION))
    return;
  ConstraintCover *cov = c->cov;
  bool moore = semantics_is_moore(cov->spec->info.semantics);
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    if (c->claimed[i] || !has_cand(cc, "definition") || cc->def_output < 0)
      continue;
    const Node *eq = cc->formula->arg; // G(<eq>)
    const char *oname = ap_table_name(&cov->aps, (uint32_t)cc->def_output);
    const Node *theta = (eq->lhs->kind == NODE_AP && eq->lhs->name == oname)
                            ? eq->rhs
                            : eq->lhs;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "definition";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    // Sound iff Mealy, acyclic (o not in theta).
    if (certify && !moore && !occurs_in(theta, oname)) {
      blk->status = CSNF_SOLVED;
      blk->cert = "definition_decoder";
      blk->dec_output = cc->def_output;
      blk->dec_theta = theta;
      c->solved[i] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
      blk->dec_output = cc->def_output;
      blk->dec_theta = theta;
    }
    c->claimed[i] = true;
  }
}

static void certify_guarded_next(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_GUARDED_NEXT))
    return;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count;

  // Group guarded-next constraints by their assigned output.
  for (uint32_t o = 0; o < A; o++) {
    if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT))
      continue;
    // collect force-true / force-false members for output o
    uint32_t *ids = malloc(cov->count * sizeof(uint32_t));
    const Node **trues = malloc(cov->count * sizeof(Node *));
    const Node **falses = malloc(cov->count * sizeof(Node *));
    uint32_t nid = 0, nt = 0, nf = 0;
    for (uint32_t i = 0; i < cov->count; i++) {
      if (c->claimed[i] || !has_cand(&cov->items[i], "guarded-next-assignment"))
        continue;
      const Node *alpha;
      int32_t out;
      bool neg;
      if (!parse_guarded_next(cov, &cov->items[i], &alpha, &out, &neg) ||
          (uint32_t)out != o)
        continue;
      ids[nid++] = i;
      if (neg)
        falses[nf++] = alpha;
      else
        trues[nt++] = alpha;
    }
    if (nid == 0) {
      free(ids);
      free(trues);
      free(falses);
      continue;
    }

    // Exclusivity: every (true-guard, false-guard) pair shares an opposite
    // literal (sufficient for the assignment o' := OR(true-guards) to be
    // consistent).  Trivially satisfied when there are no force-false guards.
    bool exclusive = true;
    if (certify) {
      for (uint32_t a = 0; a < nt && exclusive; a++)
        for (uint32_t b = 0; b < nf && exclusive; b++) {
          ApSet ap, an, bp, bn;
          apset_init(&ap, cov->arena, A);
          apset_init(&an, cov->arena, A);
          apset_init(&bp, cov->arena, A);
          apset_init(&bn, cov->arena, A);
          guard_literals(cov, trues[a], &ap, &an);
          guard_literals(cov, falses[b], &bp, &bn);
          if (!sets_intersect(&ap, &bn) && !sets_intersect(&an, &bp))
            exclusive = false;
        }
    }

    Block *blk = new_block(c);
    if (!blk) {
      free(ids);
      free(trues);
      free(falses);
      return;
    }
    blk->name = "guarded-next-assignment";
    blk->cids = malloc(nid * sizeof(uint32_t));
    memcpy(blk->cids, ids, nid * sizeof(uint32_t));
    blk->ncids = nid;
    blk->nsf_output = (int32_t)o;
    if (certify && exclusive) {
      blk->status = CSNF_SOLVED;
      blk->cert = "guarded_assignment_consistency";
      blk->nsf_guards = malloc((nt ? nt : 1) * sizeof(Node *));
      memcpy(blk->nsf_guards, trues, nt * sizeof(Node *));
      blk->nsf_nguards = nt;
      for (uint32_t k = 0; k < nid; k++)
        c->solved[ids[k]] = true;
    } else {
      blk->status = CSNF_CANDIDATE;
    }
    for (uint32_t k = 0; k < nid; k++)
      c->claimed[ids[k]] = true;
    free(ids);
    free(trues);
    free(falses);
  }
}

static void certify_mutex(Csnf *c, unsigned want, bool certify) {
  if (want && !(want & TPL_MUTEX))
    return;
  ConstraintCover *cov = c->cov;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *cc = &cov->items[i];
    if (c->claimed[i] || !cc->has_mutex)
      continue;
    Block *blk = new_block(c);
    if (!blk)
      return;
    blk->name = "mutex";
    blk->cids = malloc(sizeof(uint32_t));
    blk->cids[0] = i;
    blk->ncids = 1;
    // A mutex is a certified safety invariant, but not solved on its own.
    blk->status = certify ? CSNF_CERTIFIED : CSNF_CANDIDATE;
    blk->cert = certify ? "mutex_safety" : nullptr;
    c->claimed[i] = true;
  }
}

Csnf *templates_certify(ConstraintCover *cov, unsigned want, bool certify) {
  Csnf *c = calloc(1, sizeof *c);
  if (!c)
    return nullptr;
  c->cov = cov;
  c->nconstraints = cov->count;
  c->solved = calloc(cov->count ? cov->count : 1, sizeof(bool));
  c->claimed = calloc(cov->count ? cov->count : 1, sizeof(bool));

  // Precedence: round-robin (claims its mutex+recurrences), then definition,
  // guarded-next, then leftover standalone mutexes.
  certify_round_robin(c, want, certify);
  certify_definition(c, want, certify);
  certify_guarded_next(c, want, certify);
  certify_mutex(c, want, certify);
  return c;
}

void csnf_free(Csnf *c) {
  if (!c)
    return;
  for (uint32_t i = 0; i < c->nblocks; i++) {
    free(c->blocks[i].cids);
    free(c->blocks[i].cyc_outputs);
    free(c->blocks[i].nsf_guards);
  }
  free(c->blocks);
  free(c->solved);
  free(c->claimed);
  free(c);
}

// ---------------------------------------------------------------------------
// Emit
// ---------------------------------------------------------------------------

static const char *status_name(CsnfStatus s) {
  return s == CSNF_SOLVED      ? "solved"
         : s == CSNF_CERTIFIED ? "certified"
                               : "candidate";
}

static char *formula_str(const Node *n) {
  char *buf = nullptr;
  size_t sz = 0;
  FILE *ms = open_memstream(&buf, &sz);
  if (!ms)
    return nullptr;
  print_ltlxba_formula(ms, n, false);
  fclose(ms);
  return buf;
}

static void count_status(const Csnf *c, uint32_t *sol, uint32_t *cert,
                         uint32_t *cand) {
  *sol = *cert = *cand = 0;
  for (uint32_t i = 0; i < c->nblocks; i++)
    switch (c->blocks[i].status) {
    case CSNF_SOLVED:
      (*sol)++;
      break;
    case CSNF_CERTIFIED:
      (*cert)++;
      break;
    case CSNF_CANDIDATE:
      (*cand)++;
      break;
    }
}

void csnf_emit_lines(FILE *out, const Csnf *c, const char *source, bool solve) {
  ConstraintCover *cov = c->cov;
  uint32_t sol, cert, cand, resid = 0;
  count_status(c, &sol, &cert, &cand);
  for (uint32_t i = 0; i < c->nconstraints; i++)
    if (!c->solved[i])
      resid++;

  fprintf(out, "c CSNF for %s\n", source);
  fprintf(out, "p csnf %u %u %u %u\n", sol, cert, cand, resid);
  fprintf(out, "m semantics %s\n",
          semantics_is_moore(cov->spec->info.semantics) ? "Moore" : "Mealy");

  for (uint32_t i = 0; i < c->nblocks; i++) {
    const Block *b = &c->blocks[i];
    fprintf(out, "b %u %s %s\n", i, status_name(b->status), b->name);
    for (uint32_t k = 0; k < b->ncids; k++)
      fprintf(out, "bc %u c%u\n", i, b->cids[k]);
    if (solve || b->status == CSNF_SOLVED) {
      if (b->dec_output >= 0 && b->dec_theta) {
        char *th = formula_str(b->dec_theta);
        fprintf(out, "dec %u %s %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->dec_output),
                th ? th : "");
        free(th);
      }
      if (b->nsf_output >= 0) {
        fprintf(out, "nsf %u %s", i,
                ap_table_name(&cov->aps, (uint32_t)b->nsf_output));
        for (uint32_t g = 0; g < b->nsf_nguards; g++) {
          char *gs = formula_str(b->nsf_guards[g]);
          fprintf(out, " %s%s", g ? "| " : "", gs ? gs : "");
          free(gs);
        }
        fprintf(out, "\n");
      }
      if (b->cyc_n > 0 && b->status == CSNF_SOLVED) {
        fprintf(out, "cyc %u %u", i, b->cyc_n);
        for (uint32_t k = 0; k < b->cyc_n; k++)
          fprintf(out, " %s",
                  ap_table_name(&cov->aps, (uint32_t)b->cyc_outputs[k]));
        fprintf(out, "\n");
      }
    }
    if (b->cert)
      fprintf(out, "cert %u %s\n", i, b->cert);
    // Claims = the member constraints' formulas.
    for (uint32_t k = 0; k < b->ncids; k++) {
      char *cl = formula_str(cov->items[b->cids[k]].formula);
      fprintf(out, "cl %u %s\n", i, cl ? cl : "");
      free(cl);
    }
  }

  // Dependent (decoded) outputs.
  for (uint32_t i = 0; i < c->nblocks; i++)
    if (c->blocks[i].status == CSNF_SOLVED && c->blocks[i].dec_output >= 0)
      fprintf(out, "do %s\n",
              ap_table_name(&cov->aps, (uint32_t)c->blocks[i].dec_output));

  // Residual (unsolved) constraints.
  for (uint32_t i = 0; i < c->nconstraints; i++)
    if (!c->solved[i])
      fprintf(out, "r c%u\n", i);
}

void csnf_emit_text(FILE *out, const Csnf *c, bool solve) {
  (void)solve;
  ConstraintCover *cov = c->cov;
  uint32_t sol, cert, cand, resid = 0;
  count_status(c, &sol, &cert, &cand);
  for (uint32_t i = 0; i < c->nconstraints; i++)
    if (!c->solved[i])
      resid++;
  fprintf(out, "blocks: %u  (solved %u, certified %u, candidate %u)\n",
          c->nblocks, sol, cert, cand);
  fprintf(out, "residual constraints: %u\n", resid);
  for (uint32_t i = 0; i < c->nblocks; i++) {
    const Block *b = &c->blocks[i];
    fprintf(out, "  [%s] %s  (%u constraint%s)%s%s\n", status_name(b->status),
            b->name, b->ncids, b->ncids == 1 ? "" : "s",
            b->cert ? "  cert=" : "", b->cert ? b->cert : "");
    if (b->dec_output >= 0 && b->status == CSNF_SOLVED) {
      char *th = formula_str(b->dec_theta);
      fprintf(out, "      decoder: %s := %s\n",
              ap_table_name(&cov->aps, (uint32_t)b->dec_output), th ? th : "");
      free(th);
    }
    if (b->cyc_n > 0 && b->status == CSNF_SOLVED) {
      fprintf(out, "      cycle:");
      for (uint32_t k = 0; k < b->cyc_n; k++)
        fprintf(out, " %s",
                ap_table_name(&cov->aps, (uint32_t)b->cyc_outputs[k]));
      fprintf(out, "\n");
    }
  }
}
