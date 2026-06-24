// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/templates.h"

#include "tlsf/aiger.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/rewrite.h"
#include "tlsf/templates_internal.h"

#include <stdlib.h>
#include <string.h>

const char *const TEMPLATE_NAMES[] = {"definition",
                                      "delayed-definition",
                                      "guarded-next-assignment",
                                      "set-reset-register",
                                      "toggle-register",
                                      "fixed-delay-response",
                                      "global-recurrence-switch",
                                      "reaction",
                                      "mutex",
                                      "pure-recurrence",
                                      "round-robin",
                                      "response",
                                      "arbiter",
                                      "persistence",
                                      "reachability",
                                      "safety-invariant"};
const int TEMPLATE_NAMES_COUNT = 16;

// ---------------------------------------------------------------------------
// Syntactic helpers
// ---------------------------------------------------------------------------

bool occurs_in(const Node *n, const char *name) {
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

static const Node *copy_subst_meta(Arena *a, const Node *src, Node *dst,
                                   const char *name, const Node *value) {
  if (dst) {
    node_copy_bounded(dst, src);
    if (src->bounded.origin != BOUNDED_NONE && src->bounded.body)
      dst->bounded.body =
          src->bounded.body == src
              ? dst
              : (Node *)node_subst(a, src->bounded.body, name, value);
  }
  return dst;
}

const Node *node_subst(Arena *a, const Node *n, const char *name,
                       const Node *value) {
#define SUB_META(expr) copy_subst_meta(a, n, (expr), name, value)

  switch (n->kind) {
  case NODE_AP:
    return strcmp(n->name, name) == 0 ? value : n;
  case NODE_NOT:
    return SUB_META(node_not(a, (Node *)node_subst(a, n->arg, name, value)));
  case NODE_X:
    return SUB_META(node_x(a, (Node *)node_subst(a, n->arg, name, value)));
  case NODE_X_STRONG:
    return SUB_META(
        node_x_strong(a, (Node *)node_subst(a, n->arg, name, value)));
  case NODE_F:
    return SUB_META(node_f(a, (Node *)node_subst(a, n->arg, name, value)));
  case NODE_G:
    return SUB_META(node_g(a, (Node *)node_subst(a, n->arg, name, value)));
  case NODE_AND:
    return SUB_META(node_and(a, (Node *)node_subst(a, n->lhs, name, value),
                             (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_OR:
    return SUB_META(node_or(a, (Node *)node_subst(a, n->lhs, name, value),
                            (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_IMPL:
    return SUB_META(node_impl(a, (Node *)node_subst(a, n->lhs, name, value),
                              (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_EQUIV:
    return SUB_META(node_equiv(a, (Node *)node_subst(a, n->lhs, name, value),
                               (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_U:
    return SUB_META(node_u(a, (Node *)node_subst(a, n->lhs, name, value),
                           (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_R:
    return SUB_META(node_r(a, (Node *)node_subst(a, n->lhs, name, value),
                           (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_W:
    return SUB_META(node_w(a, (Node *)node_subst(a, n->lhs, name, value),
                           (Node *)node_subst(a, n->rhs, name, value)));
  case NODE_M:
    return SUB_META(node_m(a, (Node *)node_subst(a, n->lhs, name, value),
                           (Node *)node_subst(a, n->rhs, name, value)));
  default:
    return n;
  }

#undef SUB_META
}

// ---------------------------------------------------------------------------
// Certification dispatch
// ---------------------------------------------------------------------------

Csnf *templates_certify(ConstraintCover *cov, unsigned want, bool certify) {
  Csnf *c = calloc(1, sizeof *c);
  if (!c)
    return nullptr;
  c->cov = cov;
  c->nconstraints = cov->count;
  c->solved = calloc(cov->count ? cov->count : 1, sizeof(bool));
  c->claimed = calloc(cov->count ? cov->count : 1, sizeof(bool));

  // Precedence: block recognizers over a shared mutex first (round-robin then
  // arbiter, each claiming its mutex+members), then the single-constraint
  // certifiers from most to least specific, then leftover standalone mutexes.
  certify_round_robin(c, want, certify);
  certify_arbiter(c, want, certify);
  certify_definition(c, want, certify);
  certify_delayed_definition(c, want, certify);
  certify_set_reset_register(c, want, certify);
  certify_toggle_register(c, want, certify);
  certify_fixed_delay_response(c, want, certify);
  certify_global_recurrence_switch(c, want, certify);
  certify_guarded_next(c, want, certify);
  certify_reaction(c, want, certify);
  certify_response(c, want, certify);
  certify_persistence(c, want, certify);
  certify_reachability(c, want, certify);
  certify_mutex(c, want, certify);
  // Generic stateless safety invariant: least specific, so it only grabs
  // propositional leftovers no named template (incl. mutex) claimed.
  certify_invariant(c, want, certify);
  return c;
}

void csnf_free(Csnf *c) {
  if (!c)
    return;
  for (uint32_t i = 0; i < c->nblocks; i++) {
    free(c->blocks[i].cids);
    free(c->blocks[i].cyc_outputs);
    free(c->blocks[i].nsf_guards);
    free(c->blocks[i].sr_set_guards);
    free(c->blocks[i].sr_reset_guards);
    free(c->blocks[i].tog_guards);
    free(c->blocks[i].fdelay_guards);
    free(c->blocks[i].fdelay_steps);
    free(c->blocks[i].arb_outputs);
    free(c->blocks[i].asg_guards);
    free(c->blocks[i].inv_outputs);
    free(c->blocks[i].inv_values);
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

static char *formula_str(const Csnf *c, const Node *n) {
  char *buf = nullptr;
  size_t sz = 0;
  FILE *ms = open_memstream(&buf, &sz);
  if (!ms)
    return nullptr;
  print_ltl(ms, n, LTL_FMT_LTLXBA, false,
            semantics_is_finite(c->cov->spec->info.semantics),
            /*lower_atoms=*/false);
  fclose(ms);
  if (sz && buf[sz - 1] == '\n')
    buf[sz - 1] = '\0';
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

void csnf_counts(const Csnf *c, uint32_t *solved, uint32_t *certified,
                 uint32_t *candidate, uint32_t *residual, uint32_t *dependent) {
  uint32_t sol, ce, ca;
  count_status(c, &sol, &ce, &ca);
  if (solved)
    *solved = sol;
  if (certified)
    *certified = ce;
  if (candidate)
    *candidate = ca;
  if (residual) {
    uint32_t r = 0;
    for (uint32_t i = 0; i < c->nconstraints; i++)
      if (!c->solved[i])
        r++;
    *residual = r;
  }
  if (dependent) {
    uint32_t d = 0;
    for (uint32_t i = 0; i < c->nblocks; i++)
      if (c->blocks[i].status == CSNF_SOLVED && c->blocks[i].dec_output >= 0)
        d++;
    *dependent = d;
  }
}

// ---------------------------------------------------------------------------
// Composition
// ---------------------------------------------------------------------------

// Does SOLVED block `b` drive output AP index `o`?
static bool block_writes(const Block *b, int32_t o) {
  if (o < 0)
    return false;
  if (b->dec_output == o || b->nsf_output == o || b->sr_output == o ||
      b->tog_output == o || b->fdelay_output == o || b->asg_output == o ||
      b->db_output == o || b->reg_output == o || b->one_output == o ||
      b->hold_output == o || b->resp_output == o)
    return true;
  for (uint32_t i = 0; i < b->cyc_n; i++)
    if (b->cyc_outputs[i] == o)
      return true;
  for (uint32_t i = 0; i < b->arb_n; i++)
    if (b->arb_outputs[i] == o)
      return true;
  return false;
}

// If SOLVED block `b` assigns output `o` a *combinational* value (a function of
// the current step), return that value node; else nullptr.  These outputs can
// be eliminated from the residual by substitution.  Registers (guarded-next,
// set-reset, toggle, fixed-delay, delayed-definition) and servers
// (response/round-robin/arbiter) are not.
static const Node *block_comb_value(const Csnf *c, const Block *b, int32_t o) {
  Arena *a = c->cov->arena;
  if (b->dec_output == o && b->dec_theta)
    return b->dec_theta; // definition o := theta
  if (b->one_output == o || b->hold_output == o)
    return node_true(a); // reachability / persistence o := true
  if (b->asg_output == o) {
    if (b->asg_nguards == 0)
      return node_false(a);
    Node *acc = (Node *)b->asg_guards[0];
    for (uint32_t g = 1; g < b->asg_nguards; g++)
      acc = node_or(a, acc, (Node *)b->asg_guards[g]);
    return acc; // reaction o := OR(true-guards)
  }
  for (uint32_t k = 0; k < b->inv_n; k++)
    if (b->inv_outputs[k] == o)
      return b->inv_values[k]; // safety-invariant Skolem
  return nullptr;
}

// True if combinational decoder block `b`'s defining formula reads output `p`.
static bool decoder_reads(const Csnf *c, const Block *b, uint32_t p) {
  const char *name = ap_table_name(&c->cov->aps, p);
  if (b->dec_output >= 0 && b->dec_theta)
    return occurs_in(b->dec_theta, name);
  if (b->asg_output >= 0)
    for (uint32_t g = 0; g < b->asg_nguards; g++)
      if (occurs_in(b->asg_guards[g], name))
        return true;
  return false;
}

// DFS over the combinational-decoder dependency graph (definition + reaction);
// returns a block on a cycle to eject, or -1 if acyclic.  Next-state decoders
// (guarded-next, set-reset, toggle, fixed-delay, delayed-definition) are
// registers and never close a combinational cycle, so they are excluded.
static int32_t comb_owner(const Csnf *c, const bool *accepted, uint32_t o) {
  for (uint32_t b = 0; b < c->nblocks; b++) {
    if (!accepted[b])
      continue;
    const Block *bl = &c->blocks[b];
    if ((bl->dec_output == (int32_t)o && bl->dec_theta) ||
        bl->asg_output == (int32_t)o)
      return (int32_t)b;
  }
  return -1;
}

static bool cycle_dfs(const Csnf *c, const bool *accepted, uint32_t o,
                      uint8_t *color, int32_t *hit) {
  color[o] = 1; // gray
  int32_t b = comb_owner(c, accepted, o);
  const Block *bl = &c->blocks[b];
  for (uint32_t p = 0; p < c->cov->aps.count; p++) {
    if (comb_owner(c, accepted, p) < 0 || !decoder_reads(c, bl, p))
      continue;
    if (color[p] == 1) {
      *hit = (int32_t)p;
      return true;
    }
    if (color[p] == 0 && cycle_dfs(c, accepted, p, color, hit))
      return true;
  }
  color[o] = 2; // black
  return false;
}

static int32_t find_decoder_cycle_block(const Csnf *c, const bool *accepted) {
  uint32_t A = c->cov->aps.count;
  uint8_t *color = calloc(A ? A : 1, 1);
  int32_t eject = -1;
  for (uint32_t o = 0; o < A && eject < 0; o++) {
    if (color[o] != 0 || comb_owner(c, accepted, o) < 0)
      continue;
    int32_t hit = -1;
    if (cycle_dfs(c, accepted, o, color, &hit))
      eject = comb_owner(c, accepted, (uint32_t)hit);
  }
  free(color);
  return eject;
}

// Does SOLVED block `b` assign a combinational value to some output?
static bool block_is_comb(const Csnf *c, const Block *b) {
  for (uint32_t o = 0; o < c->cov->aps.count; o++)
    if (block_comb_value(c, b, (int32_t)o))
      return true;
  return false;
}

// Verdict-trust registry: which certifiers are under-approximations (strategy
// commitments for a liveness obligation) vs exact (forced-value substitution).
// See templates_internal.h.  Liveness strategy families strengthen the residual;
// the rest substitute a value the constraint forces.
VerdictTrust block_trust(const Block *b) {
  static const char *const under[] = {
      "reachability", "persistence",          "response", "server",
      "arbiter",      "round-robin",          "global-recurrence-switch",
      "safety-invariant",
  };
  for (size_t i = 0; i < sizeof under / sizeof *under; i++)
    if (b->name && !strcmp(b->name, under[i]))
      return TRUST_UNDER;
  return TRUST_EXACT; // definition / registers / reaction / mutex invariant
}

CsnfComposition *csnf_compose(const Csnf *c) {
  CsnfComposition *r = calloc(1, sizeof *r);
  if (!r)
    return nullptr;
  ConstraintCover *cov = c->cov;
  uint32_t A = cov->aps.count, B = c->nblocks, N = c->nconstraints;
  r->accepted_block = calloc(B ? B : 1, sizeof(bool));
  r->residual_constraint = calloc(N ? N : 1, sizeof(bool));
  r->conflicts = calloc(B + 1, sizeof(Conflict));
  r->elim = calloc(A ? A : 1, sizeof(Elim));
  r->elim_constraint = calloc(N ? N : 1, sizeof(bool));
  int32_t *provider = malloc((A ? A : 1) * sizeof(int32_t));
  bool *elim_excluded = calloc(B ? B : 1, sizeof(bool));
  bool *eliminated = r->elim_constraint;
  if (!r->accepted_block || !r->residual_constraint || !r->conflicts ||
      !r->elim || !eliminated || !provider || !elim_excluded) {
    free(provider);
    free(elim_excluded);
    csnf_composition_free(r);
    return nullptr;
  }
  for (uint32_t b = 0; b < B; b++)
    r->accepted_block[b] = c->blocks[b].status == CSNF_SOLVED;

  // Phase A: eliminate combinational outputs by substitution.  First break any
  // combinational-decoder cycle by excluding one provider (it stays residual).
  for (;;) {
    bool *cyc_set = calloc(B ? B : 1, sizeof(bool));
    for (uint32_t b = 0; b < B; b++)
      cyc_set[b] = r->accepted_block[b] && !elim_excluded[b];
    int32_t cyc = find_decoder_cycle_block(c, cyc_set);
    free(cyc_set);
    if (cyc < 0)
      break;
    elim_excluded[cyc] = true;
    r->conflicts[r->nconflicts++] = (Conflict){
        CONFLICT_DECODER_CYCLE, c->blocks[cyc].dec_output, (uint32_t)cyc};
  }
  for (uint32_t o = 0; o < A; o++)
    provider[o] = -1;
  for (uint32_t b = 0; b < B; b++) {
    if (!r->accepted_block[b] || elim_excluded[b])
      continue;
    for (uint32_t o = 0; o < A; o++)
      if ((ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT) && provider[o] < 0 &&
          block_comb_value(c, &c->blocks[b], (int32_t)o))
        provider[o] = (int32_t)b;
  }
  for (uint32_t o = 0; o < A; o++) {
    if (provider[o] < 0)
      continue;
    const Block *pb = &c->blocks[provider[o]];
    r->elim[r->nelim++] =
        (Elim){(int32_t)o, block_comb_value(c, pb, (int32_t)o)};
    for (uint32_t k = 0; k < pb->ncids; k++)
      eliminated[pb->cids[k]] = true;
  }

  // A combinational block is accepted only as the chosen provider; a duplicate
  // or cycle-excluded combinational block is not (its constraint stays
  // residual, to be substituted there).
  for (uint32_t b = 0; b < B; b++) {
    if (!r->accepted_block[b] || !block_is_comb(c, &c->blocks[b]))
      continue;
    bool is_provider = false;
    for (uint32_t o = 0; o < A; o++)
      if (provider[o] == (int32_t)b)
        is_provider = true;
    if (!is_provider)
      r->accepted_block[b] = false;
  }

  // Phase B: ownership fixpoint for the remaining (non-combinational) blocks --
  // servers/registers.  Eject one whose output is driven twice or constrained
  // in the residual.  Combinational providers are eliminated, never ejected.
  bool changed = true;
  while (changed) {
    changed = false;
    for (uint32_t i = 0; i < N; i++)
      r->residual_constraint[i] = !eliminated[i];
    for (uint32_t b = 0; b < B; b++)
      if (r->accepted_block[b])
        for (uint32_t k = 0; k < c->blocks[b].ncids; k++)
          r->residual_constraint[c->blocks[b].cids[k]] = false;

    for (uint32_t b = 0; b < B && !changed; b++) {
      if (!r->accepted_block[b] || block_is_comb(c, &c->blocks[b]))
        continue;
      for (uint32_t o = 0; o < A && !changed; o++) {
        if (!(ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT) ||
            !block_writes(&c->blocks[b], (int32_t)o))
          continue;
        bool dup = false;
        for (uint32_t b2 = 0; b2 < B; b2++)
          if (b2 != b && r->accepted_block[b2] &&
              block_writes(&c->blocks[b2], (int32_t)o)) {
            dup = true;
            break;
          }
        bool shared = false;
        for (uint32_t i = 0; i < N; i++)
          if (r->residual_constraint[i] &&
              apset_test(&cov->items[i].outputs, o)) {
            shared = true;
            break;
          }
        if (dup || shared) {
          r->accepted_block[b] = false;
          r->conflicts[r->nconflicts++] =
              (Conflict){dup ? CONFLICT_DUP_OUTPUT : CONFLICT_SHARED_OUTPUT,
                         (int32_t)o, b};
          changed = true;
        }
      }
    }
  }

  for (uint32_t b = 0; b < B; b++)
    if (r->accepted_block[b]) {
      r->naccepted++;
      if (block_trust(&c->blocks[b]) == TRUST_UNDER)
        r->may_strengthen = true;
    }
  for (uint32_t i = 0; i < N; i++)
    if (r->residual_constraint[i])
      r->nresidual++;
  r->neliminated = N - r->nresidual;

  bool *owned = calloc(A ? A : 1, sizeof(bool));
  for (uint32_t k = 0; k < r->nelim; k++)
    owned[r->elim[k].output] = true;
  for (uint32_t b = 0; b < B; b++)
    if (r->accepted_block[b])
      for (uint32_t o = 0; o < A; o++)
        if ((ap_table_flags(&cov->aps, o) & AP_FLAG_OUTPUT) &&
            block_writes(&c->blocks[b], (int32_t)o))
          owned[o] = true;
  for (uint32_t o = 0; o < A; o++)
    if (owned[o])
      r->nowned_outputs++;
  free(owned);

  free(provider);
  free(elim_excluded);
  r->fully_solved = r->nresidual == 0;
  return r;
}

static bool accepted_direct_aiger_block(const Csnf *c, const CsnfComposition *r,
                                        uint32_t b) {
  return b < c->nblocks && r->accepted_block[b] && c->blocks[b].db_output >= 0;
}

bool csnf_constraint_has_local_aiger(const Csnf *c, const CsnfComposition *r,
                                     uint32_t constraint_id) {
  for (uint32_t b = 0; b < c->nblocks; b++) {
    if (!accepted_direct_aiger_block(c, r, b))
      continue;
    for (uint32_t k = 0; k < c->blocks[b].ncids; k++)
      if (c->blocks[b].cids[k] == constraint_id)
        return true;
  }
  return false;
}

bool csnf_emit_local_aiger(const Csnf *c, const CsnfComposition *r, Aig *g) {
  for (uint32_t b = 0; b < c->nblocks; b++) {
    if (!accepted_direct_aiger_block(c, r, b))
      continue;
    const Block *blk = &c->blocks[b];
    uint32_t guard = aig_compile(g, blk->db_guard);
    if (guard == UINT32_MAX)
      return false;
    uint32_t failed = aig_latch(g, AIG_FALSE, AIG_FALSE);
    uint32_t next = aig_or(g, failed, aig_not(guard));
    if (!aig_set_latch_next(g, failed, next))
      return false;
    aig_set_output(g, ap_table_name(&c->cov->aps, (uint32_t)blk->db_output),
                   aig_not(failed));
  }
  return true;
}

void csnf_composition_free(CsnfComposition *r) {
  if (!r)
    return;
  free(r->accepted_block);
  free(r->residual_constraint);
  free(r->conflicts);
  free(r->elim);
  free(r->elim_constraint);
  free(r);
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
        char *th = formula_str(c, b->dec_theta);
        fprintf(out, "dec %u %s %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->dec_output),
                th ? th : "");
        free(th);
      }
      if (b->nsf_output >= 0) {
        fprintf(out, "nsf %u %s", i,
                ap_table_name(&cov->aps, (uint32_t)b->nsf_output));
        for (uint32_t g = 0; g < b->nsf_nguards; g++) {
          char *gs = formula_str(c, b->nsf_guards[g]);
          fprintf(out, " %s%s", g ? "| " : "", gs ? gs : "");
          free(gs);
        }
        fprintf(out, "\n");
      }
      if (b->sr_output >= 0) {
        const char *oname = ap_table_name(&cov->aps, (uint32_t)b->sr_output);
        for (uint32_t g = 0; g < b->sr_nsets; g++) {
          char *gs = formula_str(c, b->sr_set_guards[g]);
          fprintf(out, "srset %u %s %s\n", i, oname, gs ? gs : "");
          free(gs);
        }
        for (uint32_t g = 0; g < b->sr_nresets; g++) {
          char *gs = formula_str(c, b->sr_reset_guards[g]);
          fprintf(out, "srreset %u %s %s\n", i, oname, gs ? gs : "");
          free(gs);
        }
      }
      if (b->tog_output >= 0) {
        const char *oname = ap_table_name(&cov->aps, (uint32_t)b->tog_output);
        for (uint32_t g = 0; g < b->tog_nguards; g++) {
          char *gs = formula_str(c, b->tog_guards[g]);
          fprintf(out, "tog %u %s %s\n", i, oname, gs ? gs : "");
          free(gs);
        }
      }
      if (b->fdelay_output >= 0) {
        const char *oname =
            ap_table_name(&cov->aps, (uint32_t)b->fdelay_output);
        for (uint32_t g = 0; g < b->fdelay_n; g++) {
          char *gs = formula_str(c, b->fdelay_guards[g]);
          fprintf(out, "fdresp %u %s %u %s\n", i, oname, b->fdelay_steps[g],
                  gs ? gs : "");
          free(gs);
        }
      }
      if (b->db_output >= 0 && b->db_guard) {
        char *gs = formula_str(c, b->db_guard);
        fprintf(out, "dbuchi %u %s %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->db_output), gs ? gs : "");
        free(gs);
      }
      if (b->cyc_n > 0 && b->status == CSNF_SOLVED) {
        fprintf(out, "cyc %u %u", i, b->cyc_n);
        for (uint32_t k = 0; k < b->cyc_n; k++)
          fprintf(out, " %s",
                  ap_table_name(&cov->aps, (uint32_t)b->cyc_outputs[k]));
        fprintf(out, "\n");
      }
      if (b->arb_n > 0 && b->status == CSNF_SOLVED) {
        fprintf(out, "arb %u %u", i, b->arb_n);
        for (uint32_t k = 0; k < b->arb_n; k++)
          fprintf(out, " %s",
                  ap_table_name(&cov->aps, (uint32_t)b->arb_outputs[k]));
        fprintf(out, "\n");
      }
      if (b->one_output >= 0 && b->status == CSNF_SOLVED)
        fprintf(out, "one %u %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->one_output));
      if (b->hold_output >= 0 && b->status == CSNF_SOLVED)
        fprintf(out, "hold %u %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->hold_output));
      if (b->resp_output >= 0 && b->status == CSNF_SOLVED) {
        const TemplateCandidate *resp = constraint_find_candidate_payload(
            cov, &cov->items[b->cids[0]], CAND_RESPONSE);
        int32_t g = resp ? resp->u.response.guard : -1;
        fprintf(out, "resp %u %s", i,
                ap_table_name(&cov->aps, (uint32_t)b->resp_output));
        if (g >= 0)
          fprintf(out, " %s", ap_table_name(&cov->aps, (uint32_t)g));
        fprintf(out, "\n");
      }
      if (b->asg_output >= 0 && b->status == CSNF_SOLVED) {
        fprintf(out, "asg %u %s", i,
                ap_table_name(&cov->aps, (uint32_t)b->asg_output));
        for (uint32_t g = 0; g < b->asg_nguards; g++) {
          char *gs = formula_str(c, b->asg_guards[g]);
          fprintf(out, " %s%s", g ? "| " : "", gs ? gs : "");
          free(gs);
        }
        fprintf(out, "\n");
      }
      if (b->reg_output >= 0 && b->reg_theta) {
        char *th = formula_str(c, b->reg_theta);
        fprintf(out, "reg %u %s %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->reg_output),
                th ? th : "");
        free(th);
      }
      for (uint32_t k = 0; k < b->inv_n; k++) {
        char *v = formula_str(c, b->inv_values[k]);
        fprintf(out, "inv %u %s %s\n", i,
                ap_table_name(&cov->aps, (uint32_t)b->inv_outputs[k]),
                v ? v : "");
        free(v);
      }
    }
    if (b->cert)
      fprintf(out, "cert %u %s\n", i, b->cert);
    // Claims = the member constraints' formulas.
    for (uint32_t k = 0; k < b->ncids; k++) {
      char *cl = formula_str(c, cov->items[b->cids[k]].formula);
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
      char *th = formula_str(c, b->dec_theta);
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
    if (b->db_output >= 0 && b->status == CSNF_SOLVED) {
      char *gs = formula_str(c, b->db_guard);
      fprintf(out, "      deterministic Buchi: %s while G(%s) holds\n",
              ap_table_name(&cov->aps, (uint32_t)b->db_output), gs ? gs : "");
      free(gs);
    }
  }
}
