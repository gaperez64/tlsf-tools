/// tlsfresidual — what is left of a spec after template certification.
///
/// Runs the cover -> recognize -> certify -> compose pipeline, keeps the
/// maximal sound set of SOLVED blocks (csnf_compose), and re-emits the
/// remaining (residual) obligations as a single LTL formula, ready to hand to
/// an external synthesizer (e.g. `ltlsynt --ins=.. --outs=..`).  The certified
/// controllers plus a controller for this residual realise the whole spec.

#include "tlsf/cli.h"
#include "tlsf/classify.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/print_ltlxba.h"
#include "tlsf/recognize.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] [FILE]\n"
      "Emit the residual LTL of a spec after template certification.\n"
      "  --split                      decompose constraints first\n"
      "  --single                     emit the whole residual as one formula\n"
      "  --output-dir DIR             write one residual.<k>.ltl per cluster\n"
      "  --format ltlxba|ltl          output dialect (default ltlxba)\n"
      "  --overwrite-semantics VALUE  replace SEMANTICS\n"
      "  --overwrite-target VALUE     replace TARGET\n"
      "  --param NAME=VALUE           override a parameter (repeatable)\n"
      "  --output FILE                write to FILE (default stdout)\n"
      "  --version, --help\n",
      prog);
}

static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsfresidual: bad --param '%s'\n", s);
    return false;
  }
  size_t nlen = (size_t)(eq - s);
  char *name = malloc(nlen + 1);
  if (!name)
    return false;
  memcpy(name, s, nlen);
  name[nlen] = '\0';
  char *end;
  long long val = strtoll(eq + 1, &end, 10);
  if (*end != '\0') {
    fprintf(stderr, "tlsfresidual: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

// Map a constraint Role to its destination section list in the spec.
static FormulaList *role_list(TlsfSpec *spec, Role role) {
  switch (role) {
  case TLSF_ROLE_INITIALLY:
    return &spec->initially;
  case TLSF_ROLE_PRESET:
    return &spec->preset;
  case TLSF_ROLE_REQUIRE:
    return &spec->require;
  case TLSF_ROLE_ASSERT:
    return &spec->assert_;
  case TLSF_ROLE_ASSUME:
    return &spec->assume;
  case TLSF_ROLE_GUARANTEE:
  default:
    return &spec->guarantee;
  }
}

// Apply every eliminated-output substitution to `n` (the elimination set is
// acyclic, so nelim+1 passes reach a fixpoint with all eliminated outputs
// gone).
static const Node *apply_elims(Arena *a, const Node *n,
                               const CsnfComposition *comp,
                               ConstraintCover *cov) {
  for (uint32_t pass = 0; pass <= comp->nelim; pass++)
    for (uint32_t k = 0; k < comp->nelim; k++)
      n = node_subst(a, n,
                     ap_table_name(&cov->aps, (uint32_t)comp->elim[k].output),
                     comp->elim[k].value);
  return n;
}

// Mark every AP occurring in `n` in `seen`.
static void collect_aps(const Node *n, ConstraintCover *cov, bool *seen) {
  switch (n->kind) {
  case NODE_AP: {
    int32_t i = ap_table_find(&cov->aps, n->name);
    if (i >= 0)
      seen[i] = true;
    return;
  }
  case NODE_NOT:
  case NODE_X:
  case NODE_X_STRONG:
  case NODE_F:
  case NODE_G:
    collect_aps(n->arg, cov, seen);
    return;
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_M:
    collect_aps(n->lhs, cov, seen);
    collect_aps(n->rhs, cov, seen);
    return;
  default:
    return;
  }
}

// Print the residual signals (in `seen`) carrying `flag`, comma-separated.
static void print_signals(FILE *out, ConstraintCover *cov, const bool *seen,
                          uint8_t flag) {
  bool first = true;
  for (uint32_t a = 0; a < cov->aps.count; a++) {
    if (!seen[a] || !(ap_table_flags(&cov->aps, a) & flag))
      continue;
    fprintf(out, "%s%s", first ? "" : ",", ap_table_name(&cov->aps, a));
    first = false;
  }
}

static uint32_t uf_find(uint32_t *p, uint32_t x) {
  while (p[x] != x) {
    p[x] = p[p[x]];
    x = p[x];
  }
  return x;
}

// Rebuild the spec's section lists from the residual constraints belonging to
// cluster `kk` (or all residual when `all`), always including the global
// environment (key == UINT32_MAX), and assemble the cluster's LTL formula.
// `seen` (length aps.count) is filled with the APs the formula mentions.
static Node *build_cluster(TlsfSpec *spec, ConstraintCover *cov,
                           const Node **rf, const uint32_t *key, uint32_t kk,
                           bool all, uint32_t n, bool *seen) {
  spec->initially.count = spec->require.count = spec->assume.count = 0;
  spec->preset.count = spec->assert_.count = spec->guarantee.count = 0;
  memset(seen, 0, cov->aps.count ? cov->aps.count : 1);
  for (uint32_t i = 0; i < n; i++) {
    if (!rf[i] || !(all || key[i] == kk || key[i] == UINT32_MAX))
      continue;
    collect_aps(rf[i], cov, seen);
    (void)formula_list_push(spec, role_list(spec, cov->items[i].role),
                            (Node *)rf[i]);
  }
  ClassifiedSpec *cs = classify_spec(spec);
  if (!cs)
    return nullptr;
  Node *root = build_spec_formula(spec, cs, PRINT_ALL);
  if (semantics_is_finite(spec->info.semantics))
    root = apply_rewrites(spec->arena, root,
                          RW_NO_WEAK_UNTIL | RW_NO_STRONG_RELEASE);
  return root;
}

int main(int argc, char *argv[]) {
  bool split = false, single = false;
  LtlFormat fmt = LTL_FMT_LTLXBA;
  const char *input_file = nullptr, *output_file = nullptr, *out_dir = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfresidual: %s requires an argument\n",   \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--single") == 0) {
      single = true;
    } else if (strcmp(a, "--output-dir") == 0) {
      out_dir = NEED_ARG();
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "ltlxba"))
        fmt = LTL_FMT_LTLXBA;
      else if (!strcmp(v, "ltl"))
        fmt = LTL_FMT_LTL;
      else {
        fprintf(stderr, "tlsfresidual: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfresidual: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfresidual %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfresidual: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfresidual: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  FILE *fp = cli_open_input(input_file, "tlsfresidual");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfresidual");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfresidual: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfresidual: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  // Cover -> recognize -> certify -> compose.
  ConstraintCover *cov = cover_build(spec, split);
  if (!cov) {
    fprintf(stderr, "tlsfresidual: out of memory\n");
    spec_free(spec);
    return 1;
  }
  recognize_all(cov);
  Csnf *csnf = templates_certify(cov, TPL_ALL, true);
  CsnfComposition *comp = csnf ? csnf_compose(csnf) : nullptr;
  if (!csnf || !comp) {
    fprintf(stderr, "tlsfresidual: out of memory\n");
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  FILE *out = cli_open_output(output_file, "tlsfresidual");
  if (!out) {
    csnf_composition_free(comp);
    csnf_free(csnf);
    spec_free(spec);
    return 1;
  }

  uint32_t A = cov->aps.count, N = cov->count, tot = N;
  int rc = 0;

  if (comp->fully_solved)
    fprintf(out, "c composition: fully-solved\n");
  else
    fprintf(out,
            "c composition: residual=%u/%u constraints (%.0f%% eliminated), "
            "outputs owned=%u, conflicts=%u\n",
            comp->nresidual, tot,
            tot ? 100.0 * (double)comp->neliminated / (double)tot : 0.0,
            comp->nowned_outputs, comp->nconflicts);

  // Substitute solved combinational outputs out of every residual constraint.
  const Node **rf = calloc(N ? N : 1, sizeof(Node *));
  for (uint32_t i = 0; i < N; i++)
    if (comp->residual_constraint[i])
      rf[i] = apply_elims(spec->arena, cov->items[i].formula, comp, cov);

  bool *seen = calloc(A ? A : 1, sizeof(bool));

  if (single) {
    Node *root =
        build_cluster(spec, cov, rf, nullptr, 0, /*all=*/true, N, seen);
    if (!root) {
      rc = 1;
    } else {
      fprintf(out, "c outs=");
      print_signals(out, cov, seen, AP_FLAG_OUTPUT);
      fprintf(out, "\nc ins=");
      print_signals(out, cov, seen, AP_FLAG_INPUT);
      fprintf(out, "\n");
      print_ltl(out, root, fmt, /*full_parens=*/false,
                semantics_is_finite(spec->info.semantics));
    }
  } else {
    // Cluster residual constraints by shared output (output-disjoint
    // decomposition: E -> AND Gi == AND (E -> Gi)).  Pure-input environment
    // constraints have no output and are replicated into every cluster.
    uint32_t *parent = malloc((A ? A : 1) * sizeof(uint32_t));
    for (uint32_t a = 0; a < A; a++)
      parent[a] = a;
    for (uint32_t i = 0; i < N; i++) {
      if (!rf[i])
        continue;
      memset(seen, 0, A);
      collect_aps(rf[i], cov, seen);
      int64_t first = -1;
      for (uint32_t a = 0; a < A; a++) {
        if (!seen[a] || !(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
          continue;
        if (first < 0)
          first = (int64_t)a;
        else {
          uint32_t ra = uf_find(parent, a),
                   rb = uf_find(parent, (uint32_t)first);
          if (ra != rb)
            parent[ra] = rb;
        }
      }
    }
    // Per-constraint cluster key: its output component, or a sentinel for an
    // input-only system obligation, or UINT32_MAX for global environment.
    uint32_t *key = malloc((N ? N : 1) * sizeof(uint32_t));
    for (uint32_t i = 0; i < N; i++) {
      key[i] = UINT32_MAX;
      if (!rf[i])
        continue;
      memset(seen, 0, A);
      collect_aps(rf[i], cov, seen);
      int64_t first = -1;
      for (uint32_t a = 0; a < A; a++)
        if (seen[a] && (ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT)) {
          first = (int64_t)a;
          break;
        }
      if (first >= 0)
        key[i] = uf_find(parent, (uint32_t)first);
      else if (!cov->items[i].assumption_side)
        key[i] = A; // input-only system obligation: its own cluster
    }
    // Distinct, non-global cluster keys.
    uint32_t *keys = malloc((N + 1) * sizeof(uint32_t));
    uint32_t K = 0;
    for (uint32_t i = 0; i < N; i++) {
      if (key[i] == UINT32_MAX)
        continue;
      bool dup = false;
      for (uint32_t j = 0; j < K; j++)
        if (keys[j] == key[i])
          dup = true;
      if (!dup)
        keys[K++] = key[i];
    }

    fprintf(out, "c clusters %u\n", K);
    for (uint32_t k = 0; k < K && rc == 0; k++) {
      Node *root = build_cluster(spec, cov, rf, key, keys[k], false, N, seen);
      if (!root) {
        rc = 1;
        break;
      }
      bool finite = semantics_is_finite(spec->info.semantics);
      if (out_dir) {
        char path[4096];
        snprintf(path, sizeof path, "%s/residual.%u.ltl", out_dir, k);
        FILE *cf = fopen(path, "w");
        if (!cf) {
          fprintf(stderr, "tlsfresidual: cannot write %s\n", path);
          rc = 1;
          break;
        }
        fprintf(cf, "c outs=");
        print_signals(cf, cov, seen, AP_FLAG_OUTPUT);
        fprintf(cf, "\nc ins=");
        print_signals(cf, cov, seen, AP_FLAG_INPUT);
        fprintf(cf, "\n");
        print_ltl(cf, root, fmt, false, finite);
        fclose(cf);
        fprintf(out, "c cluster %u file=residual.%u.ltl outs=", k, k);
        print_signals(out, cov, seen, AP_FLAG_OUTPUT);
        fprintf(out, " ins=");
        print_signals(out, cov, seen, AP_FLAG_INPUT);
        fprintf(out, "\n");
      } else {
        fprintf(out, "c cluster %u outs=", k);
        print_signals(out, cov, seen, AP_FLAG_OUTPUT);
        fprintf(out, " ins=");
        print_signals(out, cov, seen, AP_FLAG_INPUT);
        fprintf(out, "\n");
        print_ltl(out, root, fmt, false, finite);
      }
    }
    free(parent);
    free(key);
    free(keys);
  }

  free(seen);
  free(rf);
  if (rc)
    fprintf(stderr, "tlsfresidual: classification failed (OOM)\n");
  if (output_file)
    fclose(out);
  csnf_composition_free(comp);
  csnf_free(csnf);
  spec_free(spec);
  return rc;
}
