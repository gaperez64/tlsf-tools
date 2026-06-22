/// tlsfbenchgraph — run the synthesis-graph pipeline over a corpus of TLSF
/// specs and emit per-spec metrics (TSV) describing their form/template shapes,
/// plus an optional aggregate summary.  A research/benchmarking driver: it
/// reuses cover/recognize/certify and adds no new analysis.
// NOLINTNEXTLINE(cert-dcl37-c)
#define _XOPEN_SOURCE 700
#include "tlsf/ast.h"
#include "tlsf/classify.h"
#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/nnf.h"
#include "tlsf/normalize.h"
#include "tlsf/recognize.h"
#include "tlsf/residual.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"
#include "tlsf/templates.h"

#include <ftw.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE...]\n"
          "Per-spec form/template-shape metrics (TSV) over a TLSF corpus.\n"
          "  --input-dir DIR    recursively add every *.tlsf under DIR\n"
          "  --file-list FILE   add the paths listed in FILE (one per line)\n"
          "  --split            split constraints at top-level &&\n"
          "  --summary          append an aggregate summary\n"
          "  --output FILE      write to FILE (default stdout)\n"
          "  --version, --help\n",
          prog);
}

// ---- file collection ------------------------------------------------------

static const char **g_files;
static size_t g_nfiles, g_cap;

static void add_file(const char *path) {
  if (g_nfiles == g_cap) {
    g_cap = g_cap ? g_cap * 2 : 64;
    const char **next = realloc(g_files, g_cap * sizeof(char *));
    if (!next) {
      perror("tlsfbenchgraph: realloc");
      exit(1);
    }
    g_files = next;
  }
  char *copy = strdup(path);
  if (!copy) {
    perror("tlsfbenchgraph: strdup");
    exit(1);
  }
  g_files[g_nfiles++] = copy;
}

static int nftw_cb(const char *path, const struct stat *sb, int type,
                   struct FTW *ftw) {
  (void)sb;
  (void)ftw;
  if (type == FTW_F) {
    size_t n = strlen(path);
    if (n > 5 && strcmp(path + n - 5, ".tlsf") == 0)
      add_file(path);
  }
  return 0;
}

static int cstr_cmp(const void *a, const void *b) {
  return strcmp(*(const char *const *)a, *(const char *const *)b);
}

// ---- metrics --------------------------------------------------------------
// Formula-size proxy is the shared `ast_node_count` (include/tlsf/ast.h).

static uint32_t uf_find(uint32_t *parent, uint32_t x) {
  while (parent[x] != x)
    x = parent[x] = parent[parent[x]]; // path halving
  return x;
}

// Largest set of outputs connected by "co-occur in the same constraint".
static uint32_t largest_output_component(ConstraintCover *cov) {
  uint32_t A = cov->aps.count;
  if (A == 0)
    return 0;
  uint32_t *parent = malloc(A * sizeof(uint32_t));
  for (uint32_t i = 0; i < A; i++)
    parent[i] = i;

  for (uint32_t c = 0; c < cov->count; c++) {
    int64_t first = -1;
    for (uint32_t a = 0; a < A; a++) {
      if (!apset_test(&cov->items[c].outputs, a))
        continue;
      if (first < 0)
        first = (int64_t)a;
      else {
        uint32_t ra = uf_find(parent, a), rf = uf_find(parent, (uint32_t)first);
        if (ra != rf)
          parent[ra] = rf;
      }
    }
  }

  uint32_t *size = calloc(A, sizeof(uint32_t));
  uint32_t best = 0;
  for (uint32_t a = 0; a < A; a++) {
    if (!(ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT))
      continue;
    uint32_t r = uf_find(parent, a);
    size[r]++;
    if (size[r] > best)
      best = size[r];
  }
  free(parent);
  free(size);
  return best;
}

typedef struct {
  bool ok;
  uint32_t inputs, outputs, constraints, safety, liveness;
  uint32_t response, mutex, recurrence, persistence, global_rec, gnext,
      definition;
  uint32_t tcands, solved, certified, dependent, residual, comp;
  uint32_t conflicts, fully_solved;
  uint32_t elim_constraints, owned_outputs;
  uint32_t size_raw, size_norm;
  // Residual (post-all-templates `--aiger` residual): the genuine games the
  // synthesis backends still face after every template controller is applied.
  uint32_t residual_clusters, residual_outputs,
      largest_residual_cluster_outputs;
  uint32_t residual_liveness_clusters, residual_size_norm;
  // Sickert-style normalization obstacles over the raw constraint formulas.
  TlsfObstacles obstacles;
} Metrics;

// Measure the residual the synthesis backends still face after every template
// controller is applied.  A constraint is dropped when it belongs to any
// accepted SOLVED block (`!comp->residual_constraint[i]`): combinational
// `o:=value` controllers, local-AIGER register/toggle/... blocks, AND
// multi-constraint solved blocks like arbiters/mutexes.  This is the
// composition residual, so a fully-solved spec yields an empty residual
// (`fully_solved` <=> no clusters), crediting all template work.  Surviving
// constraints have the combinational controllers substituted in and are
// partitioned into output-disjoint clusters (one independent game each) with
// the shared residual-clustering helpers.  Each cluster is classified with the
// same NNF + classify_formula path as the monolith safety/liveness columns
// (cover.c:150,153), so the two are apples-to-apples.
static void measure_residual(TlsfSpec *spec, ConstraintCover *cov,
                             const CsnfComposition *comp, Metrics *m) {
  uint32_t N = cov->count, A = cov->aps.count;
  const Node **rf = calloc(N ? N : 1, sizeof(Node *));
  bool *seen = calloc(A ? A : 1, sizeof(bool));
  bool *any_out = calloc(A ? A : 1, sizeof(bool));
  uint32_t *key = malloc((N ? N : 1) * sizeof(uint32_t));
  if (!rf || !seen || !any_out || !key) {
    free(rf);
    free(seen);
    free(any_out);
    free(key);
    return;
  }
  for (uint32_t i = 0; i < N; i++) {
    if (!comp->residual_constraint[i])
      continue;
    const Node *f =
        residual_apply_elims(spec->arena, cov->items[i].formula, comp, cov);
    f = apply_rewrites(spec->arena, (Node *)f, RW_SIMPLIFY_WEAK);
    if (f->kind != NODE_TRUE)
      rf[i] = f;
  }

  uint32_t *keys = nullptr;
  uint32_t K = residual_cluster_keys(cov, rf, N, key, &keys);
  m->residual_clusters = K;
  for (uint32_t k = 0; k < K; k++) {
    Node *root = residual_build_cluster(spec, cov, rf, key, keys[k],
                                        /*all=*/false, /*prune=*/true, N, seen);
    if (!root)
      continue;
    uint32_t outs = 0;
    for (uint32_t a = 0; a < A; a++)
      if (seen[a] && (ap_table_flags(&cov->aps, a) & AP_FLAG_OUTPUT)) {
        outs++;
        any_out[a] = true;
      }
    if (outs > m->largest_residual_cluster_outputs)
      m->largest_residual_cluster_outputs = outs;
    Node *nf = to_nnf(spec->arena, root, true);
    if (nf && classify_formula(nf) == FCLASS_LIVENESS)
      m->residual_liveness_clusters++;
    Node *sn = apply_rewrites(spec->arena, root, RW_STRONG_SIMPLIFY);
    m->residual_size_norm += ast_node_count(sn ? sn : root);
  }
  for (uint32_t a = 0; a < A; a++)
    m->residual_outputs += any_out[a] ? 1 : 0;
  free(rf);
  free(seen);
  free(any_out);
  free(key);
  free(keys);
}

static Metrics measure(const char *path, bool split) {
  Metrics m = {0};
  FILE *fp = cli_open_input(path, "tlsfbenchgraph");
  if (!fp)
    return m;
  TlsfSpec *spec = cli_parse(fp, "tlsfbenchgraph");
  fclose(fp);
  if (!spec)
    return m;
  if (expand(spec, nullptr, 0) != 0) {
    spec_free(spec);
    return m;
  }
  ConstraintCover *cov = cover_build(spec, split);
  if (!cov) {
    spec_free(spec);
    return m;
  }
  recognize_all(cov);

  m.ok = true;
  for (uint32_t i = 0; i < cov->aps.count; i++) {
    uint8_t f = ap_table_flags(&cov->aps, i);
    m.inputs += (f & AP_FLAG_INPUT) != 0;
    m.outputs += (f & AP_FLAG_OUTPUT) != 0;
  }
  m.constraints = cov->count;
  for (uint32_t i = 0; i < cov->count; i++) {
    Constraint *c = &cov->items[i];
    if (c->is_safety)
      m.safety++;
    else
      m.liveness++;
    m.tcands += c->candidate_count;
    for (uint16_t k = 0; k < c->candidate_count; k++) {
      const char *n = c->candidates[k];
      if (!strcmp(n, "response"))
        m.response++;
      else if (!strcmp(n, "mutex"))
        m.mutex++;
      else if (!strcmp(n, "pure-recurrence"))
        m.recurrence++;
      else if (!strcmp(n, "persistence"))
        m.persistence++;
      else if (!strcmp(n, "global-recurrence-switch"))
        m.global_rec++;
      else if (!strcmp(n, "guarded-next-assignment"))
        m.gnext++;
      else if (!strcmp(n, "definition"))
        m.definition++;
    }
    m.size_raw += ast_node_count(c->formula);
    Node *nf = apply_rewrites(spec->arena, c->formula, RW_STRONG_SIMPLIFY);
    m.size_norm += nf ? ast_node_count(nf) : ast_node_count(c->formula);
    tlsf_norm_count_obstacles(c->formula, &m.obstacles);
  }

  Csnf *csnf = templates_certify(cov, TPL_ALL, true);
  if (csnf) {
    csnf_counts(csnf, &m.solved, &m.certified, nullptr, &m.residual,
                &m.dependent);
    CsnfComposition *comp = csnf_compose(csnf);
    if (comp) {
      m.conflicts = comp->nconflicts;
      m.fully_solved = comp->fully_solved ? 1 : 0;
      m.elim_constraints = comp->neliminated;
      m.owned_outputs = comp->nowned_outputs;
      measure_residual(spec, cov, comp, &m);
      csnf_composition_free(comp);
    }
    csnf_free(csnf);
  }
  m.comp = largest_output_component(cov);

  spec_free(spec);
  return m;
}

static const char *basename_of(const char *p) {
  const char *s = strrchr(p, '/');
  return s ? s + 1 : p;
}

int main(int argc, char *argv[]) {
  bool summary = false, split = false;
  const char *output_file = nullptr;

#define NEED_ARG()                                                             \
  (++i >= argc ? (fprintf(stderr, "tlsfbenchgraph: %s requires an argument\n", \
                          argv[i - 1]),                                        \
                  exit(1), nullptr)                                            \
               : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--input-dir") == 0) {
      nftw(NEED_ARG(), nftw_cb, 16, 0);
    } else if (strcmp(a, "--file-list") == 0) {
      FILE *fl = fopen(NEED_ARG(), "r");
      if (!fl) {
        perror("tlsfbenchgraph: --file-list");
        return 1;
      }
      char line[4096];
      while (fgets(line, sizeof line, fl)) {
        size_t n = strlen(line);
        while (n && (line[n - 1] == '\n' || line[n - 1] == '\r'))
          line[--n] = '\0';
        if (n)
          add_file(line);
      }
      fclose(fl);
    } else if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--summary") == 0) {
      summary = true;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (strcmp(v, "tsv") != 0) {
        fprintf(stderr, "tlsfbenchgraph: only --format tsv is supported\n");
        return 1;
      }
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfbenchgraph %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (!strcmp(a, "--passes") || !strcmp(a, "--timeout") ||
               !strcmp(a, "--output-dir")) {
      fprintf(stderr,
              "tlsfbenchgraph: %s is not implemented yet (normalization / "
              "parallelism are later milestones)\n",
              a);
      return 2;
    } else if (a[0] != '-') {
      add_file(a);
    } else {
      fprintf(stderr, "tlsfbenchgraph: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  if (g_nfiles == 0) {
    fprintf(stderr, "tlsfbenchgraph: no input files\n");
    return 1;
  }
  qsort(g_files, g_nfiles, sizeof(char *), cstr_cmp); // determinism

  FILE *out = cli_open_output(output_file, "tlsfbenchgraph");
  if (!out)
    return 1;

  fprintf(out,
          "file\tparse_status\tinputs\toutputs\tconstraints\tsafety\t"
          "liveness\tresponse\tmutex\trecurrence\tpersistence\t"
          "global_recurrence\tguarded_next\tdefinition\t"
          "template_candidates\tsolved_blocks\tcertified_blocks\t"
          "dependent_outputs\tresidual_constraints\tlargest_output_component"
          "\tformula_size_raw\tformula_size_norm\t"
          "fully_solved\tconflicts\t"
          "eliminated_constraints\towned_outputs\t"
          "residual_clusters\tresidual_outputs\t"
          "largest_residual_cluster_outputs\tresidual_liveness_clusters\t"
          "residual_size_norm\t"
          "u_under_w\tlimit_under_temporal\tw_under_gf\tu_under_fg\n");

  // Aggregates.
  uint32_t nok = 0, nfail = 0;
  uint64_t tot[16] = {0};
  uint32_t with_solved = 0, with_resp = 0, with_mutex = 0, with_def = 0,
           with_rec = 0, fully = 0;
  uint64_t mono_lc = 0, res_lc = 0, mono_sz = 0, res_sz = 0;
  uint32_t lc_strictly_smaller = 0, drop_to_safety = 0, factored = 0;

  for (size_t i = 0; i < g_nfiles; i++) {
    Metrics m = measure(g_files[i], split);
    const char *fn = basename_of(g_files[i]);
    if (!m.ok) {
      nfail++;
      fprintf(out,
              "%s\tfail\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-"
              "\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\n",
              fn);
      continue;
    }
    nok++;
    fprintf(out,
            "%s\tok\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u"
            "\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%u\t%llu"
            "\t%llu\t%llu\t%llu\n",
            fn, m.inputs, m.outputs, m.constraints, m.safety, m.liveness,
            m.response, m.mutex, m.recurrence, m.persistence, m.global_rec,
            m.gnext, m.definition, m.tcands, m.solved, m.certified, m.dependent,
            m.residual, m.comp, m.size_raw, m.size_norm, m.fully_solved,
            m.conflicts, m.elim_constraints, m.owned_outputs,
            m.residual_clusters, m.residual_outputs,
            m.largest_residual_cluster_outputs, m.residual_liveness_clusters,
            m.residual_size_norm, (unsigned long long)m.obstacles.u_under_w,
            (unsigned long long)m.obstacles.limit_under_temporal,
            (unsigned long long)m.obstacles.w_under_gf,
            (unsigned long long)m.obstacles.u_under_fg);

    tot[0] += m.response;
    tot[1] += m.mutex;
    tot[2] += m.recurrence;
    tot[3] += m.persistence;
    tot[4] += m.gnext;
    tot[5] += m.definition;
    tot[12] += m.global_rec;
    tot[6] += m.solved;
    tot[7] += m.certified;
    with_solved += m.solved > 0;
    fully += m.fully_solved;
    tot[8] += m.constraints;
    tot[9] += m.elim_constraints;
    tot[10] += m.owned_outputs;
    tot[11] += m.outputs;
    with_resp += m.response > 0;
    with_mutex += m.mutex > 0;
    with_def += m.definition > 0;
    with_rec += m.recurrence > 0;
    mono_lc += m.comp;
    res_lc += m.largest_residual_cluster_outputs;
    mono_sz += m.size_norm;
    res_sz += m.residual_size_norm;
    lc_strictly_smaller += m.largest_residual_cluster_outputs < m.comp;
    drop_to_safety += m.liveness > 0 && m.fully_solved == 0 &&
                      m.residual_liveness_clusters == 0;
    factored += m.residual_clusters >= 2;
  }

  if (summary) {
    fprintf(out, "# summary: %u parsed, %u failed (of %zu)\n", nok, nfail,
            g_nfiles);
    fprintf(out,
            "# total candidates: response=%llu mutex=%llu recurrence=%llu "
            "persistence=%llu global_recurrence=%llu guarded_next=%llu "
            "definition=%llu\n",
            (unsigned long long)tot[0], (unsigned long long)tot[1],
            (unsigned long long)tot[2], (unsigned long long)tot[3],
            (unsigned long long)tot[12], (unsigned long long)tot[4],
            (unsigned long long)tot[5]);
    fprintf(out, "# total blocks: solved=%llu certified=%llu\n",
            (unsigned long long)tot[6], (unsigned long long)tot[7]);
    fprintf(out,
            "# specs with >=1: response=%u mutex=%u recurrence=%u "
            "definition=%u solved=%u\n",
            with_resp, with_mutex, with_rec, with_def, with_solved);
    fprintf(out, "# specs fully solved (sound composition): %u\n", fully);
    fprintf(out,
            "# residual reduction: %llu/%llu constraints eliminated (%.1f%%), "
            "%llu/%llu outputs owned (%.1f%%)\n",
            (unsigned long long)tot[9], (unsigned long long)tot[8],
            tot[8] ? 100.0 * (double)tot[9] / (double)tot[8] : 0.0,
            (unsigned long long)tot[10], (unsigned long long)tot[11],
            tot[11] ? 100.0 * (double)tot[10] / (double)tot[11] : 0.0);
    fprintf(out,
            "# residual complexity: largest sub-game outputs %llu->%llu "
            "(monolith->residual sum; %.1f%%), strictly smaller in %u specs; "
            "%u drop liveness->safety, %u fully solved; %u factor into >=2 "
            "clusters; residual size %llu/%llu norm nodes (%.1f%%)\n",
            (unsigned long long)mono_lc, (unsigned long long)res_lc,
            mono_lc ? 100.0 * (double)res_lc / (double)mono_lc : 0.0,
            lc_strictly_smaller, drop_to_safety, fully, factored,
            (unsigned long long)res_sz, (unsigned long long)mono_sz,
            mono_sz ? 100.0 * (double)res_sz / (double)mono_sz : 0.0);
  }

  if (output_file)
    fclose(out);
  for (size_t i = 0; i < g_nfiles; i++)
    free((void *)g_files[i]);
  free(g_files);
  return 0;
}
