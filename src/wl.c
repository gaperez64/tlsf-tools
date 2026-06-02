#define _POSIX_C_SOURCE 200809L
#include "tlsf/wl.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

// ---------------------------------------------------------------------------
// FNV-1a 64 (fixed, machine-independent — WL colors must be reproducible).
// ---------------------------------------------------------------------------

static uint64_t fnv1a(const void *data, size_t n) {
  const unsigned char *p = data;
  uint64_t h = 0xcbf29ce484222325ull;
  for (size_t i = 0; i < n; i++) {
    h ^= p[i];
    h *= 0x100000001b3ull;
  }
  return h;
}

// ---------------------------------------------------------------------------
// String->count histogram (open addressing; owns its key strings)
// ---------------------------------------------------------------------------

typedef struct {
  char **keys;
  uint32_t *cnts;
  uint32_t count, cap;
  int32_t *buckets; // idx+1, 0 = empty
  uint32_t hcap;
} Hist;

static void hist_init(Hist *h) { *h = (Hist){0}; }

static void hist_rehash(Hist *h, uint32_t ncap) {
  int32_t *b = malloc(ncap * sizeof(int32_t));
  for (uint32_t i = 0; i < ncap; i++)
    b[i] = 0;
  for (uint32_t i = 0; i < h->count; i++) {
    uint32_t m = ncap - 1;
    uint32_t j = (uint32_t)fnv1a(h->keys[i], strlen(h->keys[i])) & m;
    while (b[j])
      j = (j + 1) & m;
    b[j] = (int32_t)i + 1;
  }
  free(h->buckets);
  h->buckets = b;
  h->hcap = ncap;
}

static void hist_add(Hist *h, const char *key) {
  if (h->hcap == 0)
    hist_rehash(h, 64);
  uint32_t m = h->hcap - 1;
  uint32_t j = (uint32_t)fnv1a(key, strlen(key)) & m;
  while (h->buckets[j]) {
    uint32_t idx = (uint32_t)h->buckets[j] - 1;
    if (strcmp(h->keys[idx], key) == 0) {
      h->cnts[idx]++;
      return;
    }
    j = (j + 1) & m;
  }
  if (h->count == h->cap) {
    h->cap = h->cap ? h->cap * 2 : 64;
    h->keys = realloc(h->keys, h->cap * sizeof(char *));
    h->cnts = realloc(h->cnts, h->cap * sizeof(uint32_t));
  }
  uint32_t idx = h->count++;
  h->keys[idx] = strdup(key);
  h->cnts[idx] = 1;
  if (h->count * 2 > h->hcap)
    hist_rehash(h, h->hcap * 2);
  else
    h->buckets[j] = (int32_t)idx + 1;
}

// ---------------------------------------------------------------------------
// WlFeatures: sorted (key,count) array
// ---------------------------------------------------------------------------

typedef struct {
  char *key;
  uint32_t count;
} WlEntry;

struct WlFeatures {
  WlEntry *entries;
  uint32_t count;
  int depth;
  WlLabels labels;
};

static int entry_cmp(const void *a, const void *b) {
  return strcmp(((const WlEntry *)a)->key, ((const WlEntry *)b)->key);
}

// ---------------------------------------------------------------------------
// Materialized graph (constraints 0..K-1, APs K..K+A-1) with typed edges
// ---------------------------------------------------------------------------

typedef struct {
  uint32_t *nbr;
  const char **type;
  uint32_t n, cap;
} Adj;

static void adj_push(Adj *a, uint32_t v, const char *type) {
  if (a->n == a->cap) {
    a->cap = a->cap ? a->cap * 2 : 4;
    a->nbr = realloc(a->nbr, a->cap * sizeof(uint32_t));
    a->type = realloc(a->type, a->cap * sizeof(char *));
  }
  a->nbr[a->n] = v;
  a->type[a->n] = type;
  a->n++;
}

static void add_edge(Adj *adj, uint32_t u, uint32_t v, const char *type) {
  adj_push(&adj[u], v, type);
  adj_push(&adj[v], u, type);
}

// Initial (round-0) color string for a node, by label scheme.
static char *base_color(const ConstraintCover *cov, uint32_t node, uint32_t K,
                        WlLabels labels) {
  char buf[256];
  if (node >= K) { // AP node
    uint32_t a = node - K;
    uint8_t f = ap_table_flags(&cov->aps, a);
    const char *own = (labels == WL_BASIC)   ? ""
                      : (f & AP_FLAG_OUTPUT) ? ":output"
                      : (f & AP_FLAG_INPUT)  ? ":input"
                                             : "";
    snprintf(buf, sizeof buf, "AP%s", own);
    return strdup(buf);
  }
  const Constraint *c = &cov->items[node];
  if (labels == WL_BASIC)
    return strdup("C");
  int len = snprintf(buf, sizeof buf, "%s:%s", role_name(c->role),
                     c->is_safety ? "safety" : "liveness");
  if (labels == WL_TEMPLATE)
    for (uint16_t k = 0; k < c->candidate_count && len < (int)sizeof buf - 1;
         k++)
      len += snprintf(buf + len, sizeof buf - (size_t)len, ":%s",
                      c->candidates[k]);
  return strdup(buf);
}

static int cstr_cmp(const void *a, const void *b) {
  return strcmp(*(const char *const *)a, *(const char *const *)b);
}

// ---------------------------------------------------------------------------
// WL computation
// ---------------------------------------------------------------------------

WlFeatures *wl_compute(const ConstraintCover *cov, int rounds,
                       WlLabels labels) {
  WlFeatures *f = calloc(1, sizeof *f);
  if (!f)
    return nullptr;
  f->depth = rounds;
  f->labels = labels;

  uint32_t K = cov->count;
  uint32_t A = cov->aps.count;
  uint32_t N = K + A;

  Hist hist;
  hist_init(&hist);

  if (N == 0) {
    f->entries = nullptr;
    f->count = 0;
    return f;
  }

  // Build typed adjacency from the cover (same edges as the GSNF emitter).
  Adj *adj = calloc(N, sizeof(Adj));
  for (uint32_t i = 0; i < K; i++) {
    const Constraint *c = &cov->items[i];
    for (uint32_t a = 0; a < A; a++)
      if (apset_test(&c->inputs, a) || apset_test(&c->outputs, a))
        add_edge(adj, i, K + a, "occurs_in");
    if (c->resp_guard >= 0)
      add_edge(adj, i, K + (uint32_t)c->resp_guard, "response_guard");
    if (c->resp_target >= 0)
      add_edge(adj, i, K + (uint32_t)c->resp_target, "response_target");
    if (c->has_mutex)
      for (uint32_t a = 0; a < A; a++)
        if (apset_test(&c->mutex_members, a))
          add_edge(adj, i, K + a, "mutex_member");
  }

  // Round 0: base colors.
  char **cur = malloc(N * sizeof(char *));
  for (uint32_t v = 0; v < N; v++) {
    cur[v] = base_color(cov, v, K, labels);
    char key[300];
    snprintf(key, sizeof key, "0:%s", cur[v]);
    hist_add(&hist, key);
  }

  // Refinement rounds.
  for (int r = 1; r <= rounds; r++) {
    char **next = malloc(N * sizeof(char *));
    for (uint32_t v = 0; v < N; v++) {
      // neighbour tuples "type|color", sorted for canonicality
      uint32_t d = adj[v].n;
      char **tup = malloc((d ? d : 1) * sizeof(char *));
      for (uint32_t e = 0; e < d; e++) {
        const char *ty = adj[v].type[e];
        const char *nc = cur[adj[v].nbr[e]];
        size_t L = strlen(ty) + 1 + strlen(nc) + 1;
        char *s = malloc(L);
        snprintf(s, L, "%s|%s", ty, nc);
        tup[e] = s;
      }
      qsort(tup, d, sizeof(char *), cstr_cmp);

      // hash own color + sorted neighbour multiset
      char *buf;
      size_t sz;
      FILE *ms = open_memstream(&buf, &sz);
      fputs(cur[v], ms);
      fputc('\x1f', ms);
      for (uint32_t e = 0; e < d; e++) {
        fputs(tup[e], ms);
        fputc('\x1e', ms);
      }
      fclose(ms);
      uint64_t h = fnv1a(buf, sz);
      free(buf);
      for (uint32_t e = 0; e < d; e++)
        free(tup[e]);
      free(tup);

      char *color = malloc(17);
      snprintf(color, 17, "%016llx", (unsigned long long)h);
      next[v] = color;

      char key[64];
      snprintf(key, sizeof key, "%d:%s", r, color);
      hist_add(&hist, key);
    }
    for (uint32_t v = 0; v < N; v++)
      free(cur[v]);
    free(cur);
    cur = next;
  }

  for (uint32_t v = 0; v < N; v++)
    free(cur[v]);
  free(cur);
  for (uint32_t v = 0; v < N; v++) {
    free(adj[v].nbr);
    free(adj[v].type);
  }
  free(adj);

  // Move the histogram into a sorted entry array (transfers key ownership).
  f->entries = malloc((hist.count ? hist.count : 1) * sizeof(WlEntry));
  for (uint32_t i = 0; i < hist.count; i++)
    f->entries[i] = (WlEntry){.key = hist.keys[i], .count = hist.cnts[i]};
  f->count = hist.count;
  free(hist.keys);
  free(hist.cnts);
  free(hist.buckets);
  qsort(f->entries, f->count, sizeof(WlEntry), entry_cmp);
  return f;
}

void wl_features_free(WlFeatures *f) {
  if (!f)
    return;
  for (uint32_t i = 0; i < f->count; i++)
    free(f->entries[i].key);
  free(f->entries);
  free(f);
}

static const char *labels_name(WlLabels l) {
  return l == WL_BASIC ? "basic" : l == WL_TEMPLATE ? "template" : "synthesis";
}

void wl_features_emit(FILE *out, const WlFeatures *f, const char *source) {
  fprintf(out, "c WL features for %s\n", source);
  fprintf(out, "p wl %d %s\n", f->depth, labels_name(f->labels));
  for (uint32_t i = 0; i < f->count; i++)
    fprintf(out, "v %u %s\n", f->entries[i].count, f->entries[i].key);
}

// ---------------------------------------------------------------------------
// Kernels (merge-join over the sorted histograms)
// ---------------------------------------------------------------------------

double wl_kernel(const WlFeatures *a, const WlFeatures *b, Kernel k) {
  double dot = 0, na = 0, nb = 0, inter = 0, uni = 0;
  uint32_t i = 0, j = 0;
  while (i < a->count || j < b->count) {
    int c;
    if (i >= a->count)
      c = 1;
    else if (j >= b->count)
      c = -1;
    else
      c = strcmp(a->entries[i].key, b->entries[j].key);
    uint32_t av = 0, bv = 0;
    if (c < 0) {
      av = a->entries[i++].count;
    } else if (c > 0) {
      bv = b->entries[j++].count;
    } else {
      av = a->entries[i++].count;
      bv = b->entries[j++].count;
    }
    dot += (double)av * (double)bv;
    na += (double)av * (double)av;
    nb += (double)bv * (double)bv;
    inter += av < bv ? av : bv;
    uni += av > bv ? av : bv;
  }
  switch (k) {
  case KERNEL_DOT:
    return dot;
  case KERNEL_COSINE:
    return (na > 0 && nb > 0) ? dot / (sqrt(na) * sqrt(nb)) : 0.0;
  case KERNEL_JACCARD:
    return uni > 0 ? inter / uni : 0.0;
  }
  return 0.0;
}
