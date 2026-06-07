// NOLINTNEXTLINE(cert-dcl37-c)
#define _POSIX_C_SOURCE 200809L
#include "tlsf/aiger.h"

#include <stdlib.h>
#include <string.h>

typedef struct {
  char *name;
  uint32_t var;
} Input;
typedef struct {
  uint32_t var, next, reset;
} Latch;
typedef struct {
  uint32_t var, r0, r1;
} And;
typedef struct {
  char *name;
  uint32_t lit;
} Named;

struct Aig {
  uint32_t nextvar; // running variable counter (var 0 is the constant)
  Input *ins;
  uint32_t nin, in_cap;
  Latch *lat;
  uint32_t nlat, lat_cap;
  And *ands;
  uint32_t nand, and_cap;
  Named *outs;
  uint32_t nout, out_cap;
  Named *sig; // available signals (name -> lit) for lookups
  uint32_t nsig, sig_cap;
};

#define GROW(arr, cap, n)                                                      \
  do {                                                                         \
    if ((n) == (cap)) {                                                        \
      (cap) = (cap) ? (cap) * 2 : 8;                                           \
      void *grown_ = realloc((arr), (cap) * sizeof *(arr));                    \
      (arr) = grown_;                                                          \
    }                                                                          \
  } while (0)

Aig *aig_new(void) { return calloc(1, sizeof(Aig)); }

void aig_free(Aig *g) {
  if (!g)
    return;
  for (uint32_t i = 0; i < g->nin; i++)
    free(g->ins[i].name);
  for (uint32_t i = 0; i < g->nout; i++)
    free(g->outs[i].name);
  for (uint32_t i = 0; i < g->nsig; i++)
    free(g->sig[i].name);
  free(g->ins);
  free(g->lat);
  free(g->ands);
  free(g->outs);
  free(g->sig);
  free(g);
}

static void reg_sig(Aig *g, const char *name, uint32_t lit) {
  GROW(g->sig, g->sig_cap, g->nsig);
  g->sig[g->nsig].name = strdup(name);
  g->sig[g->nsig].lit = lit;
  g->nsig++;
}

uint32_t aig_lookup(const Aig *g, const char *name) {
  for (uint32_t i = 0; i < g->nsig; i++)
    if (strcmp(g->sig[i].name, name) == 0)
      return g->sig[i].lit;
  return UINT32_MAX;
}

bool aig_has_output(const Aig *g, const char *name) {
  for (uint32_t i = 0; i < g->nout; i++)
    if (strcmp(g->outs[i].name, name) == 0)
      return true;
  return false;
}

uint32_t aig_input(Aig *g, const char *name) {
  uint32_t var = ++g->nextvar;
  uint32_t lit = var * 2;
  GROW(g->ins, g->in_cap, g->nin);
  g->ins[g->nin].name = strdup(name);
  g->ins[g->nin].var = var;
  g->nin++;
  reg_sig(g, name, lit);
  return lit;
}

uint32_t aig_and(Aig *g, uint32_t a, uint32_t b) {
  if (a == AIG_FALSE || b == AIG_FALSE)
    return AIG_FALSE;
  if (a == AIG_TRUE)
    return b;
  if (b == AIG_TRUE)
    return a;
  if (a == b)
    return a;
  if (a == (b ^ 1u))
    return AIG_FALSE;
  uint32_t var = ++g->nextvar;
  GROW(g->ands, g->and_cap, g->nand);
  g->ands[g->nand].var = var;
  g->ands[g->nand].r0 = a;
  g->ands[g->nand].r1 = b;
  g->nand++;
  return var * 2;
}

uint32_t aig_or(Aig *g, uint32_t a, uint32_t b) {
  return aig_not(aig_and(g, aig_not(a), aig_not(b)));
}

void aig_set_output(Aig *g, const char *name, uint32_t lit) {
  GROW(g->outs, g->out_cap, g->nout);
  g->outs[g->nout].name = strdup(name);
  g->outs[g->nout].lit = lit;
  g->nout++;
  reg_sig(g, name, lit);
}

void aig_strip_output_prefix(Aig *g, const char *prefix) {
  size_t n = strlen(prefix);
  for (uint32_t i = 0; i < g->nout; i++) {
    if (strncmp(g->outs[i].name, prefix, n) != 0)
      continue;
    char *stripped = strdup(g->outs[i].name + n);
    if (!stripped)
      continue;
    free(g->outs[i].name);
    g->outs[i].name = stripped;
    reg_sig(g, stripped, g->outs[i].lit);
  }
}

uint32_t aig_compile(Aig *g, const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
    return AIG_TRUE;
  case NODE_FALSE:
    return AIG_FALSE;
  case NODE_AP:
    return aig_lookup(g, n->name);
  case NODE_NOT: {
    uint32_t a = aig_compile(g, n->arg);
    return a == UINT32_MAX ? a : aig_not(a);
  }
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV: {
    uint32_t a = aig_compile(g, n->lhs), b = aig_compile(g, n->rhs);
    if (a == UINT32_MAX || b == UINT32_MAX)
      return UINT32_MAX;
    switch (n->kind) {
    case NODE_AND:
      return aig_and(g, a, b);
    case NODE_OR:
      return aig_or(g, a, b);
    case NODE_IMPL:
      return aig_or(g, aig_not(a), b);
    default: // EQUIV
      return aig_and(g, aig_or(g, aig_not(a), b), aig_or(g, a, aig_not(b)));
    }
  }
  default:
    return UINT32_MAX; // not Boolean
  }
}

// ---------------------------------------------------------------------------
// Reader
// ---------------------------------------------------------------------------

// Parse up to `max` unsigned ints from `s`; returns how many were read.
static uint32_t parse_uints(const char *s, uint32_t *out, uint32_t max) {
  uint32_t n = 0;
  while (n < max) {
    char *end;
    unsigned long v = strtoul(s, &end, 10);
    if (end == s)
      break;
    out[n++] = (uint32_t)v;
    s = end;
  }
  return n;
}

Aig *aig_read_aag(FILE *in) {
  char line[8192];
  // Skip a leading REALIZABLE/UNREALIZABLE verdict line if present.
  long start = ftell(in);
  if (!fgets(line, sizeof line, in))
    return nullptr;
  if (strncmp(line, "aag ", 4) != 0) {
    if (strncmp(line, "REALIZABLE", 10) != 0 && start >= 0)
      fseek(in, start, SEEK_SET); // not an aag and not a verdict; rewind
    if (!fgets(line, sizeof line, in))
      return nullptr;
  }
  uint32_t hdr[5];
  if (strncmp(line, "aag ", 4) != 0 || parse_uints(line + 4, hdr, 5) != 5)
    return nullptr;
  uint32_t M = hdr[0], I = hdr[1], L = hdr[2], O = hdr[3], A = hdr[4];

  Aig *g = aig_new();
  if (!g)
    return nullptr;
  g->nextvar = M;
  uint32_t *outlits = O ? malloc(O * sizeof(uint32_t)) : nullptr;

  for (uint32_t i = 0; i < I; i++) {
    uint32_t lit;
    if (!fgets(line, sizeof line, in) || parse_uints(line, &lit, 1) != 1)
      goto fail;
    GROW(g->ins, g->in_cap, g->nin);
    g->ins[g->nin].var = lit / 2;
    g->ins[g->nin].name = nullptr; // filled from the symbol table
    g->nin++;
  }
  for (uint32_t i = 0; i < L; i++) {
    uint32_t t[3] = {0, 0, 0};
    if (!fgets(line, sizeof line, in) || parse_uints(line, t, 3) < 2)
      goto fail;
    GROW(g->lat, g->lat_cap, g->nlat);
    g->lat[g->nlat++] = (Latch){t[0] / 2, t[1], t[2]};
  }
  for (uint32_t i = 0; i < O; i++)
    if (!fgets(line, sizeof line, in) || parse_uints(line, &outlits[i], 1) != 1)
      goto fail;
  for (uint32_t i = 0; i < A; i++) {
    uint32_t t[3];
    if (!fgets(line, sizeof line, in) || parse_uints(line, t, 3) != 3)
      goto fail;
    GROW(g->ands, g->and_cap, g->nand);
    g->ands[g->nand++] = (And){t[0] / 2, t[1], t[2]};
  }
  // Symbol table: i<k> name / o<k> name / l<k> name (others ignored).
  char **onames = O ? calloc(O, sizeof(char *)) : nullptr;
  while (fgets(line, sizeof line, in)) {
    char kind = line[0];
    if (kind == 'c')
      break; // comment section
    if (kind != 'i' && kind != 'o' && kind != 'l')
      continue;
    char *end;
    unsigned long idx = strtoul(line + 1, &end, 10);
    if (end == line + 1)
      continue;
    while (*end == ' ' || *end == '\t')
      end++;
    char *nl = strpbrk(end, " \t\r\n");
    if (nl)
      *nl = '\0';
    if (*end == '\0')
      continue;
    if (kind == 'i' && idx < g->nin)
      g->ins[idx].name = strdup(end);
    else if (kind == 'o' && idx < O && onames)
      onames[idx] = strdup(end);
  }
  for (uint32_t i = 0; i < g->nin; i++)
    if (g->ins[i].name)
      reg_sig(g, g->ins[i].name, g->ins[i].var * 2);
  for (uint32_t i = 0; i < O; i++) {
    char tmp[32];
    const char *nm = onames && onames[i]
                         ? onames[i]
                         : (snprintf(tmp, sizeof tmp, "o%u", i), tmp);
    aig_set_output(g, nm, outlits[i]);
  }
  if (onames)
    for (uint32_t i = 0; i < O; i++)
      free(onames[i]);
  free(onames);
  free(outlits);
  return g;

fail:
  free(outlits);
  aig_free(g);
  return nullptr;
}

// ---------------------------------------------------------------------------
// Merge
// ---------------------------------------------------------------------------

bool aig_merge(Aig *dst, const Aig *src) {
  uint32_t *vmap =
      calloc(src->nextvar + 1, sizeof(uint32_t)); // src var -> dst var
  if (!vmap)
    return false;
  for (uint32_t i = 0; i < src->nin; i++) {
    uint32_t dl =
        src->ins[i].name ? aig_lookup(dst, src->ins[i].name) : UINT32_MAX;
    if (dl == UINT32_MAX) {
      free(vmap);
      return false; // a cluster input is not a spec signal
    }
    vmap[src->ins[i].var] = dl / 2;
  }
  for (uint32_t i = 0; i < src->nlat; i++)
    vmap[src->lat[i].var] = ++dst->nextvar;
  for (uint32_t i = 0; i < src->nand; i++)
    vmap[src->ands[i].var] = ++dst->nextvar;

#define REMAP(lit) ((lit) < 2 ? (lit) : ((vmap[(lit) / 2] * 2) | ((lit) & 1u)))
  for (uint32_t i = 0; i < src->nlat; i++) {
    GROW(dst->lat, dst->lat_cap, dst->nlat);
    dst->lat[dst->nlat++] = (Latch){vmap[src->lat[i].var],
                                    REMAP(src->lat[i].next), src->lat[i].reset};
  }
  for (uint32_t i = 0; i < src->nand; i++) {
    GROW(dst->ands, dst->and_cap, dst->nand);
    dst->ands[dst->nand++] = (And){
        vmap[src->ands[i].var], REMAP(src->ands[i].r0), REMAP(src->ands[i].r1)};
  }
  for (uint32_t i = 0; i < src->nout; i++)
    aig_set_output(dst, src->outs[i].name, REMAP(src->outs[i].lit));
#undef REMAP
  free(vmap);
  return true;
}

// ---------------------------------------------------------------------------
// Writer (renumber to canonical inputs / latches / ands order)
// ---------------------------------------------------------------------------

void aig_write_aag(FILE *out, const Aig *g) {
  uint32_t M = g->nin + g->nlat + g->nand;
  uint32_t *canon = calloc(g->nextvar + 1, sizeof(uint32_t));
  for (uint32_t k = 0; k < g->nin; k++)
    canon[g->ins[k].var] = k + 1;
  for (uint32_t k = 0; k < g->nlat; k++)
    canon[g->lat[k].var] = g->nin + 1 + k;
  for (uint32_t k = 0; k < g->nand; k++)
    canon[g->ands[k].var] = g->nin + g->nlat + 1 + k;
#define WLIT(lit) ((lit) < 2 ? (lit) : ((canon[(lit) / 2] * 2) | ((lit) & 1u)))

  fprintf(out, "aag %u %u %u %u %u\n", M, g->nin, g->nlat, g->nout, g->nand);
  for (uint32_t k = 0; k < g->nin; k++)
    fprintf(out, "%u\n", (k + 1) * 2);
  for (uint32_t k = 0; k < g->nlat; k++) {
    uint32_t v = (g->nin + 1 + k) * 2;
    if (g->lat[k].reset)
      fprintf(out, "%u %u %u\n", v, WLIT(g->lat[k].next), g->lat[k].reset);
    else
      fprintf(out, "%u %u\n", v, WLIT(g->lat[k].next));
  }
  for (uint32_t k = 0; k < g->nout; k++)
    fprintf(out, "%u\n", WLIT(g->outs[k].lit));
  for (uint32_t k = 0; k < g->nand; k++)
    fprintf(out, "%u %u %u\n", (g->nin + g->nlat + 1 + k) * 2,
            WLIT(g->ands[k].r0), WLIT(g->ands[k].r1));
  for (uint32_t k = 0; k < g->nin; k++)
    if (g->ins[k].name)
      fprintf(out, "i%u %s\n", k, g->ins[k].name);
  for (uint32_t k = 0; k < g->nout; k++)
    fprintf(out, "o%u %s\n", k, g->outs[k].name);
#undef WLIT
  free(canon);
}
