#define _GNU_SOURCE
#include "tlsf/ast.h"
#include "tlsf/dpa.h"
#include "dpa_buchi.h"
#include "sha256.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Offline protocol and CI hash gate share this serializer. A request is:
// TV1 parity|buchi default|general AP-count AP-names... prefix-formula
// AP i is bit i in each increasing valuation. States are discovered by BFS
// in that letter order. Every row is complete, sorted by its letter number.
static bool token(FILE *in, char s[4096]) {
  return fscanf(in, "%4095s", s) == 1;
}

static Node *formula(FILE *in, Arena *arena, unsigned depth) {
  char s[4096];
  if (depth > 1024 || !token(in, s))
    return NULL;
  if (!strcmp(s, "1"))
    return node_true(arena);
  if (!strcmp(s, "0"))
    return node_false(arena);
  if (s[0] == '$' && s[1]) {
    char *name = ARENA_ALLOC_N(arena, char, strlen(s));
    if (!name)
      return NULL;
    strcpy(name, s + 1);
    return node_ap(arena, name);
  }
  if (strlen(s) != 1 || !strchr("!XxFG&|ie^URWM", s[0]))
    return NULL;
  Node *a = formula(in, arena, depth + 1);
  if (!a)
    return NULL;
  switch (s[0]) {
  case '!':
    return node_not(arena, a);
  case 'X':
    return node_x(arena, a);
  case 'x':
    return node_x_strong(arena, a);
  case 'F':
    return node_f(arena, a);
  case 'G':
    return node_g(arena, a);
  default:
    break;
  }
  Node *b = formula(in, arena, depth + 1);
  if (!b)
    return NULL;
  switch (s[0]) {
  case '&':
    return node_and(arena, a, b);
  case '|':
    return node_or(arena, a, b);
  case 'i':
    return node_impl(arena, a, b);
  case 'e':
    return node_equiv(arena, a, b);
  case '^':
    return node_not(arena, node_equiv(arena, a, b));
  case 'U':
    return node_u(arena, a, b);
  case 'R':
    return node_r(arena, a, b);
  case 'W':
    return node_w(arena, a, b);
  case 'M':
    return node_m(arena, a, b);
  default:
    return NULL;
  }
}

static void prefix(FILE *out, const TlsfAstNode *f) {
  static const char *const ops[] = {"1", "0", "",  "!", "&", "|", "i", "e",
                                    "X", "x", "F", "G", "U", "R", "W", "M"};
  TlsfAstKind k = tlsf_ast_node_kind(f);
  if (k == TLSF_AST_AP)
    fprintf(out, "$%s ", tlsf_ast_node_ap_name(f));
  else
    fprintf(out, "%s ", ops[k]);
  for (uint32_t i = 0; i < tlsf_ast_node_child_count(f); ++i)
    prefix(out, tlsf_ast_node_child(f, i));
}

static bool holds(TlsfDpa *c, uint32_t label, uint32_t mask) {
  const TlsfDpaLabelNode *n = tlsf_dpa_label_node(c, label);
  while (n && n->kind == TLSF_DPA_DECISION) {
    if (n->ap >= 16)
      return false;
    n = tlsf_dpa_label_node(c, mask & (1u << n->ap) ? n->high : n->low);
  }
  return n && n->kind == TLSF_DPA_TRUE;
}

static bool edge(TlsfDpa *c, uint32_t state, uint32_t mask,
                 TlsfDpaEdge *result) {
  const TlsfDpaEdge *edges;
  size_t count, matches = 0;
  if (tlsf_dpa_successors(c, state, &edges, &count).code != TLSF_DPA_OK)
    return false;
  for (size_t i = 0; i < count; ++i)
    if (holds(c, edges[i].label, mask)) {
      *result = edges[i];
      ++matches;
    }
  return matches == 1;
}

static int dump(FILE *in, FILE *out) {
  char magic[4096], kind[4096], admission[4096], extra[4096];
  unsigned aps = 0;
  if (!token(in, magic) || strcmp(magic, "TV1") || !token(in, kind) ||
      (strcmp(kind, "parity") && strcmp(kind, "buchi")) ||
      !token(in, admission) ||
      (strcmp(admission, "default") && strcmp(admission, "general")) ||
      fscanf(in, "%u", &aps) != 1 || aps > 16)
    return 2;
  char *names[16] = {0};
  Arena *arena = arena_new(4096);
  TlsfDpa *c = NULL;
  uint32_t *ids = NULL, *queue = NULL;
  int result = 2;
  if (!arena)
    goto done;
  for (unsigned i = 0; i < aps; ++i) {
    if (!token(in, extra) || !(names[i] = strdup(extra)))
      goto done;
    for (unsigned j = 0; j < i; ++j)
      if (!strcmp(names[i], names[j]))
        goto done;
  }
  Node *f = formula(in, arena, 0);
  if (!f || token(in, extra))
    goto done;
  TlsfDpaBudget budget = {.max_states = 10000,
                          .max_host_bytes = 256u << 20,
                          .bdd_nodes = 1u << 22,
                          .bdd_cache = 1u << 18,
                          .allow_unproved = !strcmp(admission, "general")};
  bool buchi = !strcmp(kind, "buchi");
  char klass;
  TlsfDpaStatus status =
      buchi
          ? dpa_buchi_create((const TlsfAstNode *)f, (const char *const *)names,
                             aps, &budget, &c, &klass)
          : tlsf_dpa_create((const TlsfAstNode *)f, (const char *const *)names,
                            aps, NULL, 0, &budget, &c);
  if (status.code == TLSF_DPA_DECLINED &&
      status.reason == TLSF_DPA_UNSUPPORTED) {
    fprintf(out, "TV1 %s %s %u\n", kind, admission, aps);
    for (unsigned i = 0; i < aps; ++i)
      fprintf(out, "%s\n", names[i]);
    prefix(out, (const TlsfAstNode *)f);
    fputs("\ndeclined unsupported\n", out);
    result = 77;
    goto done;
  }
  if (status.code == TLSF_DPA_OK)
    status = tlsf_dpa_expand(c);
  if (status.code != TLSF_DPA_OK) {
    fprintf(stderr, "C construction status %d reason %d\n", (int)status.code,
            (int)status.reason);
    goto done;
  }
  if (tlsf_dpa_ap_count(c) != aps)
    goto done;
  for (unsigned i = 0; i < aps; ++i)
    if (strcmp(names[i], tlsf_dpa_ap_name(c, i)))
      goto done;
  size_t count = tlsf_dpa_state_count(c);
  ids = malloc(count * sizeof *ids);
  queue = malloc(count * sizeof *queue);
  if (!ids || !queue)
    goto done;
  for (size_t i = 0; i < count; ++i)
    ids[i] = UINT32_MAX;
  size_t reached = 1;
  queue[0] = tlsf_dpa_initial(c);
  ids[queue[0]] = 0;
  for (size_t i = 0; i < reached; ++i)
    for (uint32_t mask = 0; mask < (1u << aps); ++mask) {
      TlsfDpaEdge e;
      if (!edge(c, queue[i], mask, &e) || e.successor >= count)
        goto done;
      if (ids[e.successor] == UINT32_MAX) {
        ids[e.successor] = (uint32_t)reached;
        queue[reached++] = e.successor;
      }
    }
  fprintf(out, "TV1 %s %s %u\n", kind, admission, aps);
  for (unsigned i = 0; i < aps; ++i)
    fprintf(out, "%s\n", names[i]);
  prefix(out, (const TlsfAstNode *)f);
  fprintf(out, "\nstates %zu\n", reached);
  for (size_t i = 0; i < reached; ++i) {
    TlsfDpaEdge first;
    if (!edge(c, queue[i], 0, &first))
      goto done;
    fprintf(out, "%u\n", buchi ? first.priority : 0);
  }
  for (size_t i = 0; i < reached; ++i)
    for (uint32_t mask = 0; mask < (1u << aps); ++mask) {
      TlsfDpaEdge e;
      if (!edge(c, queue[i], mask, &e) || (buchi && (e.priority > 1)))
        goto done;
      // The state-based acceptance is required to be uniform across a row.
      if (buchi) {
        TlsfDpaEdge first;
        if (!edge(c, queue[i], 0, &first) || e.priority != first.priority)
          goto done;
      }
      fprintf(out, "%zu %u %u %u\n", i, mask, ids[e.successor], e.priority);
    }
  fputs("end\n", out);
  result = ferror(out) ? 2 : 0;
done:
  for (unsigned i = 0; i < aps; ++i)
    free(names[i]);
  free(queue);
  free(ids);
  tlsf_dpa_free(c);
  arena_free(arena);
  return result;
}

int main(int argc, char **argv) {
  if (argc == 2) {
    FILE *in = fopen(argv[1], "rb");
    if (!in)
      return 2;
    int status = dump(in, stdout);
    fclose(in);
    return status;
  }
  if (argc == 3 && !strcmp(argv[1], "--golden")) {
    FILE *in = fopen(argv[2], "rb");
    if (!in)
      return 2;
    char *line = NULL;
    size_t capacity = 0, count = 0;
    int status = 0;
    while (getline(&line, &capacity, in) >= 0) {
      char *tab = strchr(line, '\t');
      if (!tab || tab - line != 64) {
        status = 2;
        break;
      }
      *tab = 0;
      char *separator = strchr(tab + 1, '\t');
      if (!separator) {
        status = 2;
        break;
      }
      *separator = 0;
      int expected = !strcmp(tab + 1, "pass")       ? 0
                     : !strcmp(tab + 1, "declined") ? 77
                                                    : -1;
      if (expected < 0) {
        status = 2;
        break;
      }
      char *request = separator + 1, *bytes = NULL;
      size_t length = 0;
      FILE *source = fmemopen(request, strlen(request), "r");
      FILE *target = open_memstream(&bytes, &length);
      if (!source || !target) {
        status = 2;
        break;
      }
      int code = dump(source, target);
      fclose(source);
      fclose(target);
      char hash[65];
      sha256_hex(bytes, length, hash);
      free(bytes);
      if (code != expected || strcmp(hash, line)) {
        fprintf(stderr, "translation golden mismatch at row %zu: %s", count + 1,
                request);
        status = 1;
        break;
      }
      ++count;
    }
    free(line);
    fclose(in);
    if (!count)
      status = 1;
    if (!status)
      printf("%zu translation hashes match\n", count);
    return status;
  }
  fputs("usage: dpa_dump REQUEST | --golden GOLDENS.tsv\n", stderr);
  return 2;
}
