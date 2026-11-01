// Optional offline mode of dpa_admission; no changes to its normal inventory.
// Usage: --expand --measure {export,default,research} SOURCE PREFIX
// The caller supplies the hard deadline and total memory limit.
#ifndef DPA_STATE_COUNTS_H
#define DPA_STATE_COUNTS_H

static FILE *counts_file(const char *prefix, const char *suffix) {
  size_t n = strlen(prefix) + strlen(suffix) + 1;
  char *path = malloc(n);
  if (!path)
    return nullptr;
  snprintf(path, n, "%s%s", prefix, suffix);
  FILE *out = fopen(path, "w");
  free(path);
  return out;
}

static bool counts_formula(FILE *out, const TlsfAstNode *node);

// Flatten associative Boolean nodes while printing. Nested binary conjunctions
// make Owl's parser repeatedly copy growing operand lists on large objectives.
static bool counts_operands(FILE *out, const TlsfAstNode *node,
                            TlsfAstKind kind, const char *op) {
  if (tlsf_ast_node_kind(node) != kind)
    return counts_formula(out, node);
  if (!counts_operands(out, tlsf_ast_node_child(node, 0), kind, op))
    return false;
  fprintf(out, " %s ", op);
  return counts_operands(out, tlsf_ast_node_child(node, 1), kind, op);
}

// Print the actual lowercase AST passed to tlsf_dpa_create. Parenthesise every
// operator group and quote every AP: no second normalization or precedence
// guess.
static bool counts_formula(FILE *out, const TlsfAstNode *node) {
  static const char *const ops[] = {"true", "false", nullptr, "!", "&", "|",
                                    "->",   "<->",   "X",     "X", "F", "G",
                                    "U",    "R",     "W",     "M"};
  TlsfAstKind kind = tlsf_ast_node_kind(node);
  if (kind >= TLSF_AST_KIND_COUNT)
    return false;
  if (kind == TLSF_AST_AP) {
    const char *name = tlsf_ast_node_ap_name(node);
    if (strpbrk(name, "\"\\\n\r\t"))
      return false;
    fprintf(out, "\"%s\"", name);
    return !ferror(out);
  }
  unsigned children = tlsf_ast_node_child_count(node);
  if (!children) {
    fputs(ops[kind], out);
    return !ferror(out);
  }
  fputc('(', out);
  if (kind == TLSF_AST_AND || kind == TLSF_AST_OR) {
    bool ok = counts_operands(out, node, kind, ops[kind]);
    fputc(')', out);
    return ok && !ferror(out);
  }
  if (children == 1)
    fprintf(out, "%s ", ops[kind]);
  if (!counts_formula(out, tlsf_ast_node_child(node, 0)))
    return false;
  if (children == 2) {
    fprintf(out, " %s ", ops[kind]);
    if (!counts_formula(out, tlsf_ast_node_child(node, 1)))
      return false;
  }
  fputc(')', out);
  return !ferror(out);
}

static bool counts_export(TlsfConversionResult *r, const char *prefix) {
  const TlsfAstNode *root = tlsf_ast_root(r->ast);
  FILE *out = counts_file(prefix, ".ltl");
  if (!out)
    return false;
  bool ok = counts_formula(out, root);
  fputc('\n', out);
  if (fclose(out) || !ok)
    return false;
  out = counts_file(prefix, ".aps");
  if (!out)
    return false;
  for (uint32_t i = 0; i < r->n_inputs + r->n_outputs; ++i)
    fprintf(out, "%s\n",
            i < r->n_inputs ? r->inputs[i] : r->outputs[i - r->n_inputs]);
  if (fclose(out))
    return false;
  out = counts_file(prefix, ".meta");
  if (!out)
    return false;
  fprintf(out, "%s\t%s\t%s\t%u\t%u\n", r->semantics, r->original_target,
          r->effective_target, r->n_inputs, r->n_outputs);
  if (fclose(out))
    return false;
  out = counts_file(prefix, ".owl.ltl");
  if (!out)
    return false;
  // Owl 21.0's CLI assigns APs by first occurrence. Its parser visits every
  // conjunct before Conjunction.of removes false, then Disjunction.of drops
  // the whole false disjunct. This sets the alphabet, including unused APs,
  // without changing the parsed formula. Check this with CheckOwlFormula.java.
  fputs("(false", out);
  for (uint32_t i = 0; i < r->n_inputs + r->n_outputs; ++i)
    fprintf(out, " & \"%s\"",
            i < r->n_inputs ? r->inputs[i] : r->outputs[i - r->n_inputs]);
  fputs(") | ", out);
  ok = counts_formula(out, root);
  fputc('\n', out);
  return fclose(out) == 0 && ok;
}

static int dpa_state_counts_main(int argc, char **argv) {
  if (argc != 3 || (strcmp(argv[0], "export") && strcmp(argv[0], "default") &&
                    strcmp(argv[0], "research")))
    return 2;
  FILE *fp = fopen(argv[1], "rb");
  if (!fp || fseek(fp, 0, SEEK_END))
    return 1;
  long length = ftell(fp);
  if (length < 0 || fseek(fp, 0, SEEK_SET))
    return 1;
  char *text = malloc((size_t)length + 1);
  if (!text || fread(text, 1, (size_t)length, fp) != (size_t)length)
    return 1;
  fclose(fp);
  text[length] = 0;
  TlsfConversionResult *r = tlsf_convert(text, "Mealy");
  free(text);
  if (!r || !counts_export(r, argv[2]))
    return 1;
  if (!strcmp(argv[0], "export")) {
    tlsf_conversion_result_free(r);
    return 0;
  }
  // No state/host cap or cooperative deadline. BDD storage is separate;
  // 2^24 nodes and the original default cache fit inside the external 4 GiB
  // scope. Intrinsic syntax/stack/priority limits still apply.
  TlsfDpaBudget budget = {.bdd_nodes = 1u << 24,
                          .bdd_cache = 1u << 16,
                          .allow_unproved = !strcmp(argv[0], "research")};
  TlsfDpa *c = nullptr;
  TlsfDpaStatus status = tlsf_dpa_create(
      tlsf_ast_root(r->ast), (const char *const *)r->inputs, r->n_inputs,
      (const char *const *)r->outputs, r->n_outputs, &budget, &c);
  if (status.code == TLSF_DPA_OK)
    status = tlsf_dpa_expand(c);
  if (status.code == TLSF_DPA_OK) {
    uint32_t max = tlsf_dpa_max_priority(c), used = 0;
    bool *seen = calloc((size_t)max + 1, sizeof *seen);
    if (!seen)
      return 1;
    for (size_t s = 0; s < tlsf_dpa_state_count(c); ++s) {
      const TlsfDpaEdge *edges;
      size_t n;
      if (tlsf_dpa_successors(c, (TlsfDpaState)s, &edges, &n).code !=
          TLSF_DPA_OK)
        return 1;
      for (size_t e = 0; e < n; ++e) {
        if (edges[e].priority > max)
          return 1;
        if (!seen[edges[e].priority]) {
          seen[edges[e].priority] = true;
          ++used;
        }
      }
    }
    free(seen);
    printf("%u\t%u\t%zu\t%u\t%u\n", (unsigned)status.code,
           (unsigned)status.reason, tlsf_dpa_state_count(c), max + 1, used);
  } else
    printf("%u\t%u\tNA\tNA\tNA\n", (unsigned)status.code,
           (unsigned)status.reason);
  fflush(stdout);
  tlsf_dpa_free(c);
  tlsf_conversion_result_free(r);
  return 0;
}
#endif
