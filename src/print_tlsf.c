#include "tlsf/print_tlsf.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Internal: formula printer in TLSF syntax
// (identical operators to ltlxba except TLSF uses ! not !, same symbols)
// ---------------------------------------------------------------------------

static void print_formula(FILE *out, const Node *n) {
  assert(n);
  switch (n->kind) {
  case NODE_TRUE:  fprintf(out, "true");  return;
  case NODE_FALSE: fprintf(out, "false"); return;
  case NODE_AP:    fprintf(out, "%s", n->name); return;

  case NODE_NOT:
    fprintf(out, "!("); print_formula(out, n->arg); fprintf(out, ")");
    return;
  case NODE_AND:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " && "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;
  case NODE_OR:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " || "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;
  case NODE_IMPL:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " -> "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;
  case NODE_EQUIV:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " <-> "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;

  case NODE_X:       fprintf(out, "X ("); print_formula(out, n->arg); fprintf(out, ")"); return;
  case NODE_X_STRONG:fprintf(out, "X[!] ("); print_formula(out, n->arg); fprintf(out, ")"); return;
  case NODE_F:       fprintf(out, "F ("); print_formula(out, n->arg); fprintf(out, ")"); return;
  case NODE_G:       fprintf(out, "G ("); print_formula(out, n->arg); fprintf(out, ")"); return;

  case NODE_U:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " U "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;
  case NODE_R:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " R "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;
  case NODE_W:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " W "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;
  case NODE_M:
    fprintf(out, "("); print_formula(out, n->lhs);
    fprintf(out, " M "); print_formula(out, n->rhs);
    fprintf(out, ")"); return;

  default:
    assert(false && "print_tlsf: unexpected node kind");
  }
}

static void print_formula_list(FILE *out, const FormulaList *list,
                                const char *subsection) {
  if (list->count == 0)
    return;
  fprintf(out, "    %s {\n", subsection);
  for (uint32_t i = 0; i < list->count; i++) {
    fprintf(out, "      ");
    print_formula(out, list->formulas[i]);
    fprintf(out, ";\n");
  }
  fprintf(out, "    }\n\n");
}

// ---------------------------------------------------------------------------
// Semantics / target string helpers
// ---------------------------------------------------------------------------

static const char *semantics_str(Semantics s) {
  switch (s) {
  case SEM_MEALY:        return "Mealy";
  case SEM_MOORE:        return "Moore";
  case SEM_MEALY_STRICT: return "Strict,Mealy";
  case SEM_MOORE_STRICT: return "Strict,Moore";
  case SEM_MEALY_FINITE: return "Finite,Mealy";
  case SEM_MOORE_FINITE: return "Finite,Moore";
  }
  return "Mealy";
}

static const char *target_str(Target t) {
  return t == TARGET_MOORE ? "Moore" : "Mealy";
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

void print_tlsf(FILE *out, const TlsfSpec *spec) {
  // ---- INFO block ----
  fprintf(out, "INFO {\n");

  if (spec->info.title)
    fprintf(out, "  TITLE:       \"%s\";\n", spec->info.title);
  if (spec->info.description)
    fprintf(out, "  DESCRIPTION: \"%s\";\n", spec->info.description);

  fprintf(out, "  SEMANTICS:   %s;\n", semantics_str(spec->info.semantics));
  fprintf(out, "  TARGET:      %s;\n", target_str(spec->info.target));

  if (spec->info.tag_count > 0) {
    fprintf(out, "  TAGS:        ");
    for (uint16_t i = 0; i < spec->info.tag_count; i++) {
      if (i > 0) fprintf(out, ", ");
      fprintf(out, "\"%s\"", spec->info.tags[i]);
    }
    fprintf(out, ";\n");
  }

  fprintf(out, "}\n\n");

  // ---- MAIN block ----
  fprintf(out, "MAIN {\n\n");

  // INPUTS
  fprintf(out, "  INPUTS {\n");
  for (uint32_t i = 0; i < spec->input_count; i++) {
    const SignalDecl *sd = &spec->inputs[i];
    if (sd->is_bus)
      fprintf(out, "    %s[%u..%u];\n", sd->name, sd->bus_lo, sd->bus_hi);
    else
      fprintf(out, "    %s;\n", sd->name);
  }
  fprintf(out, "  }\n\n");

  // OUTPUTS
  fprintf(out, "  OUTPUTS {\n");
  for (uint32_t i = 0; i < spec->output_count; i++) {
    const SignalDecl *sd = &spec->outputs[i];
    if (sd->is_bus)
      fprintf(out, "    %s[%u..%u];\n", sd->name, sd->bus_lo, sd->bus_hi);
    else
      fprintf(out, "    %s;\n", sd->name);
  }
  fprintf(out, "  }\n\n");

  // Formula subsections
  print_formula_list(out, &spec->initially, "INITIALLY");
  print_formula_list(out, &spec->preset,    "PRESET");
  print_formula_list(out, &spec->require,   "REQUIRE");
  print_formula_list(out, &spec->assert_,   "ASSERT");
  print_formula_list(out, &spec->assume,    "ASSUME");
  print_formula_list(out, &spec->guarantee, "GUARANTEE");

  fprintf(out, "}\n");
}
