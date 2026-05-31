#include "tlsf/print_tlsf.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Internal: formula printer in TLSF syntax
// (identical operators to ltlxba except TLSF uses ! not !, same symbols)
// ---------------------------------------------------------------------------

static void print_formula(FILE *out, const Node *n) {
  assert(n);
  switch (n->kind) {
  case NODE_TRUE:
    fprintf(out, "true");
    return;
  case NODE_FALSE:
    fprintf(out, "false");
    return;
  case NODE_AP:
    fprintf(out, "%s", n->name);
    return;

  case NODE_NOT:
    fprintf(out, "!(");
    print_formula(out, n->arg);
    fprintf(out, ")");
    return;
  case NODE_AND:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " && ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_OR:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " || ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_IMPL:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " -> ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_EQUIV:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " <-> ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;

  case NODE_X:
    fprintf(out, "X (");
    print_formula(out, n->arg);
    fprintf(out, ")");
    return;
  case NODE_X_STRONG:
    fprintf(out, "X[!] (");
    print_formula(out, n->arg);
    fprintf(out, ")");
    return;
  case NODE_F:
    fprintf(out, "F (");
    print_formula(out, n->arg);
    fprintf(out, ")");
    return;
  case NODE_G:
    fprintf(out, "G (");
    print_formula(out, n->arg);
    fprintf(out, ")");
    return;

  case NODE_U:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " U ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_R:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " R ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_W:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " W ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_M:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " M ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;

  // -- High-level nodes (present when the GLOBAL section is preserved, i.e.
  //    when re-emitting without full expansion) --
  case NODE_INT:
    fprintf(out, "%lld", (long long)n->ival);
    return;
  case NODE_INT_VAR:
    fprintf(out, "%s", n->name);
    return;
  case NODE_INT_ADD:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " + ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_INT_SUB:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " - ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_INT_MUL:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " * ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_INT_DIV:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " / ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_INT_MOD:
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " %% ");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  case NODE_INT_NEG:
    fprintf(out, "(- ");
    print_formula(out, n->arg);
    fprintf(out, ")");
    return;

  case NODE_SIZEOF:
    fprintf(out, "SIZEOF %s", n->sizeof_name);
    return;

  case NODE_BUS_INDEX:
    fprintf(out, "%s[", n->bus_name);
    print_formula(out, n->bus_index);
    fprintf(out, "]");
    return;

  case NODE_FORALL:
  case NODE_EXISTS:
    fprintf(out, "%s[", n->kind == NODE_FORALL ? "&&" : "||");
    print_formula(out, n->qlo);
    fprintf(out, " %s %s %s ", n->qlo_strict ? "<" : "<=", n->qvar,
            n->qhi_strict ? "<" : "<=");
    print_formula(out, n->qhi);
    fprintf(out, "] ");
    print_formula(out, n->qbody);
    return;

  case NODE_DEF_CALL:
    fprintf(out, "%s(", n->callee);
    for (uint16_t i = 0; i < n->call_argc; i++) {
      if (i > 0)
        fprintf(out, ", ");
      print_formula(out, n->call_args[i]);
    }
    fprintf(out, ")");
    return;

  case NODE_CMP_EQ:
  case NODE_CMP_NE:
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE: {
    static const char *ops[] = {"==", "!=", "<", "<=", ">", ">="};
    fprintf(out, "(");
    print_formula(out, n->lhs);
    fprintf(out, " %s ", ops[n->kind - NODE_CMP_EQ]);
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;
  }

  case NODE_ITE:
    print_formula(out, n->if_cond);
    fprintf(out, " : ");
    print_formula(out, n->if_then);
    fprintf(out, "  ");
    print_formula(out, n->if_else);
    return;

  case NODE_NEXT_N:
    fprintf(out, "X[");
    print_formula(out, n->lhs);
    fprintf(out, "] (");
    print_formula(out, n->rhs);
    fprintf(out, ")");
    return;

  default:
    assert(false && "print_tlsf: unexpected node kind");
  }
}

// Print one INPUTS/OUTPUTS subsection.  A bus prints its declared range; when
// the bounds are parametric expressions (non-expanded re-emission) those are
// printed faithfully, otherwise the resolved integer bounds are used.
static void print_signal_list(FILE *out, const char *subsection,
                              const SignalDecl *sigs, uint32_t count) {
  fprintf(out, "  %s {\n", subsection);
  for (uint32_t i = 0; i < count; i++) {
    const SignalDecl *sd = &sigs[i];
    if (!sd->is_bus) {
      fprintf(out, "    %s;\n", sd->name);
      continue;
    }
    fprintf(out, "    %s[", sd->name);
    if (sd->bus_lo_expr)
      print_formula(out, sd->bus_lo_expr);
    else
      fprintf(out, "%u", sd->bus_lo);
    fprintf(out, "..");
    if (sd->bus_hi_expr)
      print_formula(out, sd->bus_hi_expr);
    else
      fprintf(out, "%u", sd->bus_hi);
    fprintf(out, "];\n");
  }
  fprintf(out, "  }\n\n");
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
  case SEM_MEALY:
    return "Mealy";
  case SEM_MOORE:
    return "Moore";
  case SEM_MEALY_STRICT:
    return "Strict,Mealy";
  case SEM_MOORE_STRICT:
    return "Strict,Moore";
  case SEM_MEALY_FINITE:
    return "Finite,Mealy";
  case SEM_MOORE_FINITE:
    return "Finite,Moore";
  }
  return "Mealy";
}

static const char *target_str(Target t) {
  return t == TARGET_MOORE ? "Moore" : "Mealy";
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// GLOBAL section (parameters + definitions), preserved when re-emitting a
// non-expanded spec (e.g. for plain parameter substitution).
// ---------------------------------------------------------------------------

static void print_global(FILE *out, const TlsfSpec *spec) {
  if (spec->param_count == 0 && spec->def_count == 0)
    return;

  fprintf(out, "GLOBAL {\n\n");

  if (spec->param_count > 0) {
    fprintf(out, "  PARAMETERS {\n");
    for (uint16_t i = 0; i < spec->param_count; i++) {
      const ParamDecl *p = &spec->params[i];
      // `value` holds the default initially and any --param override applied
      // before printing; emit it when the parameter is bound to a value.
      if (p->has_default)
        fprintf(out, "    %s = %lld;\n", p->name, (long long)p->value);
      else
        fprintf(out, "    %s;\n", p->name);
    }
    fprintf(out, "  }\n\n");
  }

  if (spec->def_count > 0) {
    fprintf(out, "  DEFINITIONS {\n");
    for (uint16_t i = 0; i < spec->def_count; i++) {
      const DefDecl *d = &spec->defs[i];
      fprintf(out, "    %s", d->name);
      if (d->param_count > 0) {
        fprintf(out, "(");
        for (uint16_t j = 0; j < d->param_count; j++) {
          if (j > 0)
            fprintf(out, ", ");
          fprintf(out, "%s", d->params[j]);
        }
        fprintf(out, ")");
      }
      fprintf(out, " = ");
      print_formula(out, d->body);
      fprintf(out, ";\n");
    }
    fprintf(out, "  }\n\n");
  }

  fprintf(out, "}\n\n");
}

void print_tlsf(FILE *out, const TlsfSpec *spec, bool include_global) {
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
      if (i > 0)
        fprintf(out, ", ");
      fprintf(out, "\"%s\"", spec->info.tags[i]);
    }
    fprintf(out, ";\n");
  }

  fprintf(out, "}\n\n");

  // ---- GLOBAL block (optional) ----
  if (include_global)
    print_global(out, spec);

  // ---- MAIN block ----
  fprintf(out, "MAIN {\n\n");

  print_signal_list(out, "INPUTS", spec->inputs, spec->input_count);
  print_signal_list(out, "OUTPUTS", spec->outputs, spec->output_count);

  // Formula subsections
  print_formula_list(out, &spec->initially, "INITIALLY");
  print_formula_list(out, &spec->preset, "PRESET");
  print_formula_list(out, &spec->require, "REQUIRE");
  print_formula_list(out, &spec->assert_, "ASSERT");
  print_formula_list(out, &spec->assume, "ASSUME");
  print_formula_list(out, &spec->guarantee, "GUARANTEE");

  fprintf(out, "}\n");
}
