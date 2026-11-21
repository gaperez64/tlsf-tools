#include "tlsf/print_tlsf.h"
#include "spec_internal.h"
#include "arena_budget.h"

#include <assert.h>

// ---------------------------------------------------------------------------
// Internal: formula printer in TLSF syntax
// (identical operators to ltlxba except TLSF uses ! not !, same symbols)
// ---------------------------------------------------------------------------

static void print_formula(FILE *out, const Node *n, Arena *budget);
static void print_cases(FILE *out, const Node *n, Arena *budget);

// A big operator's body extends rightwards: close it before printing more of
// the surrounding expression. Delimited or final operands need no extra pair.
static void print_nonfinal(FILE *out, const Node *n, Arena *budget) {
  bool paren = n->kind == NODE_FORALL || n->kind == NODE_EXISTS ||
               n->kind == NODE_SUM || n->kind == NODE_PRODUCT ||
               n->kind == NODE_SET_BIG_UNION || n->kind == NODE_SET_BIG_INTER;
  if (paren)
    fprintf(out, "(");
  print_formula(out, n, budget);
  if (paren)
    fprintf(out, ")");
}

// True when `n` prints inside its own parentheses or braces, or as a keyword.
static bool prints_enclosed(const Node *n) {
  switch (n->kind) {
  case NODE_TRUE:
  case NODE_FALSE:
  case NODE_AND:
  case NODE_OR:
  case NODE_IMPL:
  case NODE_EQUIV:
  case NODE_U:
  case NODE_R:
  case NODE_W:
  case NODE_INT_ADD:
  case NODE_INT_SUB:
  case NODE_INT_MUL:
  case NODE_INT_DIV:
  case NODE_INT_MOD:
  case NODE_INT_NEG:
  case NODE_CMP_EQ:
  case NODE_CMP_NE:
  case NODE_CMP_LT:
  case NODE_CMP_LE:
  case NODE_CMP_GT:
  case NODE_CMP_GE:
  case NODE_IN:
  case NODE_MATCH:
  case NODE_SET:
  case NODE_SET_ENUM:
  case NODE_SET_UNION:
  case NODE_SET_INTER:
  case NODE_SET_DIFF:
  case NODE_ITE:
    return true;
  default:
    return false;
  }
}

// One guard or value of a case chain. TLSF §4.6 has no case separator and the
// parser takes the longest match (see README), so anything else is enclosed:
// a trailing identifier would call the next guard (`x (g)`), a leading minus
// would subtract (`0 -n < 0`), and a big operator would absorb it.
static void print_case_part(FILE *out, const Node *n, Arena *budget) {
  bool paren = !prints_enclosed(n);
  if (paren)
    fprintf(out, "(");
  print_formula(out, n, budget);
  if (paren)
    fprintf(out, ")");
}

// Print a definition's case chain. The parser ends every chain in a `false`
// default, which re-parsing restores, so it is not printed.
static void print_cases(FILE *out, const Node *n, Arena *budget) {
  for (bool first = true; n->kind == NODE_ITE; n = n->if_else, first = false) {
    if (!first)
      fprintf(out, "  ");
    print_case_part(out, n->if_cond, budget);
    fprintf(out, " : ");
    print_case_part(out, n->if_then, budget);
  }
  if (n->kind != NODE_FALSE) {
    fprintf(out, "  otherwise : ");
    print_case_part(out, n, budget);
  }
}

static void print_formula(FILE *out, const Node *n, Arena *budget) {
  assert(n);
  if (budget && (!arena_check_budget(budget, 0) || ferror(out)))
    return;
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
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;
  case NODE_AND:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " && ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_OR:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " || ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_IMPL:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " -> ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_EQUIV:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " <-> ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;

  case NODE_X:
    fprintf(out, "X (");
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;
  case NODE_X_STRONG:
    fprintf(out, "X[!] (");
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;
  case NODE_F:
    fprintf(out, "F (");
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;
  case NODE_G:
    fprintf(out, "G (");
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;

  case NODE_U:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " U ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_R:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " R ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_W:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " W ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_M:
    fprintf(out, "!((!(");
    print_formula(out, n->lhs, budget);
    fprintf(out, ")) W (!(");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")))");
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
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " + ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_INT_SUB:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " - ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_INT_MUL:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " * ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_INT_DIV:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " / ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_INT_MOD:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " %% ");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  case NODE_INT_NEG:
    fprintf(out, "(- ");
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;

  case NODE_SIZEOF:
    fprintf(out, "SIZEOF %s", n->sizeof_name);
    return;

  case NODE_SET_SIZE:
  case NODE_SET_MIN:
  case NODE_SET_MAX:
    fprintf(out, "%s (",
            n->kind == NODE_SET_SIZE  ? "SIZE"
            : n->kind == NODE_SET_MIN ? "MIN"
                                      : "MAX");
    print_formula(out, n->arg, budget);
    fprintf(out, ")");
    return;

  case NODE_SET:
  case NODE_SET_ENUM:
    fprintf(out, "{");
    for (uint16_t i = 0; i < n->set_size; i++) {
      if (i > 0)
        fprintf(out, i == 2 && n->kind == NODE_SET_ENUM ? " .. " : ", ");
      print_formula(out, n->set_elems[i], budget);
    }
    fprintf(out, "}");
    return;

  case NODE_SET_UNION:
  case NODE_SET_INTER:
  case NODE_SET_DIFF:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " %s ",
            n->kind == NODE_SET_UNION   ? "(+)"
            : n->kind == NODE_SET_INTER ? "(*)"
                                        : "(-)");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;

  case NODE_BUS_INDEX:
    fprintf(out, "%s[", n->bus_name);
    print_formula(out, n->bus_index, budget);
    fprintf(out, "]");
    return;

  case NODE_FORALL:
  case NODE_EXISTS:
  case NODE_SUM:
  case NODE_PRODUCT:
  case NODE_SET_BIG_UNION:
  case NODE_SET_BIG_INTER: {
    const char *op = n->kind == NODE_FORALL          ? "&&"
                     : n->kind == NODE_EXISTS        ? "||"
                     : n->kind == NODE_SUM           ? "+"
                     : n->kind == NODE_PRODUCT       ? "*"
                     : n->kind == NODE_SET_BIG_UNION ? "(+)"
                                                     : "(*)";
    fprintf(out, "%s[", op);
    if (n->qset) {
      fprintf(out, "%s IN ", n->qvar);
      print_formula(out, n->qset, budget);
    } else {
      print_nonfinal(out, n->qlo, budget);
      fprintf(out, " %s %s %s ", n->qlo_strict ? "<" : "<=", n->qvar,
              n->qhi_strict ? "<" : "<=");
      print_formula(out, n->qhi, budget);
    }
    fprintf(out, "] ");
    print_formula(out, n->qbody, budget);
    return;
  }

  case NODE_DEF_CALL:
    fprintf(out, "%s(", n->callee);
    for (uint16_t i = 0; i < n->call_argc; i++) {
      if (i > 0)
        fprintf(out, ", ");
      print_formula(out, n->call_args[i], budget);
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
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " %s ", ops[n->kind - NODE_CMP_EQ]);
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;
  }

  case NODE_IN:
  case NODE_MATCH:
    fprintf(out, "(");
    print_nonfinal(out, n->lhs, budget);
    fprintf(out, " %s ", n->kind == NODE_IN ? "IN" : "~");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;

  case NODE_ITE:
    // Only a definition body may hold several cases; elsewhere this is one
    // guarded expression, which parentheses keep from extending.
    fprintf(out, "(");
    print_cases(out, n, budget);
    fprintf(out, ")");
    return;

  case NODE_NEXT_N:
    fprintf(out, n->bounded.strong ? "X[!" : "X[");
    print_formula(out, n->lhs, budget);
    fprintf(out, "] (");
    print_formula(out, n->rhs, budget);
    fprintf(out, ")");
    return;

  case NODE_G_RANGE:
  case NODE_F_RANGE:
    fprintf(out, n->bounded.strong ? "%c[!" : "%c[",
            n->kind == NODE_G_RANGE ? 'G' : 'F');
    print_formula(out, n->qlo, budget);
    fprintf(out, ":");
    print_formula(out, n->qhi, budget);
    fprintf(out, "] (");
    print_formula(out, n->qbody, budget);
    fprintf(out, ")");
    return;

  default:
    assert(false && "print_tlsf: unexpected node kind");
  }
}

void print_tlsf_formula(FILE *out, const Node *formula) {
  print_formula(out, formula, nullptr);
}

void print_tlsf_formula_checked(FILE *out, const Node *formula, Arena *arena) {
  print_formula(out, formula, arena);
}

// True when `sd` is re-emitted as `TYPE name;`: its enum type is still
// declared, which holds only before expand() empties the GLOBAL tables.
static bool prints_enum_type(const TlsfSpec *spec, const SignalDecl *sd,
                             bool include_global) {
  return include_global && sd->is_bus && sd->enum_type &&
         spec_find_enum_type(spec, sd->enum_type);
}

// Print one INPUTS/OUTPUTS subsection.  A bus prints its declared range; when
// the bounds are parametric expressions (non-expanded re-emission) those are
// printed faithfully, otherwise the resolved integer bounds are used.
static void print_signal_list(FILE *out, const char *subsection,
                              const TlsfSpec *spec, const SignalDecl *sigs,
                              uint32_t count, bool include_global) {
  fprintf(out, "  %s {\n", subsection);
  for (uint32_t i = 0; i < count; i++) {
    const SignalDecl *sd = &sigs[i];
    if (prints_enum_type(spec, sd, include_global)) {
      fprintf(out, "    %s %s;\n", sd->enum_type, sd->name);
      continue;
    }
    if (!sd->is_bus) {
      fprintf(out, "    %s;\n", sd->name);
      continue;
    }
    fprintf(out, "    %s[", sd->name);
    if (sd->bus_lo_expr)
      print_formula(out, sd->bus_lo_expr, nullptr);
    else
      fprintf(out, "%u", sd->bus_lo);
    fprintf(out, "..");
    if (sd->bus_hi_expr)
      print_formula(out, sd->bus_hi_expr, nullptr);
    else
      fprintf(out, "%u", sd->bus_hi);
    fprintf(out, "];\n");
  }
  fprintf(out, "  }\n\n");
}

// The validity formula of a signal printed as `TYPE name;`: re-parsing the
// declaration adds it again.
static bool is_implicit_formula(const TlsfSpec *spec, const Node *formula,
                                bool include_global) {
  if (!include_global || spec->enum_type_count == 0)
    return false;
  const SignalDecl *lists[] = {spec->inputs, spec->outputs};
  uint32_t counts[] = {spec->input_count, spec->output_count};
  for (unsigned k = 0; k < 2; k++)
    for (uint32_t i = 0; i < counts[k]; i++)
      if (lists[k][i].enum_validity == formula &&
          prints_enum_type(spec, &lists[k][i], include_global))
        return true;
  return false;
}

static void print_formula_list(FILE *out, const TlsfSpec *spec,
                               const FormulaList *list, const char *subsection,
                               bool include_global) {
  uint32_t shown = 0;
  for (uint32_t i = 0; i < list->count; i++)
    shown += !is_implicit_formula(spec, list->formulas[i], include_global);
  if (shown == 0)
    return;
  fprintf(out, "    %s {\n", subsection);
  for (uint32_t i = 0; i < list->count; i++) {
    if (is_implicit_formula(spec, list->formulas[i], include_global))
      continue;
    fprintf(out, "      ");
    print_formula(out, list->formulas[i], nullptr);
    fprintf(out, ";\n");
  }
  fprintf(out, "    }\n\n");
}

// ---------------------------------------------------------------------------
// Semantics / target string helpers
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// GLOBAL section (parameters + definitions), preserved when re-emitting a
// non-expanded spec (e.g. for plain parameter substitution).
// ---------------------------------------------------------------------------

static void print_global(FILE *out, const TlsfSpec *spec) {
  if (spec->param_count == 0 && spec->def_count == 0 &&
      spec->enum_type_count == 0)
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

  if (spec->def_count > 0 || spec->enum_type_count > 0) {
    fprintf(out, "  DEFINITIONS {\n");
    for (uint16_t i = 0; i < spec->enum_type_count; i++) {
      const EnumType *t = &spec->enum_types[i];
      fprintf(out, "    enum %s =", t->name);
      for (uint16_t j = 0; j < t->label_count; j++) {
        const EnumLabel *l = &spec->enum_labels[t->label_start + j];
        fprintf(out, "\n      %s: %s", l->name, l->bits);
      }
      fprintf(out, ";\n");
    }
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
      if (d->body->kind == NODE_ITE)
        print_cases(out, d->body, nullptr);
      else
        print_formula(out, d->body, nullptr);
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

  fprintf(out, "  SEMANTICS:   %s;\n",
          spec_semantics_name(spec->info.semantics));
  fprintf(out, "  TARGET:      %s;\n", spec_target_name(spec->info.target));

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

  print_signal_list(out, "INPUTS", spec, spec->inputs, spec->input_count,
                    include_global);
  print_signal_list(out, "OUTPUTS", spec, spec->outputs, spec->output_count,
                    include_global);

  // Formula subsections
  print_formula_list(out, spec, &spec->initially, "INITIALLY", include_global);
  print_formula_list(out, spec, &spec->preset, "PRESET", include_global);
  print_formula_list(out, spec, &spec->require, "REQUIRE", include_global);
  print_formula_list(out, spec, &spec->assert_, "ASSERT", include_global);
  print_formula_list(out, spec, &spec->assume, "ASSUME", include_global);
  print_formula_list(out, spec, &spec->guarantee, "GUARANTEE", include_global);

  fprintf(out, "}\n");
}
