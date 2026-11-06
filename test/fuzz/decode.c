#include "decode.h"

#include <stdbool.h>
#include <stdio.h>
#include <string.h>

typedef struct {
  const uint8_t *data;
  size_t size;
  char *out;
  unsigned inputs, outputs, width, definition;
  bool finite;
} Decoder;

static unsigned byte(Decoder *d) {
  if (!d->size)
    return 0;
  --d->size;
  return *d->data++;
}

static void put(Decoder *d, const char *s) {
  size_t n = strlen(s);
  memcpy(d->out, s, n);
  d->out += n;
}

static void number(Decoder *d, unsigned n) {
  d->out += sprintf(d->out, "%u", n);
}

/* Depth counts AST levels, including the integer child of a bus index. */
static void formula(Decoder *d, unsigned depth) {
  static const char *const binary[] = {"&&", "||", "->", "<->", "U", "R", "W"};
  static const char *const unary[] = {"!", "X", "F", "G"};
  /* Typed, closed terminals exercise the numeric/set grammar without making
   * ill-typed formulas, zero divisors or unbounded reductions. Depth <= 5. */
  static const char *const numeric[] = {
      "((1 + 2) == 3)",
      "((2 - 1) != 0)",
      "((2 * 2) < 5)",
      "((2 / 1) <= 2)",
      "((3 % 2) > 0)",
      "((- 1) >= (- 2))",
      "(SIZEOF ob == n)",
      "(SIZE {0, 1} == 2)",
      "(MIN {1, 2} == 1)",
      "(MAX {1, 2} == 2)",
      "(1 IN {0, 1 .. 2})",
      "(SIZE ({0} (+) {1}) == 2)",
      "(SIZE ({0} (*) {0}) == 1)",
      "(SIZE ({0, 1} (-) {1}) == 1)",
      "(SIZE {} == 0)",
      "((+[0 <= k < 2] k) == 1)",
      "((*[k IN {1, 2}] k) == 2)",
      "(SIZE ((+)[k IN {0, 1}] {k}) == 2)",
      "(SIZE ((*)[0 <= k <= 1] {0, k}) == 1)"};
  unsigned kind = depth == 1 ? 0 : byte(d) % (depth >= 5 ? 17 : 15);
  put(d, "(");
  if (kind == 0) {
    unsigned atom = byte(d) % 4;
    if (atom < 2)
      put(d, atom == 0 ? "true" : "false");
    else if (atom == 2 || (d->width && depth == 1)) {
      put(d, "i");
      number(d, byte(d) % d->inputs);
    } else if (d->width) {
      put(d, "ob[");
      number(d, byte(d) % d->width);
      put(d, "]");
    } else {
      put(d, "o");
      number(d, byte(d) % d->outputs);
    }
  } else if (kind <= 7) {
    formula(d, depth - 1);
    put(d, binary[kind - 1]);
    formula(d, depth - 1);
  } else if (kind <= 11) {
    put(d, unary[kind - 8]);
    formula(d, depth - 1);
  } else if (kind == 12) {
    /* Strong next is legal only with finite semantics. */
    put(d, d->finite ? "X[!]" : "X");
    formula(d, depth - 1);
  } else if (kind == 13) {
    static const char *const bounded[] = {"X[1]",  "F[0:2]",  "G[0:2]",
                                          "X[!1]", "F[!0:2]", "G[0:2!]"};
    put(d, bounded[byte(d) % (d->finite ? 6 : 3)]);
    /* Bounds contribute one AST level, even when the body is a leaf. */
    formula(d, depth - 1);
  } else if (kind == 14) {
    if (d->definition)
      put(d, d->definition == 1 ? "d0" : "df(i0)");
    else
      put(d, "i0");
  } else if (kind == 15) {
    unsigned choice = byte(d) % (sizeof(numeric) / sizeof(*numeric));
    put(d, choice == 6 && !d->width ? "(1 == 1)" : numeric[choice]);
  } else {
    put(d, byte(d) % 2 ? "||[k IN {0, 1}]" : "&&[0 <= k <= 1]");
    /* Binder bounds/set have depth <= 2; this branch requires depth >= 5. */
    formula(d, depth - 1);
  }
  put(d, ")");
}

size_t tlsf_fuzz_decode(const uint8_t *data, size_t size,
                        char text[TLSF_FUZZ_TEXT_CAPACITY]) {
  static const char *const semantics[] = {"Mealy",        "Moore",
                                          "Strict,Mealy", "Strict,Moore",
                                          "Finite,Mealy", "Finite,Moore"};
  static const char *const sections[] = {"INITIALLY", "PRESET", "REQUIRE",
                                         "ASSERT",    "ASSUME", "GUARANTEE"};
  static const char *const aliases[] = {"INVARIANTS", "ASSUMPTIONS",
                                        "GUARANTEES"};
  Decoder d = {.data = data, .size = size, .out = text};
  unsigned sem = byte(&d) % 6;
  unsigned target = byte(&d) % 2;
  d.finite = sem >= 4;
  d.inputs = 1 + byte(&d) % 4;
  d.width = byte(&d) % 5;
  d.outputs = d.width ? 1 : 1 + byte(&d) % 4;
  d.definition = byte(&d) % 3;
  put(&d, "INFO { TITLE: \"fuzz\"; DESCRIPTION: \"generated\"; SEMANTICS: ");
  put(&d, semantics[sem]);
  put(&d, target ? "; TARGET: Moore;" : "; TARGET: Mealy;");
  if (byte(&d) % 2)
    put(&d, "TAGS: \"a\", \"b\";");
  put(&d, "}\n");
  if (d.width || d.definition) {
    put(&d, "GLOBAL {");
    if (d.width) {
      put(&d, "PARAMETERS {n = ");
      number(&d, d.width);
      put(&d, ";}");
    }
    if (d.definition)
      put(&d, d.definition == 1 ? "DEFINITIONS {d0 = i0;}"
                                : "DEFINITIONS {df(x) = !(x);}");
    put(&d, "}\n");
  }
  put(&d, "MAIN { INPUTS {");
  for (unsigned i = 0; i < d.inputs; ++i) {
    put(&d, "i");
    number(&d, i);
    put(&d, ";");
  }
  put(&d, "} OUTPUTS {");
  if (d.width)
    put(&d, byte(&d) % 2 ? "ob[n];" : "ob[0..(n - 1)];");
  else
    for (unsigned i = 0; i < d.outputs; ++i) {
      put(&d, "o");
      number(&d, i);
      put(&d, ";");
    }
  put(&d, "}\n");
  for (unsigned section = 0; section < 6; ++section) {
    unsigned count = byte(&d) % 4;
    if (!count)
      continue;
    put(&d, section >= 3 && byte(&d) % 2 ? aliases[section - 3]
                                         : sections[section]);
    put(&d, "{");
    for (unsigned i = 0; i < count; ++i) {
      formula(&d, 6);
      put(&d, ";\n");
    }
    put(&d, "}\n");
  }
  put(&d, "}\n");
  *d.out = '\0';
  return (size_t)(d.out - text);
}
