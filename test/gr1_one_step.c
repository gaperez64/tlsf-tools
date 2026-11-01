/* Independent universal one-step certificate oracle. No libtlsf headers or
 * solver code: parse ASCII AIGER/JSON here and use only OxiDD's Boolean API. */
#define _POSIX_C_SOURCE 200809L
#include "oxidd/capi.h"
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef oxidd_bdd_t Bdd;
static Bdd zero, one, *owned;
static size_t nowned, capacity;

static void fail(const char *message) {
  fprintf(stderr, "one-step oracle: %s\n", message);
  exit(1);
}
static void require(bool condition, const char *message) {
  if (!condition)
    fail(message);
}
static void *alloc(size_t n, size_t size) {
  void *p = calloc(n ? n : 1, size);
  require(p != NULL, "allocation failed");
  return p;
}
/* Every returned OxiDD handle has exactly one owner in this per-goal arena.
 * Arrays below borrow handles; they never create implicit references. */
static Bdd keep(Bdd f) {
  require(f._p != NULL, "OxiDD node capacity exhausted");
  if (nowned == capacity) {
    capacity = capacity ? 2 * capacity : 1024;
    owned = realloc(owned, capacity * sizeof(*owned));
    require(owned != NULL, "handle allocation failed");
  }
  owned[nowned++] = f;
  return f;
}
static Bdd neg(Bdd f) { return keep(oxidd_bdd_not(f)); }
static Bdd both(Bdd a, Bdd b) { return keep(oxidd_bdd_and(a, b)); }
static Bdd either(Bdd a, Bdd b) { return keep(oxidd_bdd_or(a, b)); }
static Bdd different(Bdd a, Bdd b) { return keep(oxidd_bdd_xor(a, b)); }
static void release(size_t mark) {
  while (nowned > mark)
    oxidd_bdd_unref(owned[--nowned]);
}

/* Small JSON token reader: tokens store spans and the index after a subtree.
 * Only fixed ASCII schema keys are looked up; arbitrary strings are skipped. */
typedef struct {
  const char *start;
  size_t len, next;
} Token;
static Token *tokens;
static size_t ntokens, token_capacity;
static const char *cursor;
static void space(void) {
  while (isspace((unsigned char)*cursor))
    ++cursor;
}
static size_t token(void) {
  space();
  require(*cursor != 0, "truncated JSON");
  if (ntokens == token_capacity) {
    token_capacity = token_capacity ? 2 * token_capacity : 1024;
    tokens = realloc(tokens, token_capacity * sizeof(*tokens));
    require(tokens != NULL, "JSON allocation failed");
  }
  size_t index = ntokens++;
  tokens[index].start = cursor;
  char c = *cursor++;
  if (c == '{' || c == '[') {
    space();
    while (*cursor != (c == '{' ? '}' : ']')) {
      if (*cursor == ',' || *cursor == ':')
        ++cursor;
      else
        token();
      space();
      require(*cursor != 0, "unterminated JSON container");
    }
    ++cursor;
  } else if (c == '"') {
    while (*cursor && *cursor != '"') {
      if (*cursor == '\\') {
        ++cursor;
        require(*cursor != 0, "JSON escape");
      }
      ++cursor;
    }
    require(*cursor == '"', "unterminated JSON string");
    ++cursor;
  } else {
    while (*cursor && !strchr(",}:] \r\n\t", *cursor))
      ++cursor;
  }
  tokens[index].len = (size_t)(cursor - tokens[index].start);
  tokens[index].next = ntokens;
  return index;
}
static bool key_is(size_t t, const char *key) {
  return tokens[t].len == strlen(key) + 2 && tokens[t].start[0] == '"' &&
         !strncmp(tokens[t].start + 1, key, strlen(key));
}
static size_t optional(size_t object, const char *key) {
  require(tokens[object].start[0] == '{', "expected JSON object");
  for (size_t t = object + 1; t < tokens[object].next;) {
    size_t value = t + 1;
    require(value < tokens[object].next, "missing JSON value");
    if (key_is(t, key))
      return value;
    t = tokens[value].next;
  }
  return SIZE_MAX;
}
static size_t field(size_t object, const char *key) {
  size_t value = optional(object, key);
  require(value != SIZE_MAX, key);
  return value;
}
static size_t number(size_t t) {
  require(isdigit((unsigned char)*tokens[t].start),
          "expected unsigned integer");
  char *end;
  unsigned long value = strtoul(tokens[t].start, &end, 10);
  require(end == tokens[t].start + tokens[t].len, "invalid integer");
  return value;
}
static size_t integer(size_t object, const char *key) {
  return number(field(object, key));
}
static char *read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  require(f != NULL, path);
  require(fseek(f, 0, SEEK_END) == 0, "seek");
  long size = ftell(f);
  require(size >= 0 && fseek(f, 0, SEEK_SET) == 0, "file size");
  char *text = alloc((size_t)size + 1, 1);
  require(fread(text, 1, (size_t)size, f) == (size_t)size, "read");
  fclose(f);
  return text;
}

typedef struct {
  unsigned cur, next, reset;
} Latch;
typedef struct {
  unsigned lhs, a, b;
} Gate;
typedef struct {
  unsigned max, ni, nl, no, na, nb, nc, nj, nf;
  unsigned *inputs, *outputs, *bad, *fair;
  Latch *latches;
  Gate *gates;
  char **inames, **onames;
} Aag;
static char *line(FILE *f) {
  char *s = NULL;
  size_t n = 0;
  require(getline(&s, &n, f) >= 0, "truncated AAG");
  s[strcspn(s, "\r\n")] = 0;
  return s;
}
static unsigned literal_line(FILE *f) {
  char *s = line(f), *end;
  unsigned long value = strtoul(s, &end, 10);
  require(end != s && *end == 0 && value <= UINT32_MAX, "AAG literal");
  free(s);
  return (unsigned)value;
}
static Aag read_aag(const char *path) {
  FILE *f = fopen(path, "r");
  require(f != NULL, path);
  Aag a = {0};
  char *s = line(f);
  require(sscanf(s, "aag %u %u %u %u %u %u %u %u %u", &a.max, &a.ni, &a.nl,
                 &a.no, &a.na, &a.nb, &a.nc, &a.nj, &a.nf) >= 5,
          "AAG header");
  free(s);
  a.inputs = alloc(a.ni, sizeof(unsigned));
  a.outputs = alloc(a.no, sizeof(unsigned));
  a.bad = alloc(a.nb, sizeof(unsigned));
  a.fair = alloc(a.nf, sizeof(unsigned));
  a.latches = alloc(a.nl, sizeof(Latch));
  a.gates = alloc(a.na, sizeof(Gate));
  a.inames = alloc(a.ni, sizeof(char *));
  a.onames = alloc(a.no, sizeof(char *));
  for (unsigned i = 0; i < a.ni; ++i)
    a.inputs[i] = literal_line(f);
  for (unsigned i = 0; i < a.nl; ++i) {
    s = line(f);
    require(sscanf(s, "%u %u %u", &a.latches[i].cur, &a.latches[i].next,
                   &a.latches[i].reset) >= 2,
            "AAG latch");
    free(s);
  }
  for (unsigned i = 0; i < a.no; ++i)
    a.outputs[i] = literal_line(f);
  for (unsigned i = 0; i < a.nb; ++i)
    a.bad[i] = literal_line(f);
  for (unsigned i = 0; i < a.nc; ++i)
    (void)literal_line(f);
  unsigned *sizes = alloc(a.nj, sizeof(unsigned));
  for (unsigned i = 0; i < a.nj; ++i)
    sizes[i] = literal_line(f);
  for (unsigned i = 0; i < a.nj; ++i)
    for (unsigned j = 0; j < sizes[i]; ++j)
      (void)literal_line(f);
  free(sizes);
  for (unsigned i = 0; i < a.nf; ++i)
    a.fair[i] = literal_line(f);
  for (unsigned i = 0; i < a.na; ++i) {
    s = line(f);
    require(sscanf(s, "%u %u %u", &a.gates[i].lhs, &a.gates[i].a,
                   &a.gates[i].b) == 3,
            "AAG gate");
    free(s);
  }
  size_t n = 0;
  s = NULL;
  while (getline(&s, &n, f) >= 0 && strcmp(s, "c\n") != 0) {
    unsigned index;
    int offset = 0;
    if ((*s == 'i' || *s == 'o') &&
        sscanf(s + 1, "%u %n", &index, &offset) == 1) {
      char *name = s + 1 + offset;
      name[strcspn(name, "\r\n")] = 0;
      if (*s == 'i' && index < a.ni)
        a.inames[index] = strdup(name);
      if (*s == 'o' && index < a.no)
        a.onames[index] = strdup(name);
    }
  }
  free(s);
  fclose(f);
  return a;
}
static void free_aag(Aag *a) {
  for (unsigned i = 0; i < a->ni; ++i)
    free(a->inames[i]);
  for (unsigned i = 0; i < a->no; ++i)
    free(a->onames[i]);
  free(a->inames);
  free(a->onames);
  free(a->inputs);
  free(a->outputs);
  free(a->bad);
  free(a->fair);
  free(a->latches);
  free(a->gates);
}
static Bdd lit(Bdd *values, unsigned max, size_t literal) {
  require(literal / 2 <= max, "literal out of range");
  Bdd f = values[literal / 2];
  require(f._p != NULL, "undefined AAG variable");
  return literal & 1 ? neg(f) : f;
}
static Bdd *compile(const Aag *a, const Bdd *inputs, const Bdd *state) {
  Bdd *values = alloc((size_t)a->max + 1, sizeof(Bdd));
  values[0] = zero;
  for (unsigned i = 0; i < a->ni; ++i) {
    require(a->inputs[i] / 2 <= a->max, "input literal");
    values[a->inputs[i] / 2] = inputs[i];
  }
  for (unsigned i = 0; i < a->nl; ++i) {
    require(a->latches[i].cur / 2 <= a->max, "latch literal");
    values[a->latches[i].cur / 2] = state[i];
  }
  for (unsigned i = 0; i < a->na; ++i) {
    Gate g = a->gates[i];
    require(g.lhs / 2 <= a->max, "gate literal");
    values[g.lhs / 2] =
        both(lit(values, a->max, g.a), lit(values, a->max, g.b));
  }
  return values;
}
static unsigned named(char **names, unsigned count, const char *name) {
  for (unsigned i = 0; i < count; ++i)
    if (names[i] && !strcmp(names[i], name))
      return i;
  fail(name);
  return 0;
}
static Bdd output(const Aag *a, Bdd *values, const char *format, ...) {
  char name[100];
  va_list args;
  va_start(args, format);
  vsnprintf(name, sizeof(name), format, args);
  va_end(args);
  return lit(values, a->max, a->outputs[named(a->onames, a->no, name)]);
}
static Bdd *certificate(const Aag *cert, size_t variables, Bdd *state,
                        size_t ns, Bdd *inputs, size_t ni, bool reset) {
  Bdd *mapped = alloc(cert->ni, sizeof(Bdd));
  for (unsigned i = 0; i < cert->ni; ++i)
    mapped[i] = zero;
  const char *roles[] = {"state", "uncontrollable", "controllable"};
  for (unsigned role = 0; role < 3; ++role) {
    size_t array = field(variables, roles[role]);
    for (size_t t = array + 1; t < tokens[array].next; t = tokens[t].next) {
      size_t ci = integer(t, "certificate_input");
      require(ci < cert->ni, "certificate input mapping");
      if (!role) {
        size_t si = integer(t, "game_latch");
        require(si < ns, "state mapping");
        mapped[ci] = reset ? (integer(t, "reset") ? one : zero) : state[si];
      } else if (!reset) {
        size_t gi = integer(t, "game_input");
        require(gi < ni, "game input mapping");
        mapped[ci] = inputs[gi];
      }
    }
  }
  Bdd *values = compile(cert, mapped, NULL);
  free(mapped);
  return values;
}
int main(int argc, char **argv) {
  require(argc == 5, "usage: gr1_one_step GAME STRATEGY CERTIFICATE SIDECAR");
  Aag game = read_aag(argv[1]), strategy = read_aag(argv[2]),
      cert = read_aag(argv[3]);
  char *json = read_file(argv[4]);
  cursor = json;
  token();
  space();
  require(*cursor == 0, "trailing JSON");
  size_t counts = field(0, "counts"), variables = field(0, "variables");
  size_t ns = integer(counts, "state_variables"), ng = integer(counts, "goals");
  size_t nf = integer(counts, "fairness_assumptions");
  require(integer(counts, "original_game_latches") == game.nl &&
              ns >= game.nl && strategy.nl == ns + ng && cert.nl == 0 &&
              ng > 0 && nf == game.nf,
          "strategy/certificate latch or acceptance mapping mismatch");
  oxidd_bdd_manager_t manager = oxidd_bdd_manager_new(2000000, 100000, 1);
  require(manager._p != NULL, "OxiDD manager allocation");
  zero = keep(oxidd_bdd_false(manager));
  one = keep(oxidd_bdd_true(manager));
  size_t nu = 0;
  for (unsigned i = 0; i < game.ni; ++i) {
    require(game.inames[i] != NULL, "missing game input symbol");
    nu += strncmp(game.inames[i], "controllable_", 13) != 0;
  }
  require(ns + nu <= UINT32_MAX, "variable count");
  oxidd_bdd_manager_add_vars(manager, (uint32_t)(ns + nu));
  Bdd *state = alloc(ns, sizeof(Bdd)), *gi = alloc(game.ni, sizeof(Bdd));
  for (size_t i = 0; i < ns; ++i)
    state[i] = keep(oxidd_bdd_var(manager, (uint32_t)i));
  size_t u = 0;
  for (unsigned i = 0; i < game.ni; ++i) {
    gi[i] = zero;
    if (strncmp(game.inames[i], "controllable_", 13) != 0)
      gi[i] = keep(oxidd_bdd_var(manager, (uint32_t)(ns + u++)));
  }
  Bdd *reset = certificate(&cert, variables, state, ns, gi, game.ni, true);
  require(oxidd_bdd_valid(output(&cert, reset, "inv")),
          "reset outside invariant");
  free(reset);
  size_t mark = nowned, levels = field(counts, "levels_per_goal");
  size_t level_token = levels + 1;
  for (size_t goal = 0; goal < ng; ++goal) {
    require(level_token < tokens[levels].next, "missing goal rank levels");
    size_t nlevels = number(level_token);
    level_token = tokens[level_token].next;
    Bdd *si = alloc(strategy.ni, sizeof(Bdd)),
        *ss = alloc(strategy.nl, sizeof(Bdd));
    for (unsigned i = 0; i < strategy.ni; ++i)
      si[i] = zero;
    for (size_t i = 0; i < ns; ++i)
      ss[i] = state[i];
    for (size_t i = 0; i < ng; ++i)
      ss[ns + i] = i == goal ? one : zero;
    for (unsigned i = 0; i < game.ni; ++i)
      if (strncmp(game.inames[i], "controllable_", 13) != 0)
        si[named(strategy.inames, strategy.ni, game.inames[i])] = gi[i];
    Bdd *sv = compile(&strategy, si, ss);
    for (unsigned i = 0; i < game.ni; ++i)
      if (strncmp(game.inames[i], "controllable_", 13) == 0)
        gi[i] = lit(sv, strategy.max,
                    strategy.outputs[named(strategy.onames, strategy.no,
                                           game.inames[i])]);
    Bdd *gv = compile(&game, gi, state), *next = alloc(ns, sizeof(Bdd));
    size_t states = field(variables, "state"), nstates = 0;
    for (size_t t = states + 1; t < tokens[states].next; t = tokens[t].next) {
      size_t i = integer(t, "game_latch");
      require(i < ns && !next[i]._p, "state index inventory");
      next[i] = lit(gv, game.max, integer(t, "next_game_literal"));
      ++nstates;
    }
    require(nstates == ns, "incomplete state inventory");
    Bdd *gn = compile(&game, gi, next);
    Bdd *cur = certificate(&cert, variables, state, ns, gi, game.ni, false);
    Bdd *suc = certificate(&cert, variables, next, ns, gi, game.ni, false);
    Bdd inv = output(&cert, cur, "inv"), bad = zero;
    for (unsigned i = 0; i < game.nb; ++i)
      bad = either(bad, lit(gv, game.max, game.bad[i]));
    if (!game.nb && game.no == 1)
      bad = lit(gv, game.max, game.outputs[0]);
    Bdd violation = either(bad, neg(output(&cert, suc, "inv")));
    for (size_t i = 0; i < ns; ++i)
      violation = either(
          violation,
          different(lit(sv, strategy.max, strategy.latches[i].next), next[i]));
    violation = either(violation, neg(output(&cert, cur, "move_%zu", goal)));
    Bdd at_goal = output(&cert, cur, "goal_%zu", goal);
    for (size_t i = 0; i < ng; ++i) {
      Bdd expected = either(i == goal ? neg(at_goal) : zero,
                            i == (goal + 1) % ng ? at_goal : zero);
      violation =
          either(violation,
                 different(lit(sv, strategy.max, strategy.latches[ns + i].next),
                           expected));
    }
    Bdd covered = at_goal, lower = output(&cert, suc, "goal_%zu", goal);
    for (size_t k = 0; k < nlevels; ++k) {
      for (size_t i = 0; i < (nf ? nf : 1); ++i) {
        Bdd x = output(&cert, cur, "x_%zu_%zu_%zu", goal, k, i);
        Bdd xn = output(&cert, suc, "x_%zu_%zu_%zu", goal, k, i);
        Bdd fair = nf ? lit(gn, game.max, game.fair[i]) : one;
        for (size_t t = states + 1; t < tokens[states].next;
             t = tokens[t].next) {
          size_t source = optional(t, "source");
          if (nf && source != SIZE_MAX && tokens[source].start[0] == '{' &&
              key_is(field(source, "kind"), "fairness") &&
              integer(source, "index") == i)
            fair = next[integer(t, "game_latch")];
        }
        Bdd layer = both(x, neg(covered));
        Bdd allowed = either(lower, both(xn, neg(fair)));
        violation =
            either(violation, both(neg(at_goal), both(layer, neg(allowed))));
        covered = either(covered, x);
        lower = either(lower, xn);
      }
    }
    violation = both(inv, either(violation, both(neg(at_goal), neg(covered))));
    if (oxidd_bdd_satisfiable(violation)) {
      fprintf(stderr, "one-step oracle: universal check failed for goal %zu\n",
              goal);
      return 1;
    }
    free(si);
    free(ss);
    free(sv);
    free(gv);
    free(gn);
    free(next);
    free(cur);
    free(suc);
    release(mark);
  }
  printf("%zu\n", ng);
  release(0);
  free(owned);
  free(state);
  free(gi);
  free(tokens);
  free(json);
  free_aag(&game);
  free_aag(&strategy);
  free_aag(&cert);
  oxidd_bdd_manager_unref(manager);
  return 0;
}
