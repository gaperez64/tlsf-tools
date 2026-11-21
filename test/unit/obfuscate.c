// tlsf_obfuscate(): identifier classes, neutral INFO, determinism, seeds,
// the self-check's fault hooks, and error statuses.

#include "../check.h"
#include "tlsf/obfuscate.h"

#include <ctype.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

// The fixture (obfuscate_every.tlsf) has every identifier class: signals, a
// bus, an enum type and labels, used and unused parameters, definitions, an
// argument shadowing a parameter, range and set binders and a pattern
// variable, plus free text and the SYNTCOMP trailer.
static char *every;

static const struct {
  const char *name;
  TlsfObfuscateKind kind;
} classes[] = {
    {"request", TLSF_OBFUSCATE_INPUT},
    {"reset", TLSF_OBFUSCATE_INPUT},
    {"grant", TLSF_OBFUSCATE_OUTPUT},
    {"mode", TLSF_OBFUSCATE_OUTPUT},
    {"width", TLSF_OBFUSCATE_PARAMETER},
    {"unused_alpha", TLSF_OBFUSCATE_PARAMETER},
    {"unused_beta", TLSF_OBFUSCATE_PARAMETER},
    {"unused_gamma", TLSF_OBFUSCATE_PARAMETER},
    {"phase", TLSF_OBFUSCATE_ENUM_TYPE},
    {"idle", TLSF_OBFUSCATE_ENUM_LABEL},
    {"busy", TLSF_OBFUSCATE_ENUM_LABEL},
    {"mutex", TLSF_OBFUSCATE_DEFINITION},
    {"exclusive", TLSF_OBFUSCATE_DEFINITION},
    {"served", TLSF_OBFUSCATE_DEFINITION},
    {"bus", TLSF_OBFUSCATE_ARGUMENT},
    {"width", TLSF_OBFUSCATE_ARGUMENT},
    {"formula", TLSF_OBFUSCATE_ARGUMENT},
    {"left", TLSF_OBFUSCATE_BINDER},
    {"right", TLSF_OBFUSCATE_BINDER},
    {"client", TLSF_OBFUSCATE_BINDER},
    {"leaf", TLSF_OBFUSCATE_PATTERN},
    {"request_2", TLSF_OBFUSCATE_INPUT_SIGNAL},
    {"reset", TLSF_OBFUSCATE_INPUT_SIGNAL},
    {"grant_0", TLSF_OBFUSCATE_OUTPUT_SIGNAL},
    {"mode_1", TLSF_OBFUSCATE_OUTPUT_SIGNAL},
};

static TlsfObfuscateStatus run(const char *source, unsigned mode, uint64_t seed,
                               TlsfObfuscateResult *result) {
  TlsfObfuscateOptions o = {.mode = mode, .seed = seed};
  return tlsf_obfuscate(source, strlen(source), &o, result);
}

// True when `word` occurs in `text` as a whole identifier.
static bool identifier_char(char c) {
  return isalnum((unsigned char)c) || c == '_' || c == '@' || c == '\'';
}

static bool has_identifier(const char *text, const char *word) {
  size_t n = strlen(word);
  for (const char *at = strstr(text, word); at; at = strstr(at + 1, word)) {
    bool start = at == text || !identifier_char(at[-1]);
    bool end = !identifier_char(at[n]);
    if (start && end)
      return true;
  }
  return false;
}

static bool neutral(const char *name) {
  if (!islower((unsigned char)*name++) || !isdigit((unsigned char)*name))
    return false;
  while (isdigit((unsigned char)*name))
    name++;
  if (*name == '_' && isdigit((unsigned char)name[1]))
    for (name++; isdigit((unsigned char)*name); name++)
      ;
  return *name == '\0';
}

static void every_class_renamed(void) {
  TlsfObfuscateResult r;
  CHECK(run(every, TLSF_OBFUSCATE_RENAME, 5, &r) == TLSF_OBFUSCATE_OK);
  for (size_t i = 0; i < sizeof classes / sizeof *classes; i++) {
    const char *renamed =
        tlsf_obfuscate_lookup(&r, classes[i].name, classes[i].kind);
    CHECK(renamed && neutral(renamed));
    CHECK(!has_identifier(r.text, classes[i].name));
  }
  // One bijection on spellings: the shadowing argument keeps sharing the
  // parameter's name, and bus bits follow their bus.
  CHECK(strcmp(tlsf_obfuscate_lookup(&r, "width", TLSF_OBFUSCATE_ARGUMENT),
               tlsf_obfuscate_lookup(&r, "width", TLSF_OBFUSCATE_PARAMETER)) ==
        0);
  char bit[32];
  snprintf(bit, sizeof bit, "%s_2",
           tlsf_obfuscate_lookup(&r, "request", TLSF_OBFUSCATE_INPUT));
  CHECK(strcmp(
            tlsf_obfuscate_lookup(&r, "request_2", TLSF_OBFUSCATE_INPUT_SIGNAL),
            bit) == 0);
  for (size_t i = 0; i < r.entry_count; i++)
    CHECK(neutral(r.entries[i].obfuscated));
  CHECK(has_identifier(r.text, "_")); // the pattern wildcard stays
  tlsf_obfuscate_result_clear(&r);
}

static void info_and_comments_neutral(void) {
  for (unsigned mode = TLSF_OBFUSCATE_RENAME; mode <= TLSF_OBFUSCATE_ALL;
       mode++) {
    TlsfObfuscateResult r;
    CHECK(run(every, mode, 1, &r) == TLSF_OBFUSCATE_OK);
    CHECK(!strstr(r.text, "//") && !strstr(r.text, "/*"));
    CHECK(!strstr(r.text, "SYNTCOMP") && !strstr(r.text, "STATUS") &&
          !strstr(r.text, "REF_SIZE"));
    CHECK(strstr(r.text, "SEMANTICS:   Mealy;"));
    CHECK(strstr(r.text, "TARGET:      Mealy;"));
    bool renames = mode & TLSF_OBFUSCATE_RENAME;
    CHECK(!strstr(r.text, "Arbiter") == renames);
    CHECK(!strstr(r.text, "TAGS") == renames);
    CHECK((r.entry_count == 0) == !renames);
    tlsf_obfuscate_result_clear(&r);
  }
}

static void deterministic_and_seeded(void) {
  for (unsigned mode = TLSF_OBFUSCATE_RENAME; mode <= TLSF_OBFUSCATE_ALL;
       mode++) {
    TlsfObfuscateResult a, b, c;
    CHECK(run(every, mode, 7, &a) == TLSF_OBFUSCATE_OK);
    CHECK(run(every, mode, 7, &b) == TLSF_OBFUSCATE_OK);
    CHECK(run(every, mode, 8, &c) == TLSF_OBFUSCATE_OK);
    CHECK(a.size == b.size && memcmp(a.text, b.text, a.size) == 0);
    CHECK(a.size != c.size || memcmp(a.text, c.text, a.size) != 0);
    tlsf_obfuscate_result_clear(&a);
    tlsf_obfuscate_result_clear(&b);
    tlsf_obfuscate_result_clear(&c);
  }
  // The seed gives the name, not the declaration order: across seeds the
  // first unused parameter takes several numbers.
  unsigned seen = 0;
  for (uint64_t seed = 0; seed < 16; seed++) {
    TlsfObfuscateResult r;
    CHECK(run(every, TLSF_OBFUSCATE_RENAME, seed, &r) == TLSF_OBFUSCATE_OK);
    const char *name =
        tlsf_obfuscate_lookup(&r, "unused_alpha", TLSF_OBFUSCATE_PARAMETER);
    CHECK(name && name[0] == 'p' && name[1] >= '0' && name[1] <= '3');
    seen |= 1u << (name[1] - '0');
    tlsf_obfuscate_result_clear(&r);
  }
  CHECK(__builtin_popcount(seen) > 1);
}

static void reorder_keeps_names(void) {
  TlsfObfuscateResult r;
  CHECK(run(every, TLSF_OBFUSCATE_REORDER, 3, &r) == TLSF_OBFUSCATE_OK);
  for (size_t i = 0; i < sizeof classes / sizeof *classes; i++)
    if (classes[i].kind < TLSF_OBFUSCATE_INPUT_SIGNAL)
      CHECK(has_identifier(r.text, classes[i].name));
  tlsf_obfuscate_result_clear(&r);
}

static void overrides_become_values(void) {
  ParamOverride width = {"width", 4};
  TlsfObfuscateOptions o = {
      .mode = TLSF_OBFUSCATE_ALL, .overrides = &width, .n_overrides = 1};
  TlsfObfuscateResult r;
  CHECK(tlsf_obfuscate(every, strlen(every), &o, &r) == TLSF_OBFUSCATE_OK);
  char value[32];
  snprintf(value, sizeof value, "%s = 4;",
           tlsf_obfuscate_lookup(&r, "width", TLSF_OBFUSCATE_PARAMETER));
  CHECK(strstr(r.text, value));
  CHECK(tlsf_obfuscate_lookup(&r, "grant_3", TLSF_OBFUSCATE_OUTPUT_SIGNAL));
  tlsf_obfuscate_result_clear(&r);

  ParamOverride unknown = {"height", 2};
  o.overrides = &unknown;
  CHECK(tlsf_obfuscate(every, strlen(every), &o, &r) == TLSF_OBFUSCATE_INVALID);
  CHECK(!r.text && strstr(r.message, "height"));
  tlsf_obfuscate_result_clear(&r);
}

static void self_check_rejects_faults(void) {
  for (unsigned fault = 1; fault <= 2; fault++)
    for (unsigned mode = TLSF_OBFUSCATE_RENAME; mode <= TLSF_OBFUSCATE_ALL;
         mode++) {
      TlsfObfuscateOptions o = {.mode = mode, .seed = 2, .test_fault = fault};
      TlsfObfuscateResult r;
      CHECK(tlsf_obfuscate(every, strlen(every), &o, &r) ==
            TLSF_OBFUSCATE_CHECK_FAILED);
      CHECK(!r.text && r.entry_count == 0);
      CHECK(strstr(r.message, "self-check"));
      tlsf_obfuscate_result_clear(&r);
    }
}

static void errors(void) {
  TlsfObfuscateResult r;
  CHECK(run(every, 0, 0, &r) == TLSF_OBFUSCATE_INVALID);
  tlsf_obfuscate_result_clear(&r);
  CHECK(run(every, 4, 0, &r) == TLSF_OBFUSCATE_INVALID);
  tlsf_obfuscate_result_clear(&r);
  CHECK(run("INFO { SEMANTICS: Mealy TARGET: Mealy } MAIN { INPUTS { a ",
            TLSF_OBFUSCATE_ALL, 0, &r) == TLSF_OBFUSCATE_INVALID);
  CHECK(!r.text && strstr(r.message, "does not parse"));
  tlsf_obfuscate_result_clear(&r);
  static const char unvalued[] =
      "INFO { TITLE: \"t\" DESCRIPTION: \"d\" SEMANTICS: Mealy TARGET: Mealy }"
      "GLOBAL { PARAMETERS { n; } }"
      "MAIN { INPUTS { r[n]; } OUTPUTS { g[n]; }"
      "  GUARANTEE { &&[0 <= i < n] G (r[i] -> F g[i]); } }";
  CHECK(run(unvalued, TLSF_OBFUSCATE_ALL, 0, &r) ==
        TLSF_OBFUSCATE_UNEXPANDABLE);
  CHECK(strstr(r.message, "--param n="));
  tlsf_obfuscate_result_clear(&r);
  ParamOverride n = {"n", 2};
  TlsfObfuscateOptions o = {
      .mode = TLSF_OBFUSCATE_ALL, .overrides = &n, .n_overrides = 1};
  CHECK(tlsf_obfuscate(unvalued, strlen(unvalued), &o, &r) ==
        TLSF_OBFUSCATE_OK);
  tlsf_obfuscate_result_clear(&r);
}

static char *read_file(const char *path) {
  FILE *in = fopen(path, "rb");
  CHECK(in);
  static char bytes[1 << 16];
  size_t size = fread(bytes, 1, sizeof bytes - 1, in);
  CHECK(!ferror(in) && size < sizeof bytes - 1);
  fclose(in);
  bytes[size] = '\0';
  return bytes;
}

int main(int argc, char **argv) {
  CHECK(argc == 2);
  every = read_file(argv[1]);
  every_class_renamed();
  info_and_comments_neutral();
  deterministic_and_seeded();
  reorder_keeps_names();
  overrides_become_values();
  self_check_rejects_faults();
  errors();
  return 0;
}
