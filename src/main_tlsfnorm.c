/// tlsfnorm — local, equivalence-preserving normalization of a TLSF spec,
/// re-emitted as TLSF.  Each section is the conjunction of its formulas, so the
/// passes operate per-section without changing the spec's meaning.  This is the
/// user-visible harness for every normalization pass (see include/tlsf/
/// normalize.h): pre-expansion passes run before expand(), post-expansion
/// passes run on the expanded formulas before re-emission.

#include "tlsf/cli.h"
#include "tlsf/expand.h"
#include "tlsf/normalize.h"
#include "tlsf/print_tlsf.h"
#include "tlsf/rewrite.h"
#include "tlsf/spec.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] [FILE]\n"
          "Local normalization of a TLSF spec, re-emitted as TLSF.\n"
          "  --pre-passes SCHEDULE        high-level passes before expand()\n"
          "  --passes SCHEDULE            post-expansion passes (default: "
          "split)\n"
          "  --normalize PROFILE          append a profile to --passes\n"
          "  --norm-max-iter N            schedule-level iteration cap\n"
          "  --norm-max-growth PERCENT    per-formula node growth cap\n"
          "  --norm-max-nodes N           absolute node cap\n"
          "  --norm-stats[=human|tsv]     normalization stats to stderr\n"
          "  --norm-trace FILE            per-step TSV trace (- = stderr)\n"
          "  --norm-soundness off|assert|verify   rule soundness gate "
          "(default assert)\n"
          "  --check-equivalence[=auto|spot|off]  (reserved)\n"
          "  --format tlsf|trace          output (default tlsf)\n"
          "  --overwrite-semantics VALUE  replace SEMANTICS\n"
          "  --overwrite-target VALUE     replace TARGET\n"
          "  --param NAME=VALUE           override a parameter (repeatable)\n"
          "  --output FILE                write to FILE (default stdout)\n"
          "  --version, --help\n"
          "Schedule grammar: pass[:N] comma-list, e.g. "
          "match-safe:2,route-safe.\n"
          "Passes: split nnf weak boolean bool-canon or-to-impl-pattern\n"
          "  equiv-output-side mutex-demorgan route-safe sickert-stage2\n"
          "  sickert-stage3 pre-indexed-x pre-bounded-bool pre-spine-split\n"
          "Profiles: off match-safe route-safe pre-safe sickert-bounded\n",
          prog);
}

static bool parse_override(const char *s, ParamOverride *out) {
  const char *eq = strchr(s, '=');
  if (!eq || eq == s) {
    fprintf(stderr, "tlsfnorm: bad --param '%s'\n", s);
    return false;
  }
  size_t nlen = (size_t)(eq - s);
  char *name = malloc(nlen + 1);
  if (!name)
    return false;
  memcpy(name, s, nlen);
  name[nlen] = '\0';
  char *end;
  long long val = strtoll(eq + 1, &end, 10);
  if (*end != '\0') {
    fprintf(stderr, "tlsfnorm: non-integer value in --param '%s'\n", s);
    free(name);
    return false;
  }
  out->name = name;
  out->value = (int64_t)val;
  return true;
}

typedef enum { STATS_OFF, STATS_HUMAN, STATS_TSV } StatsMode;

// Apply one post-expansion pass spec to one section list (in spec->arena).
// Split is list-altering (grows the list); everything else maps each formula
// through tlsf_normalize_formula.
static void apply_post(TlsfSpec *spec, FormulaList *L,
                       const TlsfNormPassSpec *ps, const TlsfNormOptions *base,
                       TlsfNormStats *stats) {
  if (ps->pass == TLSF_NORM_PASS_SPLIT) {
    FormulaList nl = {0};
    for (uint32_t i = 0; i < L->count; i++) {
      Node **parts;
      uint32_t np = rewrite_decompose(spec->arena, L->formulas[i], &parts);
      for (uint32_t p = 0; p < np; p++)
        (void)formula_list_push(spec, &nl, parts[p]);
    }
    *L = nl;
    return;
  }
  TlsfNormOptions o = *base;
  TlsfNormPassSpec one = *ps;
  o.schedule = (TlsfNormSchedule){.items = &one, .count = 1};
  for (uint32_t i = 0; i < L->count; i++)
    L->formulas[i] =
        tlsf_normalize_formula(spec->arena, L->formulas[i], &o, stats);
}

int main(int argc, char *argv[]) {
  bool trace = false;
  const char *input_file = nullptr, *output_file = nullptr;
  const char *os_arg = nullptr, *ot_arg = nullptr;
  const char *pre_arg = nullptr, *passes_arg = nullptr,
             *normalize_arg = nullptr;
  const char *trace_file = nullptr;
  StatsMode stats_mode = STATS_OFF;
  int soundness = 1; // 0 off, 1 assert, 2 verify (default assert)
  uint32_t max_iter = 32, max_growth = 200, max_nodes = 20000;
  ParamOverride overrides[64];
  size_t n_overrides = 0;

#define NEED_ARG()                                                             \
  (++i >= argc                                                                 \
       ? (fprintf(stderr, "tlsfnorm: %s requires an argument\n", argv[i - 1]), \
          exit(1), nullptr)                                                    \
       : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--pre-passes") == 0) {
      pre_arg = NEED_ARG();
    } else if (strcmp(a, "--passes") == 0) {
      passes_arg = NEED_ARG();
    } else if (strcmp(a, "--normalize") == 0) {
      normalize_arg = NEED_ARG();
    } else if (strcmp(a, "--norm-max-iter") == 0) {
      max_iter = (uint32_t)strtoul(NEED_ARG(), nullptr, 10);
    } else if (strcmp(a, "--norm-max-growth") == 0) {
      max_growth = (uint32_t)strtoul(NEED_ARG(), nullptr, 10);
    } else if (strcmp(a, "--norm-max-nodes") == 0) {
      max_nodes = (uint32_t)strtoul(NEED_ARG(), nullptr, 10);
    } else if (strcmp(a, "--norm-stats") == 0) {
      stats_mode = STATS_HUMAN;
    } else if (strcmp(a, "--norm-stats=human") == 0) {
      stats_mode = STATS_HUMAN;
    } else if (strcmp(a, "--norm-stats=tsv") == 0) {
      stats_mode = STATS_TSV;
    } else if (strcmp(a, "--norm-trace") == 0) {
      trace_file = NEED_ARG();
    } else if (strcmp(a, "--norm-soundness") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "off"))
        soundness = 0;
      else if (!strcmp(v, "assert"))
        soundness = 1;
      else if (!strcmp(v, "verify"))
        soundness = 2;
      else {
        fprintf(stderr, "tlsfnorm: bad --norm-soundness '%s'\n", v);
        return 1;
      }
    } else if (strncmp(a, "--check-equivalence", 19) == 0) {
      // Accepted for forward-compatibility; external check not wired yet.
    } else if (strcmp(a, "--format") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "tlsf"))
        trace = false;
      else if (!strcmp(v, "trace"))
        trace = true;
      else {
        fprintf(stderr, "tlsfnorm: unknown format '%s'\n", v);
        return 1;
      }
    } else if (strcmp(a, "--overwrite-semantics") == 0) {
      os_arg = NEED_ARG();
    } else if (strcmp(a, "--overwrite-target") == 0) {
      ot_arg = NEED_ARG();
    } else if (strcmp(a, "--param") == 0) {
      const char *v = NEED_ARG();
      if (n_overrides >= 64) {
        fprintf(stderr, "tlsfnorm: too many --param overrides\n");
        return 1;
      }
      if (!parse_override(v, &overrides[n_overrides++]))
        return 1;
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfnorm %s\n", TLSF_VERSION);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      return 0;
    } else if (a[0] != '-') {
      if (input_file) {
        fprintf(stderr, "tlsfnorm: multiple input files not supported\n");
        return 1;
      }
      input_file = a;
    } else {
      fprintf(stderr, "tlsfnorm: unknown option '%s'\n", a);
      usage(argv[0]);
      return 1;
    }
  }
#undef NEED_ARG

  if (!passes_arg && !normalize_arg && !pre_arg)
    passes_arg = "split"; // backward-compatible default

  // Parse schedules.
  Arena *sa = arena_new(1 << 12);
  if (!sa) {
    fprintf(stderr, "tlsfnorm: out of memory\n");
    return 1;
  }
  TlsfNormSchedule pre = {0}, post = {0}, extra = {0};
  if (pre_arg && !tlsf_norm_parse_schedule(sa, pre_arg, "tlsfnorm", &pre))
    return 1;
  if (passes_arg &&
      !tlsf_norm_parse_schedule(sa, passes_arg, "tlsfnorm", &post))
    return 1;
  if (normalize_arg &&
      !tlsf_norm_parse_schedule(sa, normalize_arg, "tlsfnorm", &extra))
    return 1;
  // Append --normalize profile to the post schedule.
  if (extra.count) {
    TlsfNormPassSpec *merged =
        ARENA_ALLOC_N(sa, TlsfNormPassSpec, post.count + extra.count);
    for (uint32_t i = 0; i < post.count; i++)
      merged[i] = post.items[i];
    for (uint32_t i = 0; i < extra.count; i++)
      merged[post.count + i] = extra.items[i];
    post.items = merged;
    post.count += extra.count;
  }

  FILE *fp = cli_open_input(input_file, "tlsfnorm");
  if (!fp)
    return 1;
  TlsfSpec *spec = cli_parse(fp, "tlsfnorm");
  if (input_file)
    fclose(fp);
  if (!spec)
    return 1;

  if (os_arg && !parse_semantics(os_arg, &spec->info.semantics)) {
    fprintf(stderr, "tlsfnorm: invalid semantics '%s'\n", os_arg);
    spec_free(spec);
    return 1;
  }
  if (ot_arg && !parse_target(ot_arg, &spec->info.target)) {
    fprintf(stderr, "tlsfnorm: invalid target '%s'\n", ot_arg);
    spec_free(spec);
    return 1;
  }
  if (!spec_validate_semantics(spec, "tlsfnorm")) {
    spec_free(spec);
    return 1;
  }

  bool finite = semantics_is_finite(spec->info.semantics);

  // Soundness gate (always enforces finite-word safety; assert also enforces
  // phase legality; off disables the gate entirely).
  FILE *tracefp = nullptr;
  if (trace_file) {
    tracefp = strcmp(trace_file, "-") == 0 ? stderr : fopen(trace_file, "w");
    if (!tracefp) {
      perror("tlsfnorm: --norm-trace");
      spec_free(spec);
      return 1;
    }
    fprintf(tracefp, "file\tphase\tconstraint\trole\tpass\titeration\t"
                     "nodes_before\tnodes_after\tchanged\treject_reason\n");
  }

  TlsfNormStats pre_stats, post_stats;
  tlsf_norm_stats_init(&pre_stats, TLSF_NORM_PHASE_PRE_EXPAND,
                       tlsf_norm_schedule_string(sa, &pre));
  tlsf_norm_stats_init(&post_stats, TLSF_NORM_PHASE_VISIBLE,
                       tlsf_norm_schedule_string(sa, &post));

  TlsfNormOptions pre_opts, post_opts;
  tlsf_norm_options_default(&pre_opts, TLSF_NORM_PHASE_PRE_EXPAND);
  tlsf_norm_options_default(&post_opts, TLSF_NORM_PHASE_VISIBLE);
  pre_opts.finite_word = post_opts.finite_word = finite;
  pre_opts.max_iter_default = post_opts.max_iter_default = max_iter;
  pre_opts.max_growth_percent = post_opts.max_growth_percent = max_growth;
  pre_opts.max_nodes = post_opts.max_nodes = max_nodes;
  pre_opts.trace = post_opts.trace = tracefp;
  pre_opts.trace_file = post_opts.trace_file =
      input_file ? input_file : "<stdin>";

  TlsfNormRejectReason reason;
  if (soundness >= 1) {
    if (!tlsf_norm_schedule_check(&pre, &pre_opts, "tlsfnorm", &reason) ||
        !tlsf_norm_schedule_check(&post, &post_opts, "tlsfnorm", &reason)) {
      spec_free(spec);
      return 1;
    }
  }

  // Pre-expansion passes operate on the high-level section formulas.  The
  // pre-pass rewrites land in PR5; the plumbing/guard is active now.
  if (pre.count) {
    FormulaList *plists[] = {&spec->initially, &spec->require,
                             &spec->assume,    &spec->preset,
                             &spec->assert_,   &spec->guarantee};
    for (uint32_t pi = 0; pi < pre.count; pi++) {
      TlsfNormPassSpec one = pre.items[pi];
      TlsfNormOptions o = pre_opts;
      o.schedule = (TlsfNormSchedule){.items = &one, .count = 1};
      for (int s = 0; s < 6; s++)
        for (uint32_t k = 0; k < plists[s]->count; k++)
          plists[s]->formulas[k] = tlsf_normalize_formula(
              spec->arena, plists[s]->formulas[k], &o, &pre_stats);
    }
  }

  if (expand(spec, overrides, n_overrides) != 0) {
    spec_free(spec);
    return 1;
  }
  for (size_t i = 0; i < n_overrides; i++)
    free((void *)overrides[i].name);

  FormulaList *lists[] = {&spec->initially, &spec->require, &spec->assume,
                          &spec->preset,    &spec->assert_, &spec->guarantee};
  static const char *names[] = {"INITIALLY", "REQUIRE", "ASSUME",
                                "PRESET",    "ASSERT",  "GUARANTEE"};

  FILE *out = cli_open_output(output_file, "tlsfnorm");
  if (!out) {
    spec_free(spec);
    return 1;
  }

  for (uint32_t p = 0; p < post.count; p++) {
    for (int s = 0; s < 6; s++) {
      uint32_t before = lists[s]->count;
      apply_post(spec, lists[s], &post.items[p], &post_opts, &post_stats);
      if (trace && lists[s]->count != before)
        fprintf(out, "c pass %s: %s %u -> %u\n",
                tlsf_norm_pass_name(post.items[p].pass), names[s], before,
                lists[s]->count);
    }
  }

  if (!trace)
    print_tlsf(out, spec, /*include_global=*/false);

  if (stats_mode == STATS_HUMAN) {
    if (pre.count)
      tlsf_norm_stats_print_human(stderr, &pre_stats);
    tlsf_norm_stats_print_human(stderr, &post_stats);
  } else if (stats_mode == STATS_TSV) {
    tlsf_norm_stats_print_tsv_header(stderr);
    if (pre.count)
      tlsf_norm_stats_print_tsv_row(stderr, &pre_stats);
    tlsf_norm_stats_print_tsv_row(stderr, &post_stats);
  }

  if (tracefp && tracefp != stderr)
    fclose(tracefp);
  if (output_file)
    fclose(out);
  arena_free(sa);
  spec_free(spec);
  return 0;
}
