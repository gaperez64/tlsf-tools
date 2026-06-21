/// tlsfwl — compare TLSF synthesis graphs with Weisfeiler-Lehman features.
/// For experiment management, template retrieval and benchmark clustering.
/// WL similarity is a heuristic, never a proof: it suggests, templates verify.

#include "tlsf/cli.h"
#include "tlsf/cover.h"
#include "tlsf/expand.h"
#include "tlsf/recognize.h"
#include "tlsf/spec.h"
#include "tlsf/wl.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TLSF_VERSION "0.1.0"

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s [OPTIONS] FILE...\n"
          "Weisfeiler-Lehman features / similarity of TLSF synthesis graphs.\n"
          "  --wl N                       refinement depth (default 2)\n"
          "  --labels basic|synthesis|template   WL label scheme (default "
          "synthesis)\n"
          "  --kernel dot|cosine|jaccard  similarity kernel (default cosine)\n"
          "  --matrix                     all-pairs similarity matrix\n"
          "  --split                      split constraints at top-level &&\n"
          "  --compare FILE               similarity of each input to FILE\n"
          "  --nearest K                  top-K nearest inputs per input\n"
          "  --output FILE                write to FILE (default stdout)\n"
          "  --version, --help\n",
          prog);
}

static const char *kernel_name(Kernel k) {
  return k == KERNEL_DOT ? "dot" : k == KERNEL_JACCARD ? "jaccard" : "cosine";
}

// Parse + expand + build WL features for one TLSF file.  Returns nullptr on
// failure (message already printed).  The spec is freed here; features persist.
static WlFeatures *load(const char *path, int rounds, WlLabels labels,
                        bool split) {
  FILE *fp = cli_open_input(path, "tlsfwl");
  if (!fp)
    return nullptr;
  TlsfSpec *spec = cli_parse(fp, "tlsfwl");
  if (path)
    fclose(fp);
  if (!spec)
    return nullptr;
  if (expand(spec, nullptr, 0) != 0) {
    spec_free(spec);
    return nullptr;
  }
  ConstraintCover *cov = cover_build(spec, split);
  if (!cov) {
    spec_free(spec);
    return nullptr;
  }
  recognize_all(cov);
  WlFeatures *f = wl_compute(cov, rounds, labels);
  spec_free(spec); // features are malloc-backed, independent of the arena
  return f;
}

int main(int argc, char *argv[]) {
  int rounds = 2;
  WlLabels labels = WL_SYNTHESIS;
  Kernel kernel = KERNEL_COSINE;
  bool matrix = false;
  bool split = false;
  int nearest = 0;
  const char *compare_file = nullptr, *output_file = nullptr;
  const char **files = malloc((size_t)argc * sizeof(char *));
  size_t nfiles = 0;

#define NEED_ARG()                                                             \
  (++i >= argc                                                                 \
       ? (fprintf(stderr, "tlsfwl: %s requires an argument\n", argv[i - 1]),   \
          exit(1), nullptr)                                                    \
       : argv[i])

  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (strcmp(a, "--wl") == 0) {
      rounds = (int)strtol(NEED_ARG(), nullptr, 10);
      if (rounds < 0) {
        fprintf(stderr, "tlsfwl: --wl N must be >= 0\n");
        free(files);
        return 1;
      }
    } else if (strcmp(a, "--labels") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "basic"))
        labels = WL_BASIC;
      else if (!strcmp(v, "synthesis"))
        labels = WL_SYNTHESIS;
      else if (!strcmp(v, "template"))
        labels = WL_TEMPLATE;
      else {
        fprintf(stderr, "tlsfwl: unknown --labels '%s'\n", v);
        free(files);
        return 1;
      }
    } else if (strcmp(a, "--kernel") == 0) {
      const char *v = NEED_ARG();
      if (!strcmp(v, "dot"))
        kernel = KERNEL_DOT;
      else if (!strcmp(v, "cosine"))
        kernel = KERNEL_COSINE;
      else if (!strcmp(v, "jaccard"))
        kernel = KERNEL_JACCARD;
      else {
        fprintf(stderr, "tlsfwl: unknown --kernel '%s'\n", v);
        free(files);
        return 1;
      }
    } else if (strcmp(a, "--split") == 0) {
      split = true;
    } else if (strcmp(a, "--matrix") == 0) {
      matrix = true;
    } else if (strcmp(a, "--compare") == 0) {
      compare_file = NEED_ARG();
    } else if (strcmp(a, "--nearest") == 0) {
      nearest = (int)strtol(NEED_ARG(), nullptr, 10);
    } else if (strcmp(a, "--output") == 0) {
      output_file = NEED_ARG();
    } else if (strcmp(a, "--version") == 0) {
      printf("tlsfwl %s\n", TLSF_VERSION);
      free(files);
      return 0;
    } else if (strcmp(a, "--help") == 0) {
      usage(argv[0]);
      free(files);
      return 0;
    } else if (a[0] != '-') {
      files[nfiles++] = a;
    } else {
      fprintf(stderr, "tlsfwl: unknown option '%s'\n", a);
      usage(argv[0]);
      free(files);
      return 1;
    }
  }
#undef NEED_ARG

  if (nfiles == 0) {
    fprintf(stderr, "tlsfwl: no input files\n");
    free(files);
    return 1;
  }

  int rc = 0;
  WlFeatures **feats = calloc(nfiles, sizeof(WlFeatures *));
  for (size_t i = 0; i < nfiles; i++) {
    feats[i] = load(files[i], rounds, labels, split);
    if (!feats[i])
      rc = 1;
  }

  FILE *out = output_file ? cli_open_output(output_file, "tlsfwl") : stdout;
  if (!out)
    rc = 1;

  if (rc == 0 && compare_file) {
    WlFeatures *ref = load(compare_file, rounds, labels, split);
    if (!ref) {
      rc = 1;
    } else {
      fprintf(out, "p wlcompare %zu %s\n", nfiles, kernel_name(kernel));
      fprintf(out, "m ref %s\n", compare_file);
      for (size_t i = 0; i < nfiles; i++) {
        fprintf(out, "m file %zu %s\n", i, files[i]);
        fprintf(out, "x %zu %.4f\n", i, wl_kernel(feats[i], ref, kernel));
      }
      wl_features_free(ref);
    }
  } else if (rc == 0 && matrix) {
    fprintf(out, "p wlmatrix %zu %s\n", nfiles, kernel_name(kernel));
    for (size_t i = 0; i < nfiles; i++)
      fprintf(out, "m file %zu %s\n", i, files[i]);
    for (size_t i = 0; i < nfiles; i++)
      for (size_t j = i + 1; j < nfiles; j++)
        fprintf(out, "x %zu %zu %.4f\n", i, j,
                wl_kernel(feats[i], feats[j], kernel));
  } else if (rc == 0 && nearest > 0) {
    fprintf(out, "p wlnearest %zu %s\n", nfiles, kernel_name(kernel));
    double *sim = malloc(nfiles * sizeof(double));
    bool *taken = malloc(nfiles * sizeof(bool));
    for (size_t i = 0; i < nfiles; i++) {
      for (size_t j = 0; j < nfiles; j++) {
        taken[j] = (j == i);
        sim[j] = (j == i) ? -1.0 : wl_kernel(feats[i], feats[j], kernel);
      }
      for (int rank = 0; rank < nearest; rank++) {
        double best = -1.0;
        long bestj = -1;
        for (size_t j = 0; j < nfiles; j++) // ties broken by lowest index
          if (!taken[j] && sim[j] > best) {
            best = sim[j];
            bestj = (long)j;
          }
        if (bestj < 0)
          break;
        taken[bestj] = true;
        fprintf(out, "n %zu %ld %.4f\n", i, bestj, best);
      }
    }
    free(sim);
    free(taken);
  } else if (rc == 0) {
    for (size_t i = 0; i < nfiles; i++)
      if (feats[i])
        wl_features_emit(out, feats[i], files[i]);
  }

  for (size_t i = 0; i < nfiles; i++)
    wl_features_free(feats[i]);
  free(feats);
  free(files);
  if (output_file && out)
    fclose(out);
  return rc;
}
