#include "gr1_check_internal.h"
#include "tlsf/build_info.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void usage(const char *prog) {
  fprintf(
      stderr,
      "Usage: %s [OPTIONS] GAME POLICY\n"
      "       %s --method region --certificate FILE [OPTIONS] GAME\n"
      "Check a combinational GR(1) policy without solving the game.\n"
      "  --policy-json FILE       policy mapping sidecar (default "
      "POLICY.json)\n"
      "  --certificate FILE       M2 certificate AAG\n"
      "  --certificate-json FILE  M2 sidecar (default CERTIFICATE.json)\n"
      "  --method NAME            auto|certificate|closed-loop|both|region\n"
      "                           region is policy-free gr1-region-v1\n"
      "  --json-out FILE          write versioned method-result JSON\n"
      "  --emit-controller FILE   emit the checked standalone controller\n"
      "  --timeout SECONDS        return UNKNOWN after the soft deadline\n"
      "  --node-cap N             OxiDD inner-node cap (default 16777216)\n"
      "  --cache-cap N            OxiDD apply-cache cap in entries (default "
      "node cap)\n"
      "  --stats                  write construction/proof diagnostics to "
      "stderr\n"
      "Exit 0 VERIFIED, 1 REFUTED, 2 ERROR, 3 UNKNOWN, 4 INVALID,\n"
      "     5 INTERNAL-ERROR (verified certificate contradicted by the "
      "closed loop),\n"
      "     6 CERT_FAILED (a form of UNKNOWN: the certificate does not "
      "prove this policy;\n"
      "       nothing is concluded about the policy itself). Region success "
      "is REGION_VERIFIED.\n",
      prog, prog);
}

static bool parse_u64(const char *text, uint64_t *value) {
  if (!text || *text == '-' || *text == '\0')
    return false;
  char *end = nullptr;
  errno = 0;
  unsigned long long parsed = strtoull(text, &end, 10);
  if (errno || end == text || *end != '\0')
    return false;
  *value = (uint64_t)parsed;
  return true;
}

static bool parse_double(const char *text, double *value) {
  char *end = nullptr;
  errno = 0;
  double parsed = strtod(text, &end);
  if (errno || end == text || *end != '\0' || parsed < 0)
    return false;
  *value = parsed;
  return true;
}

static char *sidecar_default(const char *path) {
  size_t n = strlen(path) + sizeof ".json";
  char *result = malloc(n);
  if (result)
    snprintf(result, n, "%s.json", path);
  return result;
}

static int parse_options(int argc, char **argv, Options *options,
                         char **owned_policy_json, char **owned_cert_json) {
  *options =
      (Options){.method = METHOD_AUTO, .timeout = 0, .node_cap = 1u << 24};
  const char *positional[2] = {nullptr, nullptr};
  uint32_t npos = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--help") || !strcmp(argv[i], "-h")) {
      usage(argv[0]);
      return 1;
    }
    if (!strcmp(argv[i], "--version")) {
      printf("tlsfcertcheck %s oxidd=%s research=%s simd=%s oxidd_patch=%s\n",
             TLSF_PROJECT_VERSION, tlsf_build_oxidd(), tlsf_build_research(),
             tlsf_build_simd(), tlsf_build_oxidd_patch());
      return 1;
    }
    if (!strcmp(argv[i], "--stats")) {
      options->stats = true;
      continue;
    }
    if (!strcmp(argv[i], "--test-unspecialized-policy")) {
      options->test_unspecialized_policy = true;
      continue;
    }
    if (!strcmp(argv[i], "--test-rebuild-successor")) {
      options->test_rebuild_successor = true;
      continue;
    }
    const char **slot = nullptr;
    if (!strcmp(argv[i], "--policy-json"))
      slot = &options->policy_json_path;
    else if (!strcmp(argv[i], "--certificate"))
      slot = &options->certificate_path;
    else if (!strcmp(argv[i], "--certificate-json"))
      slot = &options->certificate_json_path;
    else if (!strcmp(argv[i], "--json-out"))
      slot = &options->json_out_path;
    else if (!strcmp(argv[i], "--emit-controller"))
      slot = &options->emit_path;
    if (slot) {
      if (++i == argc) {
        fprintf(stderr, "%s: option requires a value\n", argv[0]);
        return -1;
      }
      *slot = argv[i];
      continue;
    }
    if (!strcmp(argv[i], "--method")) {
      if (++i == argc) {
        fprintf(stderr, "%s: --method requires a value\n", argv[0]);
        return -1;
      }
      if (!strcmp(argv[i], "auto"))
        options->method = METHOD_AUTO;
      else if (!strcmp(argv[i], "certificate"))
        options->method = METHOD_CERTIFICATE;
      else if (!strcmp(argv[i], "closed-loop"))
        options->method = METHOD_CLOSED_LOOP;
      else if (!strcmp(argv[i], "both"))
        options->method = METHOD_BOTH;
      else if (!strcmp(argv[i], "region"))
        options->method = METHOD_REGION;
      else {
        fprintf(stderr, "%s: unknown method '%s'\n", argv[0], argv[i]);
        return -1;
      }
      continue;
    }
    if (!strcmp(argv[i], "--timeout")) {
      if (++i == argc || !parse_double(argv[i], &options->timeout)) {
        fprintf(stderr, "%s: invalid --timeout\n", argv[0]);
        return -1;
      }
      continue;
    }
    if (!strcmp(argv[i], "--node-cap")) {
      uint64_t cap;
      if (++i == argc || !parse_u64(argv[i], &cap) || cap < 1024 ||
          cap > SIZE_MAX) {
        fprintf(stderr, "%s: invalid --node-cap\n", argv[0]);
        return -1;
      }
      options->node_cap = (size_t)cap;
      continue;
    }
    if (!strcmp(argv[i], "--cache-cap")) {
      uint64_t cap;
      if (++i == argc || !parse_u64(argv[i], &cap) || cap == 0 ||
          cap > SIZE_MAX) {
        fprintf(stderr, "%s: invalid --cache-cap\n", argv[0]);
        return -1;
      }
      options->cache_cap = (size_t)cap;
      options->cache_cap_explicit = true;
      continue;
    }
    if (argv[i][0] == '-') {
      fprintf(stderr, "%s: unknown option '%s'\n", argv[0], argv[i]);
      return -1;
    }
    if (npos == 2) {
      fprintf(stderr, "%s: too many positional arguments\n", argv[0]);
      return -1;
    }
    positional[npos++] = argv[i];
  }
  uint32_t expected_positional = options->method == METHOD_REGION ? 1u : 2u;
  if (npos != expected_positional) {
    usage(argv[0]);
    return -1;
  }
  if (!options->cache_cap)
    options->cache_cap = options->node_cap;
  if (options->cache_cap_explicit &&
      (options->cache_cap & (options->cache_cap - 1)) != 0) {
    fprintf(stderr, "%s: invalid --cache-cap: must be a power of two\n",
            argv[0]);
    return -1;
  }
  if (options->cache_cap_explicit &&
      options->cache_cap > (size_t)UINT32_MAX - 1) {
    fprintf(stderr, "%s: invalid --cache-cap: exceeds OxiDD's capacity limit\n",
            argv[0]);
    return -1;
  }
  if (!gr1_check_node_capacity(options->node_cap,
                               &options->effective_node_cap)) {
    fprintf(stderr, "%s: invalid --node-cap: exceeds OxiDD's capacity limit\n",
            argv[0]);
    return -1;
  }
  if (!gr1_check_cache_capacity(options->cache_cap,
                                &options->effective_cache_cap)) {
    fprintf(stderr, "%s: invalid --%s-cap: exceeds OxiDD's cache limit\n",
            argv[0], options->cache_cap_explicit ? "cache" : "node");
    return -1;
  }
  if (options->cache_cap_explicit &&
      options->effective_cache_cap > options->effective_node_cap) {
    fprintf(stderr,
            "%s: invalid --cache-cap: must not exceed effective node capacity "
            "(%zu)\n",
            argv[0], options->effective_node_cap);
    return -1;
  }
  options->game_path = positional[0];
  options->policy_path = expected_positional == 2 ? positional[1] : nullptr;
  if (options->policy_path && !options->policy_json_path) {
    *owned_policy_json = sidecar_default(options->policy_path);
    options->policy_json_path = *owned_policy_json;
  }
  if (options->certificate_path && !options->certificate_json_path) {
    *owned_cert_json = sidecar_default(options->certificate_path);
    options->certificate_json_path = *owned_cert_json;
  }
  if (options->certificate_json_path && !options->certificate_path) {
    fprintf(stderr, "%s: --certificate-json requires --certificate\n", argv[0]);
    return -1;
  }
  if ((options->method == METHOD_CERTIFICATE ||
       options->method == METHOD_BOTH || options->method == METHOD_REGION) &&
      !options->certificate_path) {
    fprintf(stderr, "%s: selected method requires --certificate\n", argv[0]);
    return -1;
  }
  if (options->method == METHOD_REGION &&
      (options->policy_json_path || options->emit_path ||
       options->test_unspecialized_policy)) {
    fprintf(stderr,
            "%s: --method region does not accept policy options or emit a "
            "controller\n",
            argv[0]);
    return -1;
  }
  return 0;
}

int main(int argc, char **argv) {
  Options options;
  char *owned_policy_json = nullptr, *owned_cert_json = nullptr;
  int parsed =
      parse_options(argc, argv, &options, &owned_policy_json, &owned_cert_json);
  if (parsed != 0) {
    free(owned_policy_json);
    free(owned_cert_json);
    return parsed > 0 ? 0 : EXIT_ERROR;
  }
  return gr1_check_run(options, owned_policy_json, owned_cert_json, nullptr,
                       nullptr);
}
