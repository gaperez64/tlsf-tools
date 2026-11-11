#include "tlsf/symmetry.h"
#include "tlsf/version.h"
extern "C" {
#include "diagnostic.h"
}
#include <yyjson.h>

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <memory>
#include <stdexcept>
#include <string>

using Clock = std::chrono::steady_clock;

// yyjson is already a library dependency; keep all escaping and serialization
// there. Fail rather than emitting an incomplete census on allocation failure.
template <class T> static T checked(T value) {
  if (!value)
    throw std::bad_alloc();
  return value;
}

struct Json {
  std::unique_ptr<yyjson_mut_doc, decltype(&yyjson_mut_doc_free)> doc{
      checked(yyjson_mut_doc_new(nullptr)), yyjson_mut_doc_free};

  yyjson_mut_val *object() { return checked(yyjson_mut_obj(doc.get())); }
  yyjson_mut_val *array() { return checked(yyjson_mut_arr(doc.get())); }
  void add(yyjson_mut_val *o, const char *key, yyjson_mut_val *v) {
    checked(yyjson_mut_obj_add_val(doc.get(), o, key, v));
  }
  void str(yyjson_mut_val *o, const char *key, const char *v) {
    add(o, key, checked(yyjson_mut_strcpy(doc.get(), v)));
  }
  void num(yyjson_mut_val *o, const char *key, size_t v) {
    add(o, key, checked(yyjson_mut_uint(doc.get(), v)));
  }
  void boolean(yyjson_mut_val *o, const char *key, bool v) {
    add(o, key, checked(yyjson_mut_bool(doc.get(), v)));
  }
  void push(yyjson_mut_val *a, yyjson_mut_val *v) {
    checked(yyjson_mut_arr_append(a, v));
  }
  yyjson_mut_val *names(char **items, uint32_t count) {
    auto *a = array();
    for (uint32_t i = 0; i < count; ++i)
      push(a, checked(yyjson_mut_strcpy(doc.get(), items[i])));
    return a;
  }
  void print(yyjson_mut_val *root, Clock::time_point start) {
    double seconds =
        std::chrono::duration<double>(Clock::now() - start).count();
    add(root, "wall_seconds", checked(yyjson_mut_real(doc.get(), seconds)));
    yyjson_mut_doc_set_root(doc.get(), root);
    size_t len;
    std::unique_ptr<char, decltype(&free)> text{
        checked(yyjson_mut_write(doc.get(), 0, &len)), free};
    if (fwrite(text.get(), 1, len, stdout) != len || putchar('\n') == EOF ||
        fflush(stdout) != 0)
      throw std::runtime_error("cannot write census");
  }
};

static int census(const std::string &text, Clock::time_point start) {
  // Keep the library's actual diagnostic for unresolved parameters, finite
  // semantics, etc. A failed conversion never produces a verified generator.
  char *diagnostic = nullptr;
  size_t diagnostic_size = 0;
  FILE *stream = checked(open_memstream(&diagnostic, &diagnostic_size));
  FILE *previous = tlsf_diagnostic_swap(stream);
  std::unique_ptr<TlsfConversionResult, decltype(&tlsf_conversion_result_free)>
      c{tlsf_convert(text.c_str(), "Mealy"), tlsf_conversion_result_free};
  tlsf_diagnostic_swap(previous);
  int closed = fclose(stream);
  std::unique_ptr<char, decltype(&free)> message{diagnostic, free};
  if (closed != 0)
    throw std::runtime_error("cannot capture conversion diagnostic");

  Json j;
  auto *result = j.object();
  j.str(
      result, "limitations",
      "The census is a lower bound: different concrete bounds are not coupled, "
      "families on the same range are only permuted together, enum families "
      "permute encoding bits, and canonical inequality is inconclusive.");
  auto *families = j.array();
  auto *ranges = j.array();
  j.add(result, "families", families);
  j.add(result, "ranges", ranges);
  if (!c) {
    j.str(result, "status", "unverified");
    j.str(result, "reason",
          diagnostic_size ? message.get() : "conversion failed");
    j.add(result, "summary", checked(yyjson_mut_null(j.doc.get())));
    j.print(result, start);
    return 1;
  }
  j.str(result, "semantics", c->semantics);
  j.str(result, "original_target", c->original_target);
  j.str(result, "effective_target", c->effective_target);
  j.add(result, "inputs", j.names(c->inputs, c->n_inputs));
  j.add(result, "outputs", j.names(c->outputs, c->n_outputs));

  TlsfSymmetryResult *raw = nullptr;
  TlsfSymmetryStatus status = tlsf_symmetry_detect(c.get(), &raw);
  if (status == TLSF_SYMMETRY_NO_MEMORY)
    throw std::bad_alloc();
  if (status != TLSF_SYMMETRY_OK)
    throw std::runtime_error("symmetry detection failed");
  std::unique_ptr<TlsfSymmetryResult, decltype(&tlsf_symmetry_result_free)>
      census{raw, tlsf_symmetry_result_free};

  for (uint32_t i = 0; i < c->n_indexed_families; ++i) {
    const auto &f = c->indexed_families[i];
    auto *family = j.object();
    j.str(family, "origin_name", f.origin_name);
    j.add(family, "members", j.names(f.members, f.n_members));
    j.num(family, "lo", f.lo);
    j.num(family, "hi", f.hi);
    j.num(family, "size", f.n_members);
    j.boolean(family, "is_output", f.is_output);
    j.boolean(family, "is_enum", f.is_enum);
    j.push(families, family);
  }
  j.str(result, "status", census->reason ? "unverified" : "ok");
  if (census->reason)
    j.str(result, "reason", census->reason);

  auto *sizes = j.array();
  for (size_t i = 0; i < census->n_ranges; ++i) {
    const auto &r = census->ranges[i];
    size_t size = static_cast<size_t>(r.hi) - r.lo + 1;
    auto *range = j.object();
    auto *candidates = j.array();
    auto *family_ids = j.array();
    j.num(range, "lo", r.lo);
    j.num(range, "hi", r.hi);
    j.num(range, "size", size);
    j.num(range, "n_families", r.n_families);
    j.add(range, "families", family_ids);
    j.add(range, "candidates", candidates);
    j.push(ranges, range);
    j.push(sizes, checked(yyjson_mut_uint(j.doc.get(), size)));
    for (size_t k = 0; k < r.n_families; ++k)
      j.push(family_ids, checked(yyjson_mut_uint(j.doc.get(), r.families[k])));
    for (size_t k = 0; k < r.n_candidates; ++k) {
      const auto &c = r.candidates[k];
      auto *candidate = j.object();
      auto *image = j.array();
      j.str(candidate, "kind",
            c.kind == TLSF_SYMMETRY_ROTATION ? "rotation" : "adjacent");
      for (size_t n = 0; n < size; ++n)
        j.push(image, checked(yyjson_mut_uint(j.doc.get(), c.image[n])));
      j.add(candidate, "image", image);
      j.boolean(candidate, "verified", c.generator != SIZE_MAX);
      if (c.reason)
        j.str(candidate, "reason", c.reason);
      j.push(candidates, candidate);
    }
    if (r.reason)
      j.str(range, "reason", r.reason);
    j.str(range, "verified_group",
          r.verdict == TLSF_SYMMETRY_SYMMETRIC ? "symmetric"
          : r.verdict == TLSF_SYMMETRY_CYCLIC  ? "cyclic"
                                               : "none");
  }
  auto *summary = j.object();
  j.num(summary, "n_families", c->n_indexed_families);
  j.num(summary, "n_ranges", census->n_ranges);
  j.add(summary, "range_sizes", sizes);
  j.add(result, "summary", summary);
  j.print(result, start);
  return 0;
}

int main(int argc, char **argv) {
  auto start = Clock::now();
  if (argc == 2 && std::string(argv[1]) == "--version") {
    printf("tlsfsym %s\n", TLSF_PROJECT_VERSION);
    return 0;
  }
  if (argc != 2 || std::string(argv[1]) == "--help") {
    fputs("Usage: tlsfsym FILE\n"
          "Census of declared index permutations of the native Mealy "
          "objective.\n",
          argc == 2 ? stdout : stderr);
    return argc == 2 ? 0 : 1;
  }
  try {
    std::ifstream input(argv[1]);
    if (!input)
      throw std::runtime_error("cannot open input file");
    std::string text{std::istreambuf_iterator<char>(input), {}};
    if (input.bad())
      throw std::runtime_error("cannot read input file");
    return census(text, start);
  } catch (const std::exception &e) {
    fprintf(stderr, "tlsfsym: %s\n", e.what());
    return 1;
  }
}
