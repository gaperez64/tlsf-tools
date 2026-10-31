// Offline inventory of precisely the monitor constructors the reduction
// reaches. The wrapper changes only the requested admission policy, then calls
// the real constructor. Failed reductions still retain every reached formula on
// stdout.
#define main tv_native_reduction_main
#include "../../test/api/native_reduction.cpp"
#undef main
extern "C" {
#include "dpa_buchi.h"
#include "tlsf/convert.h"
TlsfDpaStatus __real_dpa_buchi_create(const TlsfAstNode *, const char *const *,
                                      uint32_t, const TlsfDpaBudget *,
                                      TlsfDpa **, char *);
}

static bool general_admission;

static void prefix(const TlsfAstNode *f) {
  static const char *ops[] = {"1", "0", "",  "!", "&", "|", "i", "e",
                              "X", "x", "F", "G", "U", "R", "W", "M"};
  auto kind = tlsf_ast_node_kind(f);
  if (kind == TLSF_AST_AP)
    std::cout << '$' << tlsf_ast_node_ap_name(f) << ' ';
  else
    std::cout << ops[kind] << ' ';
  for (uint32_t i = 0; i < tlsf_ast_node_child_count(f); ++i)
    prefix(tlsf_ast_node_child(f, i));
}

extern "C" TlsfDpaStatus __wrap_dpa_buchi_create(const TlsfAstNode *root,
                                                 const char *const *names,
                                                 uint32_t count,
                                                 const TlsfDpaBudget *budget,
                                                 TlsfDpa **out, char *klass) {
  std::cout << "TV1 parity " << (general_admission ? "general" : "default")
            << ' ' << count << ' ';
  for (uint32_t i = 0; i < count; ++i)
    std::cout << names[i] << ' ';
  prefix(root);
  std::cout << std::endl;
  TlsfDpaBudget selected = *budget;
  selected.allow_unproved = general_admission;
  return __real_dpa_buchi_create(root, names, count, &selected, out, klass);
}

int main(int argc, char **argv) {
  if (argc == 3 && std::string(argv[1]) == "--ground") {
    std::ifstream in(argv[2]);
    if (!in)
      return 2;
    std::string bytes((std::istreambuf_iterator<char>(in)), {});
    auto *converted = tlsf_convert(bytes.c_str(), "Mealy");
    if (!converted)
      return 2;
    std::cout << "TV1 parity default "
              << converted->n_inputs + converted->n_outputs << ' ';
    for (uint32_t i = 0; i < converted->n_inputs; ++i)
      std::cout << converted->inputs[i] << ' ';
    for (uint32_t i = 0; i < converted->n_outputs; ++i)
      std::cout << converted->outputs[i] << ' ';
    prefix(tlsf_ast_root(converted->ast));
    std::cout << std::endl;
    tlsf_conversion_result_free(converted);
    return 0;
  }
  if (argc < 2 ||
      (std::string(argv[1]) != "default" && std::string(argv[1]) != "general"))
    return 2;
  general_admission = std::string(argv[1]) == "general";
  return tv_native_reduction_main(argc - 1, argv + 1);
}
