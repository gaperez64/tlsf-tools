#define main tlsfsym_main
#include "../../src/tools/tlsfsym/main.cpp"
#undef main
#include "../check.h"

#include <limits>

static constexpr size_t unlimited = std::numeric_limits<size_t>::max();
static size_t budget = unlimited;
static size_t allocations;

void *operator new(size_t size) {
  if (budget == 0)
    throw std::bad_alloc();
  if (budget != unlimited)
    --budget;
  ++allocations;
  if (void *p = std::malloc(size ? size : 1))
    return p;
  throw std::bad_alloc();
}
// Keep replacement deletes opaque to GCC's mismatched-new-delete diagnostic.
[[gnu::noinline]] void operator delete(void *p) noexcept { std::free(p); }
[[gnu::noinline]] void operator delete(void *p, size_t) noexcept {
  std::free(p);
}

int main() {
  Dag dag;
  for (Id ap = 0; ap < 128; ++ap)
    dag.intern({TLSF_AST_AP, ap, {}});
  std::vector<Id> identity(128);
  std::iota(identity.begin(), identity.end(), 0);

  // AP-only candidates need just the image vector, independent of DAG size.
  // Copying the original node table would allocate once per hash-table entry.
  allocations = 0;
  CHECK(dag.invariant(0, identity));
  CHECK(allocations == 1);

  // Enough shared, ordered nodes to grow and rehash the candidate table.
  std::vector<Id> children;
  for (Id ap = 2; ap < 34; ++ap)
    children.push_back(dag.intern({TLSF_AST_IMPL, 0, {0, ap}}));
  Id root = dag.intern({TLSF_AST_AND, 0, std::move(children)});
  const auto nodes = dag.nodes;
  const auto ids = dag.ids;
  auto swapped = identity;
  std::swap(swapped[0], swapped[1]);
  CHECK(!dag.invariant(root, swapped));
  CHECK(dag.invariant(root, identity));

  // Fail every C++ allocation in a candidate, then reuse the unchanged base.
  size_t failures = 0;
  for (size_t fail = 0;; ++fail) {
    CHECK(fail < 1000);
    budget = fail;
    try {
      bool verified = dag.invariant(root, swapped);
      budget = unlimited;
      CHECK(!verified);
      break;
    } catch (const std::bad_alloc &) {
      budget = unlimited;
      ++failures;
      CHECK(dag.nodes == nodes && dag.ids == ids);
      CHECK(dag.invariant(root, identity));
    }
  }
  CHECK(failures > 0);
  CHECK(dag.nodes == nodes && dag.ids == ids);
  printf("overlay: one identity allocation; %zu OOM points recovered\n",
         failures);
}
