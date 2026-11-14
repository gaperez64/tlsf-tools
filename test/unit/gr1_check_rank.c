// Include the engine to inspect its private rank owners and setup failures.
#define _GNU_SOURCE
#include <stdlib.h>
static void *rank_calloc(size_t count, size_t size);
#define calloc rank_calloc
#include "../../src/lib/gr1_check.c"
#undef calloc
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>

static size_t allocations, fail_at, live, and_calls, fail_and;
static bool bdd_oom;
static struct {
  Bdd value;
  size_t refs;
} owned[1u << 18];

static void *rank_calloc(size_t count, size_t size) {
  return ++allocations == fail_at ? nullptr : calloc(count, size);
}
static size_t handle_index(Bdd value) {
  size_t mask = sizeof owned / sizeof *owned - 1;
  size_t i = (value._i * 2654435761u + (uintptr_t)value._p) & mask;
  size_t probes = 0;
  while (owned[i].value._p &&
         (owned[i].value._p != value._p || owned[i].value._i != value._i)) {
    assert(++probes <= mask);
    i = (i + 1) & mask;
  }
  owned[i].value = value;
  return i;
}
static Bdd acquire(Bdd value) {
  if (value._p) {
    ++owned[handle_index(value)].refs;
    ++live;
  }
  return value;
}
#define WRAP(name, args, call)                                                 \
  Bdd __real_oxidd_bdd_##name args;                                            \
  Bdd __wrap_oxidd_bdd_##name args;                                            \
  Bdd __wrap_oxidd_bdd_##name args {                                           \
    return acquire(__real_oxidd_bdd_##name call);                              \
  }
WRAP(ref, (Bdd a), (a))
WRAP(not, (Bdd a), (a))
WRAP(true, (oxidd_bdd_manager_t m), (m))
WRAP(false, (oxidd_bdd_manager_t m), (m))
WRAP(var, (oxidd_bdd_manager_t m, oxidd_var_no_t v), (m, v))
WRAP(or, (Bdd a, Bdd b), (a, b))
WRAP(xor, (Bdd a, Bdd b), (a, b))
WRAP(equiv, (Bdd a, Bdd b), (a, b))
WRAP(forall, (Bdd a, Bdd b), (a, b))
WRAP(exists, (Bdd a, Bdd b), (a, b))
WRAP(restrict, (Bdd a, Bdd b), (a, b))
WRAP(substitute, (Bdd a, const oxidd_bdd_substitution_t *s), (a, s))
WRAP(cofactor_true, (Bdd a), (a))
WRAP(cofactor_false, (Bdd a), (a))
WRAP(apply_exists, (oxidd_boolean_operator op, Bdd a, Bdd b, Bdd c),
     (op, a, b, c))
Bdd __real_oxidd_bdd_and(Bdd a, Bdd b);
Bdd __wrap_oxidd_bdd_and(Bdd a, Bdd b);
Bdd __wrap_oxidd_bdd_and(Bdd a, Bdd b) {
  return bdd_oom || (++and_calls >= fail_and && fail_and)
             ? (Bdd){0}
             : acquire(__real_oxidd_bdd_and(a, b));
}
oxidd_bdd_pair_t __real_oxidd_bdd_cofactors(Bdd a);
oxidd_bdd_pair_t __wrap_oxidd_bdd_cofactors(Bdd a);
oxidd_bdd_pair_t __wrap_oxidd_bdd_cofactors(Bdd a) {
  oxidd_bdd_pair_t pair = __real_oxidd_bdd_cofactors(a);
  acquire(pair.first);
  acquire(pair.second);
  return pair;
}
void __real_oxidd_bdd_unref(Bdd a);
void __wrap_oxidd_bdd_unref(Bdd a);
void __wrap_oxidd_bdd_unref(Bdd a) {
  if (a._p) {
    size_t i = handle_index(a);
    assert(owned[i].refs > 0 && live > 0);
    --owned[i].refs;
    --live;
  }
  __real_oxidd_bdd_unref(a);
}

static Checker fixture(uint32_t fair, bool valid) {
  Checker ck = {.options = {.method = METHOD_REGION,
                            .node_cap = 4096,
                            .cache_cap = 1024,
                            .quiet = true},
                .nstate = 1,
                .nin = 2,
                .nu = 1,
                .nc = 1,
                .ngoals = 3,
                .nfair = fair,
                .nfair_disj = fair ? fair : 1,
                .started = now_seconds()};
  ck.game = aig_new();
  uint32_t u = aig_input(ck.game, "u");
  uint32_t c = aig_input(ck.game, "controllable_c");
  aig_set_output(ck.game, "bad", aig_and(ck.game, u, c));
  uint32_t state = aig_latch_named(ck.game, 1, 0, "q");
  for (uint32_t j = 0; j < ck.ngoals; ++j)
    aig_add_justice(ck.game, &state, 1, "goal");
  for (uint32_t i = 0; i < fair; ++i)
    aig_add_fairness(ck.game, state, "fair");
  ck.certificate = aig_new();
  state = aig_input(ck.certificate, "q");
  aig_set_output(ck.certificate, "inv", valid ? 1 : 0);
  const uint32_t levels[] = {2, 3, 1};
  char name[64];
  for (uint32_t j = 0; j < ck.ngoals; ++j) {
    snprintf(name, sizeof name, "goal_%u", j);
    aig_set_output(ck.certificate, name, state);
    for (uint32_t k = 0; k < levels[j]; ++k) {
      snprintf(name, sizeof name, "y_%u_%u", j, k);
      aig_set_output(ck.certificate, name, 1);
      for (uint32_t i = 0; i < ck.nfair_disj; ++i) {
        snprintf(name, sizeof name, "x_%u_%u_%u", j, k, i);
        // Four distinguishable functions expose both wrong strides and rows.
        uint32_t lit = (j + k + i) % 4;
        aig_set_output(ck.certificate, name, valid ? 1 : lit);
      }
    }
  }
  allocations = 0;
  return ck;
}
static void balanced(Checker *ck) {
  cleanup(ck);
  assert(live == 0);
  for (size_t i = 0; i < sizeof owned / sizeof *owned; ++i)
    assert(owned[i].refs == 0);
  memset(owned, 0, sizeof owned);
}
static size_t polls, interrupt_at;
static bool interrupt_deadline;
static int interrupted(void *context) {
  if (++polls != interrupt_at)
    return 0;
  if (!interrupt_deadline)
    return 1;
  ((Checker *)context)->bdd_options.deadline_mono_ns = 1;
  return 0;
}
// Reuse the real CLI so mutation/differential suites audit every teardown too.
int rank_cli_main(int argc, char **argv);
#define main rank_cli_main
#include "../../src/tools/tlsfcertcheck/main.c"
#undef main
int main(int argc, char **argv) {
  if (argc > 1) {
    int result = rank_cli_main(argc, argv);
    assert(live == 0);
    return result;
  }
  const uint32_t levels[] = {2, 3, 1};
  char message[512];
  for (uint32_t fair = 0; fair <= 3; ++fair) {
    Checker ck = fixture(fair, false);
    assert(setup_bdds(&ck, levels, message, sizeof message));
    size_t count = allocations;
    for (uint32_t j = 0; j < ck.ngoals; ++j)
      for (uint32_t k = 0; k < levels[j]; ++k)
        for (uint32_t i = 0; i < ck.nfair_disj; ++i) {
          uint32_t lit = (j + k + i) % 4;
          Bdd expected = lit < 2 ? (lit ? oxidd_bdd_true(ck.manager)
                                        : oxidd_bdd_false(ck.manager))
                                 : (lit == 2 ? oxidd_bdd_ref(ck.q[0])
                                             : oxidd_bdd_not(ck.q[0]));
          assert(bdd_eq(rank_x(&ck, j, k, i), expected));
          oxidd_bdd_unref(expected);
        }
    assert(check_region_mode(&ck) == CHECK_CERT_FAILED);
    balanced(&ck);
    // Fail every checker-owned calloc, including both arrays of every goal.
    for (fail_at = 1; fail_at <= count; ++fail_at) {
      ck = fixture(fair, false);
      assert(!setup_bdds(&ck, levels, message, sizeof message));
      balanced(&ck);
    }
    fail_at = 0;
    size_t proof_ands = 0, setup_polls = 0, proof_polls = 0;
    for (unsigned stop = 0; stop < 2; ++stop) {
      ck = fixture(fair, true);
      ck.options.cancelled = interrupted;
      ck.options.cancel_ctx = &ck;
      polls = 0;
      assert(setup_bdds(&ck, levels, message, sizeof message));
      setup_polls = polls;
      // Leave only the runtime callback armed, excluding outer checkpoints.
      ck.options.cancelled = nullptr;
      if (stop == 1)
        bdd_oom = true;
      and_calls = polls = 0;
      CheckResult result = check_region_mode(&ck);
      assert(result == (stop ? CHECK_UNKNOWN : CHECK_VERIFIED));
      if (!stop) {
        proof_ands = and_calls;
        proof_polls = polls;
      }
      bdd_oom = false;
      balanced(&ck);
    }
    assert(setup_polls && proof_polls);
    // Interrupt every runtime poll in setup and the rank proof, for each
    // reason.
    for (unsigned proof = 0; proof < 2; ++proof)
      for (unsigned deadline = 0; deadline < 2; ++deadline)
        for (size_t point = 1; point <= (proof ? proof_polls : setup_polls);
             ++point) {
          ck = fixture(fair, true);
          ck.options.cancelled = interrupted;
          ck.options.cancel_ctx = &ck;
          interrupt_deadline = deadline;
          interrupt_at = proof ? 0 : point;
          polls = 0;
          bool ready = setup_bdds(&ck, levels, message, sizeof message);
          if (proof) {
            assert(ready);
            ck.options.cancelled = nullptr;
            interrupt_at = point;
            polls = 0;
            assert(check_region_mode(&ck) == CHECK_UNKNOWN);
          } else {
            assert(!ready);
          }
          assert(polls == point && ck.run.stopped);
          assert(ck.failure.kind ==
                 (deadline ? OXIDD_FAILURE_DEADLINE : OXIDD_FAILURE_CANCELLED));
          interrupt_at = 0;
          balanced(&ck);
        }
    for (size_t failure = 1; failure <= proof_ands; ++failure) {
      ck = fixture(fair, true);
      assert(setup_bdds(&ck, levels, message, sizeof message));
      and_calls = 0;
      fail_and = failure;
      assert(check_region_mode(&ck) == CHECK_UNKNOWN);
      fail_and = 0;
      balanced(&ck);
    }
    printf("fair=%u: %zu allocation failures, %zu AND failures, indexing, "
           "rejection, BDD OOM, "
           "%zu setup + %zu proof deadline/cancellation points: balanced\n",
           fair, count, proof_ands, setup_polls, proof_polls);
  }
  return 0;
}
