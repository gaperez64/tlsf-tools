# Internal units: these may include libtlsf's private headers.

dpa_equivalence = executable('dpa_equivalence', 'dpa_equivalence.cpp',
  cpp_args: ['-DDPA_GOLDEN_DIR="' + (meson.project_source_root() / 'test/fixtures/golden/dpa') + '"'],
  dependencies: tlsf_internal_dep)
dpa_contract = executable('dpa_contract', 'dpa_contract.c',
  c_args: ['-UNDEBUG'],
  link_args: ['-Wl,--wrap=oxidd_host_calloc', '-Wl,--wrap=oxidd_bdd_ite',
    '-Wl,--wrap=oxidd_bdd_not', '-Wl,--wrap=oxidd_bdd_and',
    '-Wl,--wrap=oxidd_bdd_or', '-Wl,--wrap=oxidd_bdd_cofactor_false',
    '-Wl,--wrap=oxidd_bdd_cofactor_true'],
  dependencies: tlsf_internal_dep)
test('dpa_contract', dpa_contract, timeout: 120)
test('dpa_equivalence', dpa_equivalence, timeout: 120)
test('dpa_buchi_goldens', dpa_equivalence, args: ['--buchi'], timeout: 120)
test('dpa_equivalence_research', dpa_equivalence,
  args: ['--allow-unproved'], timeout: 120)
test('dpa_limits', dpa_equivalence,
  args: [files('dpa_limits.ltl'), '--allow-unproved', '--expect-bdd-limit'],
  timeout: 120)
dpa_stage2 = executable('dpa_stage2', 'dpa_stage2.c',
  c_args: ['-UNDEBUG'], dependencies: tlsf_internal_dep)
test('dpa_stage2', dpa_stage2, timeout: 120)
foreach mode : ['default', 'research']
  test('dpa_random_' + mode, python3,
    args: [files('dpa_random.py'), dpa_equivalence,
           meson.project_source_root() / 'test/fixtures/golden/dpa/random.ltl', mode],
    timeout: 120)
endforeach
dpa_admission = executable('dpa_admission', 'dpa_admission.c',
  dependencies: tlsf_internal_dep)
test('dpa_delta2', python3, args: [files('dpa_delta2.py'), dpa_equivalence,
  meson.project_source_root() / 'test/fixtures/golden/dpa/delta2.ltl'], timeout: 300)

objective_cli = static_library('objective-cli',
  files('../../src/tools/tlsf2ltl/main.c'),
  c_args: ['-Dmain=objective_cli_main'], dependencies: tool_dep)
objective_alloc_exe = executable('objective_alloc', 'objective_alloc.c',
  files('../../src/lib/arena.c'), c_args: ['-DTLSF_ARENA_FAULT'],
  link_with: objective_cli,
  link_args: ['-Wl,--wrap=build_spec_formula', '-Wl,--wrap=malloc',
              '-Wl,--wrap=calloc', '-Wl,--wrap=realloc',
              '-Wl,--wrap=open_memstream', '-Wl,--wrap=fmemopen',
              '-Wl,--wrap=fputc', '-Wl,--wrap=fputs', '-Wl,--wrap=fprintf',
              '-Wl,--wrap=cover_build', '-Wl,--wrap=csnf_compose'],
  dependencies: tool_dep)
test('objective_alloc', objective_alloc_exe)

if research_tools
  pruning_cache = executable('pruning_cache', 'pruning_cache.c',
    link_args: ['-Wl,--wrap=env_witness_search'],
    dependencies: tlsf_internal_dep)
  test('pruning_cache', pruning_cache)
  phase_b_probe = executable('phase_b_probe', 'phase_b_probe.c',
    dependencies: tlsf_internal_dep)
  residual_fault = executable('residual-fault', 'research_fault.c',
    files('../../src/tools/tlsfresidual/main.c'),
    c_args: ['-DRESIDUAL_FAULT'],
    link_args: ['-Wl,--wrap=residual_cluster_keys', '-Wl,--wrap=malloc'],
    dependencies: tool_dep)
  template_fault = executable('template-fault', 'research_fault.c',
    files('../../src/tools/tlsftemplates/main.c'),
    link_args: ['-Wl,--wrap=csnf_emit_lines', '-Wl,--wrap=csnf_emit_text',
                '-Wl,--wrap=open_memstream'],
    dependencies: tool_dep)
  composition_fault = executable('composition-fault', 'research_fault.c',
    tools['tlsfcompose']['sources'],
    c_args: ['-DCOMPOSITION_FAULT'],
    link_args: ['-Wl,--wrap=csnf_compose', '-Wl,--wrap=malloc',
                '-Wl,--wrap=calloc', '-Wl,--wrap=realloc'],
    dependencies: tools['tlsfcompose']['dependencies'])
endif

# Header-only: the SIMD kernels in src/lib/simd.h.
simd_check_exe = executable('simd_check', 'simd_check.c',
                            include_directories: lib_inc)
test('simd_kernels', simd_check_exe)

native_contract_api_exe = executable('native_contract_api',
  'native_contract_api.cpp', reduction_contract_hooks, gr1_reduction_source,
  cpp_args: ['-DTLSF_GR1_REDUCTION_TEST_FAULT'],
  dependencies: tlsf_internal_dep)
test('native_contract_validators', native_contract_api_exe)
native_env_contract_api_exe = executable('native_env_contract_api',
  'native_env_contract_api.cpp', dependencies: tlsf_internal_dep)
test('native_env_contract_validators', native_env_contract_api_exe)
# gr1_lift.cc again, with its fault hooks compiled in; its own object takes
# precedence over the library's copy.
native_lift_api_exe = executable('native_lift_api',
  'native_lift_api.cpp', gr1_lift_source,
  cpp_args: ['-DTLSF_GR1_LIFT_TEST_FAULT'],
  dependencies: tlsf_internal_dep)
test('native_lift_api', native_lift_api_exe, timeout: 60, is_parallel: false)
native_both_api_exe = executable('native_both_api',
  'native_both_api.cpp', gr1_lift_source, gr1_env_lift_source,
  cpp_args: ['-DTLSF_GR1_LIFT_TEST_FAULT'],
  dependencies: tlsf_internal_dep)
test('native_both_api', native_both_api_exe,
  args: files('../oracle/env_lift_one.tlsf'),
  timeout: get_option('buildtype') == 'debug' ? 180 : 90,
  is_parallel: false)
# Three added corruption cases each retain the worker's 30-second deadline.
test('native_failure_census', native_both_api_exe,
  args: [files('../oracle/env_lift_one.tlsf'), '--fault-census'],
  timeout: get_option('buildtype') == 'debug' ? 270 : 180,
  is_parallel: false)
test('native_corruption_guards', native_both_api_exe,
  args: [files('../oracle/env_lift_one.tlsf'), '--corruption-guards'],
  timeout: get_option('buildtype') == 'debug' ? 180 : 90,
  is_parallel: false)
native_real_both_api_exe = executable('native_real_both_api',
  'native_real_both_api.cpp', gr1_lift_source, gr1_env_lift_source,
  cpp_args: ['-DTLSF_GR1_LIFT_TEST_FAULT'],
  dependencies: tlsf_internal_dep)
test('native_real_both_api', native_real_both_api_exe,
  args: files('../oracle/env_lift_one.tlsf'),
  timeout: 30, is_parallel: false)
native_env_real_api_exe = executable('native_env_real_api',
  'native_env_real_api.cpp', dependencies: tlsf_internal_dep)
test('native_env_real_negative_control', native_env_real_api_exe,
  timeout: 90, is_parallel: false)
env_rank_probe_exe = executable('env_rank_probe', 'env_rank_probe.cpp',
  dependencies: tlsf_internal_dep)
env_rank_fault_probe_exe = executable('env_rank_fault_probe',
  'env_rank_probe.cpp', gr1_lift_source, gr1_env_lift_source,
  cpp_args: ['-DTLSF_GR1_LIFT_TEST_FAULT'],
  dependencies: tlsf_internal_dep)

if research_tools
  oxidd_memory_test = executable('oxidd_memory_test', 'oxidd_memory.c',
    link_args: ['-Wl,--wrap=oxidd_bdd_and', '-Wl,--wrap=oxidd_bdd_substitute',
                '-Wl,--wrap=oxidd_bdd_apply_exists', '-Wl,--wrap=oxidd_bdd_forall',
                '-Wl,--wrap=oxidd_bdd_exists', '-Wl,--wrap=oxidd_bdd_restrict',
                '-Wl,--wrap=calloc', '-Wl,--wrap=oxidd_host_realloc'],
    dependencies: tlsf_oxidd_dep)
  test('oxidd_memory', oxidd_memory_test)

  aiger_game_roundtrip_exe = executable('aiger-game-roundtrip',
    'aiger_game_roundtrip.c', dependencies: tlsf_oxidd_dep)
  test('aiger_game_roundtrip', aiger_game_roundtrip_exe)
endif

if host_machine.system() == 'linux'
  oxidd_runtime_exe = executable('oxidd_runtime', 'oxidd_runtime.c',
                                 dependencies: tlsf_internal_dep)
  foreach mib : ['0', '64', '512', '1024', '2048', '32768']
    test('oxidd_runtime_' + mib, oxidd_runtime_exe, args: [mib],
         is_parallel: false)
  endforeach
endif

# Diagnostic inventory; not a test and never used by the production reducer.
gr1_admission = executable('gr1_admission', 'gr1_admission.cpp',
  dependencies: tlsf_internal_dep)
env_witness = executable('env_witness', 'env_witness.c',
  c_args: ['-UNDEBUG'], dependencies: tlsf_internal_dep)
test('env_witness', env_witness)
