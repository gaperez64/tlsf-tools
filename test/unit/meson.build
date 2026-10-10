# Internal units: these may include libtlsf's private headers.

# Header-only: the SIMD kernels in src/lib/simd.h.
simd_check_exe = executable('simd_check', 'simd_check.c',
                            include_directories: lib_inc)
test('simd_kernels', simd_check_exe)

if native_gr1
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
endif

if research_tools and have_oxidd
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
