# Internal units: these may include libtlsf's private headers.

# Header-only: the SIMD kernels in src/lib/simd.h.
simd_check_exe = executable('simd_check', 'simd_check.c',
                            include_directories: lib_inc)
test('simd_kernels', simd_check_exe)

if native_gr1
  # gr1_lift.cc again, with its fault hooks compiled in; its own object takes
  # precedence over the library's copy.
  native_lift_api_exe = executable('native_lift_api',
    'native_lift_api.cpp', gr1_lift_source,
    cpp_args: ['-DTLSF_GR1_LIFT_TEST_FAULT'],
    dependencies: tlsf_internal_dep)
  test('native_lift_api', native_lift_api_exe, timeout: 30, is_parallel: false)
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
