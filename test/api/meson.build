# Public-API clients. They see only include/ (through tlsf_dep), so a private
# header here fails to compile, as it would for an installed consumer.

foreach name : ['ast_visitor', 'aiger_roundtrip']
  test(name, executable(name, name + '.c', dependencies: tlsf_dep))
endforeach
foreach name : ['decompose_cpp', 'visitor_cpp']
  test(name, executable(name, name + '.cpp', dependencies: tlsf_dep))
endforeach

if spot_dep.found()
  test('tlsf2spot', tlsf2spot_exe, args: [files(cases / 'cluster_split.tlsf')])
endif

if native_gr1
  native_lift_exe = executable('native_lift', 'native_lift.cpp',
                               dependencies: tlsf_dep)
  native_lift_c_exe = executable('native_lift_c', 'native_lift_c.c',
                                 dependencies: tlsf_dep, link_language: 'c')
  test('native_lift_c', native_lift_c_exe, timeout: 10, is_parallel: false)
  native_reduction_exe = executable('native_reduction', 'native_reduction.cpp',
                                    dependencies: tlsf_dep)
  native_reduction_c_exe = executable('native_reduction_c',
    'native_reduction_c.c', dependencies: tlsf_dep, link_language: 'c')
  test('native_reduction_c', native_reduction_c_exe)
  native_api_c_exe = executable('native_api_c', 'native_api.c',
                                dependencies: tlsf_dep)
  test('native_api_c', native_api_c_exe)
  oxidd_manager_lifetime_exe = executable('oxidd_manager_lifetime',
    'oxidd_manager_lifetime.c', dependencies: tlsf_dep)
  test('oxidd_manager_lifetime_manager', oxidd_manager_lifetime_exe,
    args: ['manager', meson.project_source_root()], timeout: 120,
    is_parallel: false)
  test('oxidd_manager_lifetime_checker', oxidd_manager_lifetime_exe,
    args: ['checker',
           meson.project_source_root() / 'test/fixtures/oxidd-manager-lifetime'],
    timeout: 900, is_parallel: false)
  native_api_cpp_exe = executable('native_api_cpp', 'native_api_cpp.cpp',
                                  dependencies: tlsf_dep)
  test('native_api_cpp', native_api_cpp_exe)
  if host_machine.system() == 'linux'
    native_api_failure_exe = executable('native_api_failure',
      'native_api_failure.c', dependencies: tlsf_dep,
      link_args: ['-Wl,--wrap=malloc', '-Wl,--wrap=calloc',
                  '-Wl,--wrap=oxidd_host_calloc',
                  '-Wl,--wrap=oxidd_host_realloc'])
    test('native_api_failure', native_api_failure_exe)
  endif
endif

# The layout rules: one target per source, installed headers == include/tlsf,
# and no include from the library into a tool or from the API into internals.
if python3.found()
  test('source_layout', python3,
    args: [files('check_layout.py'), meson.project_source_root(),
           meson.project_build_root()])
endif
