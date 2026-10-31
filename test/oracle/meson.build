# Python oracles and differentials: independent re-derivations of the tools'
# and the library's answers.

if python3.found()
  aigtoaig_check = find_program('aigtoaig', required: false)
  aigmove_check = find_program('aigmove', required: false)
  combine_aiger_check = find_program('combine-aiger', required: false)
  abc_check = find_program('abc', required: false)
  if aigtoaig_check.found() and aigmove_check.found() and combine_aiger_check.found() and abc_check.found()
    test('aiger_closed_loop', python3,
      args: [files('check_aiger_safety.py'),
             '--aiger-dir', fs.parent(aigtoaig_check.full_path()),
             '--combine-aiger', combine_aiger_check.full_path(),
             '--abc', abc_check.full_path()], timeout: 120)
  endif
endif

if python3.found()
  test('native_env_rank_api', python3,
    args: [files('check_env_rank_api.py'),
           '--binary', env_rank_fault_probe_exe,
           '--fixture', files('env_rank_learner.tlsf'),
           '--out', meson.project_build_root() / 'env-rank-api'],
    # Small learner fixture keeps the debug build comfortably below 30 s.
    timeout: 90, is_parallel: false)
  test('native_env_lift_api', python3,
    args: [files('check_env_lift_api.py'),
           '--binary', env_rank_fault_probe_exe,
           '--fixtures', meson.project_source_root() / 'test/oracle',
           '--out', meson.project_build_root() / 'env-lift-api'],
    # Three-fairness and test-only capped capacity keep debug work small.
    timeout: 90, is_parallel: false)
  test('typed_provenance', python3,
    args: [files('test_typed_provenance.py'),
           '--frontend', exe['tlsf2tlsf'],
           '--reducer', gr1_environment_reduce_exe,
           '--enum-fixture', files(cases / 'enum_demo.tlsf'),
           '--builddir', meson.project_build_root()],
    timeout: 120)
endif
# These scripts locate their helpers under --builddir. Declare those targets
# explicitly so `meson test` also works without a preceding full build.
native_lift_test_deps = [native_lift_exe]
if research_tools
  native_lift_test_deps += [exe['tlsfcertcheck']]
endif
foreach suite, helpers : {
  'native_lift_differential': native_lift_test_deps,
  'native_reduction': [native_reduction_exe],
  'native_reduction_language': [native_reduction_exe, exe['tlsf2ltl']],
  'native_reduction_strict': [native_reduction_exe],
}
  test(suite, python3,
    args: [files('test_' + suite + '.py'), '--builddir', meson.project_build_root()],
    depends: helpers,
    timeout: 1800, is_parallel: false)
endforeach

if research_tools
  test('assumption_pruning_guards', python3,
    args: [files('test_assumption_pruning.py'), exe['tlsf2ltl'],
           exe['tlsfresidual'], exe['tlsfcompose']], timeout: 90)
  test('disjoint_assumptions_equivalent', python3,
    args: [files('test_disjoint_assumptions.py'), exe['tlsf2ltl'],
           exe['tlsfresidual'], exe['tlsfcompose'], files(cases / 'disjoint_assumptions.tlsf')])
  if python3.found()
    foreach mode : ['lowercase', 'comment', 'signals']
      test('review4_' + mode, python3,
        args: [files('test_review4_exports.py'), exe['tlsf2ltl'],
               exe['tlsfresidual'], exe['tlsfcompose'], mode], timeout: 60)
    endforeach
    foreach mode : ['moore', 'finite', 'implicit', 'wrapper']
      test('compose_driver_' + mode, python3,
        args: [files('test_compose_driver_semantics.py'), exe['tlsfcompose'], mode], timeout: 60)
    endforeach
    test('decomposition_exactness_golden', python3,
      args: [files('test_decomposition_exactness.py'), exe['tlsf2ltl'],
             exe['tlsfresidual'], exe['tlsfcompose'], phase_b_probe, cases],
      depends: [native_reduction_exe, exe['tlsfsolve']], timeout: 60)
    test('oxidd_semantic_oracle', python3,
      args: [files('check_oxidd_oracle.py'), exe['tlsfsolve']], timeout: 120)
    test('native_oracle_8b158d7', python3,
      args: [files('native_oracle.py'), meson.project_build_root(), oxidd_build[0]],
      depends: [oxidd_build, exe['tlsf2tlsf'], exe['tlsfsolve'],
                exe['tlsfcertcheck'], native_api_c_exe],
      timeout: 900, is_parallel: false)
    test('gr1_explicit_differential', python3,
      args: [files('test_gr1_differential.py'),
             '--solver', exe['tlsfsolve'], '--games', '320'],
      timeout: 120,
    )
    test('gr1_certificate', python3,
      args: [files('test_gr1_certificate.py'),
             '--solver', exe['tlsfsolve'], '--one-step-helper', gr1_one_step, '--games', '240'],
      timeout: 180,
    )
    test('gr1_certcheck', python3,
      args: [files('test_gr1_certcheck.py'),
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck'],
             # Fixed seed: fairness at 2, rank/inv at 5, rare mutation at 15.
             '--games', '16'],
      timeout: 180,
    )
    test('gr1_check_order', python3,
      args: [files('test_gr1_check_order.py'),
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck']],
      timeout: 120,
    )
    test('gr1_region', python3,
      args: [files('test_gr1_region.py'),
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck'],
             '--games', '32'],
      timeout: 180,
    )
    test('gr1_unreal_certificate', python3,
      args: [files('test_gr1_unreal_certificate.py'),
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck'],
             # Fixed seed: dual rank at 0, losing counter-strategy at 1.
             '--games', '16'],
      timeout: 180,
    )
    test('gr1_environment_replay', python3,
      args: [files('test_gr1_environment_replay.py'),
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck']],
      timeout: 180,
    )
    test('gr1_environment_provenance', python3,
      args: [files('test_gr1_environment_provenance.py'),
             '--reduction', gr1_environment_reduce_exe,
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck']],
      timeout: 180,
    )
  endif
  test('gr1_monitor_game', python3,
    args: [files('test_gr1_monitor_game.py'), '--builddir', meson.project_build_root()],
    depends: [native_reduction_exe, exe['tlsf2ltl'], exe['tlsfsolve'], exe['tlsfcertcheck']],
    timeout: 600, is_parallel: false)
endif
