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

if native_gr1
  if get_option('native_lift_oracle_root') != '' and spot_python_found
    lift_diff_args = [files('test_native_lift_differential.py'),
                      '--native', native_lift_exe,
                      '--builddir', meson.project_build_root(),
                      '--oracle-root', get_option('native_lift_oracle_root'),
                      '--tools-build', meson.project_build_root()]
    if get_option('native_lift_corpus_root') != ''
      lift_diff_args += ['--corpus-root', get_option('native_lift_corpus_root'),
                         '--corpus-limit', '8', '--seconds', '12']
    endif
    test('native_lift_differential', spot_python,
         args: lift_diff_args, env: spot_python_env,
         timeout: get_option('native_lift_corpus_root') != '' ? 180 : 90,
         is_parallel: false)
  endif
  if spot_python_found
    native_diff_args = [files('test_native_reduction.py'),
                        '--native', native_reduction_exe,
                        '--builder', files(scripts / 'gr1_monitor_game.py'),
                        '--tlsf2ltl', exe['tlsf2ltl'],
                        '--tlsf2tlsf', exe['tlsf2tlsf'],
                        '--tlsfinfo', exe['tlsfinfo'],
                        '--fixtures', cases,
                        '--builddir', meson.project_build_root()]
    if get_option('native_reduction_corpus') != ''
      native_diff_args += ['--corpus', get_option('native_reduction_corpus')]
    endif
    test('native_reduction_differential', spot_python,
         args: native_diff_args, env: spot_python_env, timeout: 1800)
    test('native_reduction_language', spot_python,
         args: [files('test_native_reduction_language.py'),
                '--native', native_reduction_exe,
                '--tlsf2ltl', exe['tlsf2ltl'],
                '--builddir', meson.project_build_root()],
         env: spot_python_env, timeout: 120)
  endif
endif

if research_tools and have_oxidd
  if python3.found()
    test('oxidd_semantic_oracle', python3,
      args: [files('check_oxidd_oracle.py'), exe['tlsfsolve']], timeout: 120)
    if native_gr1
      test('native_oracle_8b158d7', python3,
        args: [files('native_oracle.py'), meson.project_build_root()],
        timeout: 900, is_parallel: false)
    endif
    test('gr1_explicit_differential', python3,
      args: [files('test_gr1_differential.py'),
             '--solver', exe['tlsfsolve'], '--games', '320'],
      timeout: 120,
    )
    test('gr1_certificate', python3,
      args: [files('test_gr1_certificate.py'),
             '--solver', exe['tlsfsolve'], '--games', '240'],
      timeout: 180,
    )
    test('gr1_certcheck', python3,
      args: [files('test_gr1_certcheck.py'),
             '--solver', exe['tlsfsolve'], '--checker', exe['tlsfcertcheck'],
             '--games', '80'],
      timeout: 180,
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
             '--games', '120'],
      timeout: 180,
    )
  endif
  if spot_python_found
    test('gr1_monitor_game', spot_python,
      args: [files('test_gr1_monitor_game.py'),
             '--python', spot_python,
             '--builder', files(scripts / 'gr1_monitor_game.py'),
             '--verifier', files(scripts / 'verify_strategy_explicit.py'),
             '--old-verifier', files(scripts / 'verify_aiger_ltl.py'),
             '--tlsf2ltl', exe['tlsf2ltl'],
             '--tlsf2tlsf', exe['tlsf2tlsf'],
             '--tlsfinfo', exe['tlsfinfo'],
             '--solver', exe['tlsfsolve'],
             '--checker', exe['tlsfcertcheck']],
      env: spot_python_env,
      timeout: 120,
    )
  endif
endif
