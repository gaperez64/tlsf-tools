# unit/    programs that exercise internal units (private headers allowed)
# api/     programs that use only the installed headers
# cli/     checks of the command-line tools against golden outputs
# oracle/  Python oracles and differentials
# fixtures/ fake solvers, stubs and the case corpus

cases = meson.current_source_dir() / 'fixtures' / 'cases'
scripts = meson.project_source_root() / 'scripts'

subdir('fixtures')
subdir('unit')
subdir('api')
subdir('cli')
subdir('oracle')

if have_oxidd and python3.found()
  test('oxidd_build_stamp', python3,
    args: [files('api/test_oxidd_stamp.py'), oxidd_stamp_py, oxidd_dir,
           meson.project_build_root()],
    timeout: 90, is_parallel: false)
endif
