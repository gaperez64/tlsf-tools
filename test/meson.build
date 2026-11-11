# unit/    programs that exercise internal units (private headers allowed)
# api/     programs that use only the installed headers
# cli/     checks of the command-line tools against golden outputs
# oracle/  Python oracles and differentials
# fixtures/ fake solvers, stubs and the case corpus

cases = meson.current_source_dir() / 'fixtures' / 'cases'
scripts = meson.project_source_root() / 'scripts'

# Default-behaviour checks must ignore developer solver overrides. Solver
# configuration tests supply their own subprocess environment explicitly.
test_env = environment()
test_env.unset('TLSFCOMPOSE_SOLVER')
add_test_setup('default', env: test_env, is_default: true)

subdir('fixtures')
subdir('unit')
if research_tools
  subdir('symmetry')
endif
subdir('fuzz')
subdir('api')
subdir('cli')
if research_tools
  gr1_one_step = executable('gr1_one_step', 'gr1_one_step.c', dependencies: oxidd_dep)
endif
subdir('oracle')

if python3.found()
  test('oxidd_build_stamp', python3,
    args: [files('api/test_oxidd_stamp.py'), oxidd_stamp_py, oxidd_dir,
           meson.project_build_root()],
    timeout: 90, is_parallel: false)
endif
