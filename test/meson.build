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
