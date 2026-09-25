# The public API. Every header in this directory is installed; the GR(1)
# headers only when libtlsf carries that API (-Dnative_gr1=enabled).

version_h = vcs_tag(
  command: [git_version, '--dirty'],
  input: 'version.h.in',
  output: 'version.h',
  fallback: meson.project_version(),
  replace_string: '@VCS_TAG@',
  install: true,
  install_dir: get_option('includedir') / 'tlsf',
)

public_headers = files(
  'aiger.h',
  'apset.h',
  'arena.h',
  'ast.h',
  'ast_api.h',
  'ast_api.hpp',
  'cover.h',
  'decompose.h',
  'decompose.hpp',
  'expand.h',
  'intern.h',
  'normalize.h',
  'pipeline.h',
  'print_tlsf.h',
  'spec.h',
  'templates.h',
)
gr1_headers = files(
  'gr1_check.h',
  'gr1_lift.h',
  'gr1_oxidd.h',
  'gr1_reduction.h',
  'oxidd_options.h',
  'safety_oxidd.h',
)
install_headers(public_headers + (native_gr1 ? gr1_headers : []),
                subdir: 'tlsf')
