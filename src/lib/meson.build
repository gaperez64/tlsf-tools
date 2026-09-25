# libtlsf and its private headers. The OxiDD solvers and the GR(1) checker
# form a second archive, tlsf-oxidd: the OxiDD tools link it, and under
# -Dnative_gr1=enabled it is folded into libtlsf, whose GR(1) API needs it.

flex_out = custom_target(
  'tlsf_lex',
  input: 'tlsf.l',
  output: ['tlsf_lex.c', 'tlsf_lex.h'],
  command: [flex, '--header-file=@OUTPUT1@', '--outfile=@OUTPUT0@', '@INPUT@'],
)
bison_out = custom_target(
  'tlsf_parse',
  input: 'tlsf.y',
  output: ['tlsf_parse.c', 'tlsf_parse.h'],
  command: [bison, '--defines=@OUTPUT1@', '--output=@OUTPUT0@',
            '--warnings=all', '@INPUT@'],
)

build_info_conf = configuration_data()
build_info_conf.set('TLSF_BUILD_OXIDD', have_oxidd ? 1 : 0)
build_info_conf.set_quoted('TLSF_BUILD_OXIDD_PATCH', oxidd_patch_record)
build_info_conf.set('TLSF_BUILD_RESEARCH', research_tools ? 1 : 0)
configure_file(output: 'build_config.h', configuration: build_info_conf)

# Private headers, and the parser and build_config.h generated beside them.
lib_inc = include_directories('.')

lib_sources = files(
  'aiger.c',
  'apset.c',
  'arena.c',
  'ast.c',
  'ast_api.c',
  'classify.c',
  'cover.c',
  'decompose.c',
  'diagnostic.c',
  'expand.c',
  'gr.c',
  'intern.c',
  'liveness_class.c',
  'nnf.c',
  'normalize.c',
  'obligation_census.c',
  'pipeline.c',
  'pipeline_source.c',
  'print_ltlxba.c',
  'print_tlsf.c',
  'provenance.c',
  'recognize.c',
  'residual.c',
  'residual_plan.c',
  'rewrite.c',
  'section_pattern.c',
  'sha256.c',
  'spec.c',
  'spec_parse.c',
  'templates.c',
  'templates_certify.c',
) + [
  flex_out[0],
  bison_out[0],
  bison_out[1], # tlsf_parse.h: compile the lexer only after it exists.
]
lib_c_args = []
lib_compile_deps = [yyjson_dep]
lib_deps = [yyjson_dep]
pkg_private_libs = []
oxidd_link_whole = []

if have_oxidd
  # The decompose API's boolean-fragment pre-check.
  lib_sources += files('precheck_unreal.c')
  lib_c_args += ['-DHAVE_OXIDD']
  lib_compile_deps += [oxidd_dep.partial_dependency(includes: true)]
  lib_deps += [oxidd_dep]
  pkg_private_libs += ['-loxidd_ffi_c', '-lpthread', '-lm']

  tlsf_oxidd_lib = static_library(
    'tlsf-oxidd',
    files(
      'gr1_check.c',
      'gr1_oxidd.c',
      'gr1_service.c',
      'oxidd_common.c',
      'oxidd_host.c',
      'oxidd_order.c',
      'safety_oxidd.c',
    ),
    include_directories: [public_inc, lib_inc],
    dependencies: lib_compile_deps,
    pic: true,
  )
  if native_gr1
    oxidd_link_whole = [tlsf_oxidd_lib]
  endif
endif

if native_gr1
  lib_sources += files('gr1_lift.cc', 'gr1_reduction.cc')
  cpp_runtime = host_machine.system() == 'darwin' ? 'c++' : 'stdc++'
  lib_compile_deps += [spot_dep.partial_dependency(compile_args: true,
                                                   includes: true)]
  lib_deps += [spot_dep,
               meson.get_compiler('cpp').find_library(cpp_runtime)]
  pkg_private_libs += ['-l' + cpp_runtime]
endif
if have_oxidd and host_machine.system() != 'darwin'
  pkg_private_libs += ['-ldl']
endif

tlsf_lib = static_library(
  'tlsf',
  lib_sources,
  include_directories: [public_inc, lib_inc],
  c_args: lib_c_args,
  dependencies: lib_compile_deps,
  link_whole: oxidd_link_whole,
  install: true,
  pic: true,
)

# What consumers see: the public headers only.
tlsf_dep = declare_dependency(
  include_directories: public_inc,
  link_with: tlsf_lib,
  dependencies: lib_deps,
  sources: version_h,
)
meson.override_dependency('tlsf', tlsf_dep)

# What the tools and unit tests see: the private headers as well.
tlsf_internal_dep = declare_dependency(
  include_directories: lib_inc,
  dependencies: tlsf_dep,
)

# The OxiDD solvers and checker, linked ahead of libtlsf, which they call.
if have_oxidd
  tlsf_oxidd_dep = declare_dependency(
    link_with: native_gr1 ? [] : tlsf_oxidd_lib,
    dependencies: tlsf_internal_dep,
  )
endif

# The fault-injection build of the lifting code; it must never reach the
# installed library, so only test/unit compiles it (a second time).
gr1_lift_source = files('gr1_lift.cc')

pkg.generate(
  libraries: ['-L${libdir}', '-ltlsf'],
  name: 'tlsf',
  filebase: 'tlsf',
  description: 'TLSF decomposition and preprocessing library',
  version: meson.project_version(),
  libraries_private: pkg_private_libs,
  requires_private: ['yyjson'] + (native_gr1 ? ['libspot'] : []),
)
