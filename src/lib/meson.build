# libtlsf includes TLSF conversion, OxiDD and the native GR(1) API.

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
  'conversion.c',
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
  'process.c',
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
  flex_out[1], # tlsf_lex.h: spec_parse.c includes it.
  bison_out[0],
  bison_out[1], # tlsf_parse.h: compile the lexer only after it exists.
]
lib_sources += files(
  'precheck_unreal.c', 'oxidd_runtime.c', 'gr1_check.c', 'gr1_oxidd.c',
  'gr1_service.c', 'oxidd_common.c', 'oxidd_host.c', 'oxidd_order.c',
  'safety_oxidd.c', 'gr1_lift.cc', 'gr1_env_lift.cc', 'gr1_reduction.cc',
)
cpp_compiler = meson.get_compiler('cpp')
cpp_runtime = 'stdc++'
if host_machine.system() == 'darwin' and cpp_compiler.get_id() != 'gcc'
  cpp_runtime = 'c++'
endif
lib_compile_deps = [yyjson_dep, oxidd_dep.partial_dependency(includes: true,
                                                          sources: true),
                   spot_dep.partial_dependency(compile_args: true, includes: true)]
# An explicit dynamic -lstdc++ would override the wheel's static-runtime flag.
cpp_runtime_static = cpp_runtime == 'stdc++' and \
  get_option('cpp_link_args').contains('-static-libstdc++')
cpp_runtime_dep = cpp_compiler.find_library(cpp_runtime, static: cpp_runtime_static)
lib_deps = [yyjson_dep, oxidd_dep, spot_dep, cpp_runtime_dep]
pkg_private_libs = ['-loxidd_ffi_c', '-lpthread', '-lm', '-l' + cpp_runtime]
if host_machine.system() != 'darwin'
  pkg_private_libs += ['-ldl']
endif

tlsf_lib = static_library(
  'tlsf',
  lib_sources,
  include_directories: [public_inc, lib_inc],
  dependencies: lib_compile_deps,
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

tlsf_oxidd_dep = tlsf_internal_dep

# The fault-injection build of the lifting code; it must never reach the
# installed library, so only test/unit compiles it (a second time).
gr1_lift_source = files('gr1_lift.cc')
gr1_env_lift_source = files('gr1_env_lift.cc')
gr1_reduction_source = files('gr1_reduction.cc')
reduction_contract_hooks = files('../../test/unit/reduction_contract_hooks.cc')

pkg.generate(
  libraries: ['-L${libdir}', '-ltlsf'],
  name: 'tlsf',
  filebase: 'tlsf',
  description: 'TLSF decomposition and preprocessing library',
  version: meson.project_version(),
  libraries_private: pkg_private_libs,
  requires_private: ['yyjson', 'libspot'],
)
