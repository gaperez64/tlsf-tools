project(
  'tlsf-tools',
  'c',
  'cpp',
  version: '0.1.0',
  license: 'MIT',
  default_options: [
    'warning_level=3',
    'werror=false',
    'b_ndebug=if-release',
    'cpp_std=c++17',
  ],
)

fs = import('fs')
pkg = import('pkgconfig')

# ---------------------------------------------------------------------------
# Compiler: force C23 via -std=c23 (meson's c_std enum doesn't map 'c23'
# until meson 1.3+, but clang 16+ and gcc 14+ accept it directly).
# ---------------------------------------------------------------------------

cc = meson.get_compiler('c')
research_tools = get_option('research_tools')

c23_flag = cc.get_supported_arguments(['-std=c23', '-std=c2x'])
add_project_arguments(c23_flag, language: 'c')
# Apple clang 15 accepts -std=c2x but lacks the C23 nullptr keyword.
has_c23_nullptr = cc.compiles(
  'int main(void) { void *p = nullptr; return p == nullptr; }',
  args: c23_flag,
  name: 'C23 nullptr',
)
if not has_c23_nullptr
  if not cc.compiles(
    'int main(void) { void *p = nullptr; return p == nullptr; }',
    args: c23_flag + ['-Dnullptr=0'],
    name: 'C23 nullptr compatibility define',
  )
    error('compiler does not support C23 nullptr or the compatibility define')
  endif
  add_project_arguments('-Dnullptr=0', language: 'c')
endif

extra_cflags = cc.get_supported_arguments([
  '-Wstrict-prototypes',
  '-Wmissing-prototypes',
  '-Wshadow',
  '-Wconversion',
  '-Wno-unused-parameter',      # generated bison/flex code trips this
  '-fstrict-aliasing',
  '-fstack-protector-strong',
])
add_project_arguments(extra_cflags, language: 'c')

# ---------------------------------------------------------------------------
# Target CPU / SIMD (opt-in via -Dcpu=...).  These -m flags both enable the
# matching compile-time path in include/tlsf/simd.h (via the predefined
# __AVX2__ / __AVX512F__ / __ARM_NEON macros) and let the compiler
# auto-vectorize the rest of the tree.  Filtered through get_supported_arguments
# so an ISA flag the host compiler/arch doesn't accept degrades to the scalar
# fallback instead of failing the build.
# ---------------------------------------------------------------------------

cpu = get_option('cpu')
cpu_flags = []
if cpu == 'x86-64-v2'
  cpu_flags = ['-march=x86-64-v2', '-mtune=generic']
elif cpu == 'avx2'
  cpu_flags = ['-mavx2', '-mfma']
elif cpu == 'avx512'
  cpu_flags = ['-mavx512f', '-mavx512bw', '-mavx512vpopcntdq']
elif cpu == 'neon'
  if host_machine.system() == 'darwin'
    cpu_flags = []
  else
    cpu_flags = ['-march=armv8-a+simd']
  endif
elif cpu == 'native'
  cpu_flags = ['-march=native']
endif
if cpu_flags.length() > 0
  add_project_arguments(cc.get_supported_arguments(cpu_flags), language: 'c')
endif

# ---------------------------------------------------------------------------
# Sanitizer support (opt-in via -Dsanitize=address etc.)
# ---------------------------------------------------------------------------

sanitize = get_option('sanitize')
if sanitize != 'none'
  san_flags = ['-fsanitize=' + sanitize, '-fno-omit-frame-pointer']
  add_project_arguments(san_flags, language: 'c')
  add_project_link_arguments(san_flags, language: 'c')
endif

# ---------------------------------------------------------------------------
# Dependencies: flex and bison
# ---------------------------------------------------------------------------

flex  = find_program('flex',  required: true)
bison = find_program('bison', required: true)
# Optional: used by wrapper/benchmark tests that shell out to ltlsynt.
ltlsynt = find_program('ltlsynt', required: false)
git = find_program('git', required: false)
bash = find_program('bash', required: false)
python3 = find_program('python3', required: false)
spot_python_found = false
if python3.found()
  spot_python_found = run_command(
    python3,
    '-c',
    'import spot',
    check: false,
  ).returncode() == 0
endif

# ---------------------------------------------------------------------------
# Optional in-process safety + GR(1) solver backend: OxiDD (Rust + C FFI),
# vendored as a submodule and built before explicit OxiDD-enabled research
# configuration. The default production build is dependency-free.
# ---------------------------------------------------------------------------

oxidd_feature = get_option('oxidd')
oxidd_dir = join_paths(meson.project_source_root(), 'external', 'oxidd')
oxidd_build_sh = join_paths(meson.project_source_root(), 'scripts', 'build_oxidd.sh')
oxidd_lib_path = join_paths(oxidd_dir, 'target', 'release', 'liboxidd_ffi_c.a')
oxidd_inc_path = join_paths(oxidd_dir, 'build', 'include')
oxidd_capi_h = join_paths(oxidd_inc_path, 'oxidd', 'capi.h')
oxidd_submodule_ready = fs.exists(join_paths(oxidd_dir, 'crates', 'oxidd-ffi-c', 'Cargo.toml'))

if git.found()
  run_target(
    'oxidd-submodule',
    command: [
      git, 'submodule', 'update', '--init', '--recursive', 'external/oxidd',
    ],
  )
endif
if bash.found()
  run_target('oxidd-build', command: [bash, oxidd_build_sh])
endif

oxidd_ready = fs.exists(oxidd_lib_path) and fs.exists(oxidd_capi_h)
oxidd_dep = dependency('', required: false)  # null dependency by default
have_oxidd = false
if oxidd_feature.enabled() or (oxidd_feature.auto() and oxidd_ready)
  if not oxidd_ready
    error(
      'OxiDD artifacts are missing. Run:\n' +
      '  git submodule update --init --recursive\n' +
      '  scripts/build_oxidd.sh\n' +
      '  meson setup build-research -Dresearch_tools=true ' +
      '-Doxidd=enabled --buildtype=release',
    )
  endif
  # Rust staticlib pulls in the system threading/dl/math runtime.
  oxidd_link_args = [oxidd_lib_path, '-lpthread', '-lm']
  if host_machine.system() != 'darwin'
    oxidd_link_args += ['-ldl']
  endif
  oxidd_dep = declare_dependency(
    include_directories: include_directories('external/oxidd/build/include'),
    link_args: oxidd_link_args,
  )
  have_oxidd = true
  message('OxiDD safety solver enabled (' + oxidd_lib_path + ')')
elif oxidd_feature.auto()
  message('OxiDD safety solver disabled (artifacts absent; build with ' +
          '`meson compile -C build oxidd-build`)')
endif

build_info_conf = configuration_data()
build_info_conf.set_quoted('TLSF_PROJECT_VERSION', meson.project_version())
build_info_conf.set('TLSF_BUILD_OXIDD', have_oxidd ? 1 : 0)
build_info_conf.set('TLSF_BUILD_RESEARCH', research_tools ? 1 : 0)
configure_file(
  output: 'build_config.h',
  configuration: build_info_conf,
)

# ---------------------------------------------------------------------------
# Codegen: flex → tlsf_lex.c + tlsf_lex.h
# ---------------------------------------------------------------------------

flex_out = custom_target(
  'tlsf_lex',
  input:  'src/tlsf.l',
  output: ['tlsf_lex.c', 'tlsf_lex.h'],
  command: [
    flex,
    '--header-file=@OUTPUT1@',
    '--outfile=@OUTPUT0@',
    '@INPUT@',
  ],
  build_by_default: true,
)

# ---------------------------------------------------------------------------
# Codegen: bison → tlsf_parse.c + tlsf_parse.h
# ---------------------------------------------------------------------------

bison_out = custom_target(
  'tlsf_parse',
  input:  'src/tlsf.y',
  output: ['tlsf_parse.c', 'tlsf_parse.h'],
  command: [
    bison,
    '--defines=@OUTPUT1@',
    '--output=@OUTPUT0@',
    '--warnings=all',
    '@INPUT@',
  ],
  build_by_default: true,
)

# ---------------------------------------------------------------------------
# Include directories
# ---------------------------------------------------------------------------

inc = include_directories(
  'include',
  '.',            # so #include "tlsf_lex.h" / "tlsf_parse.h" resolve in builddir
)

# ---------------------------------------------------------------------------
# Shared static library
# ---------------------------------------------------------------------------

lib_sources = [
  'src/arena.c',
  'src/intern.c',
  'src/ast.c',
  'src/spec.c',
  'src/cli.c',
  'src/expand.c',
  'src/nnf.c',
  'src/rewrite.c',
  'src/normalize.c',
  'src/classify.c',
  'src/liveness_class.c',
  'src/apset.c',
  'src/cover.c',
  'src/recognize.c',
  'src/pipeline.c',
  'src/decompose.c',
  'src/templates.c',
  'src/templates_certify.c',
  'src/residual.c',
  'src/residual_plan.c',
  'src/aiger.c',
  'src/gr.c',
  'src/print_ltlxba.c',
  'src/print_tlsf.c',
  flex_out[0],
  bison_out[0],
  bison_out[1],   # tlsf_parse.h — declare as a source so the generated lexer
                  # (which #includes it) is compiled only after it exists.
]

if have_oxidd
  lib_sources += ['src/precheck_unreal.c']
endif

lib_c_args = have_oxidd ? ['-DHAVE_OXIDD'] : []
lib_deps = have_oxidd ? [oxidd_dep] : []
pkg_private_libs = have_oxidd ? oxidd_link_args : []

tlsf_lib = static_library(
  'tlsf',
  lib_sources,
  include_directories: inc,
  c_args: lib_c_args,
  dependencies: lib_deps,
  install: true,
  pic: false,
)

tlsf_dep = declare_dependency(
  include_directories: inc,
  link_with: tlsf_lib,
  dependencies: lib_deps,
)

install_headers(
  'include/tlsf/decompose.h',
  'include/tlsf/decompose.hpp',
  subdir: 'tlsf',
)

pkg.generate(
  tlsf_lib,
  name: 'tlsf',
  filebase: 'tlsf',
  description: 'TLSF decomposition and preprocessing library',
  libraries_private: pkg_private_libs,
)

# ---------------------------------------------------------------------------
# Executables
# ---------------------------------------------------------------------------

tlsf2ltl_exe = executable(
  'tlsf2ltl',
  sources: ['src/main_tlsf2ltl.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

tlsf2tlsf_exe = executable(
  'tlsf2tlsf',
  sources: ['src/main_tlsf2tlsf.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

tlsfinfo_exe = executable(
  'tlsfinfo',
  sources: ['src/main_tlsfinfo.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

tlsfnorm_exe = executable(
  'tlsfnorm',
  sources: ['src/main_tlsfnorm.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

if research_tools
  tlsftemplates_exe = executable(
    'tlsftemplates',
    sources: ['src/main_tlsftemplates.c', bison_out[1]],
    link_with: tlsf_lib,
    include_directories: inc,
    install: true,
  )

  tlsfbenchgraph_exe = executable(
    'tlsfbenchgraph',
    sources: ['src/main_tlsfbenchgraph.c', bison_out[1]],
    link_with: tlsf_lib,
    include_directories: inc,
    install: true,
  )

  tlsfresidual_exe = executable(
    'tlsfresidual',
    sources: ['src/main_tlsfresidual.c', bison_out[1]],
    link_with: tlsf_lib,
    include_directories: inc,
    install: true,
  )

  if have_oxidd
    tlsfcompose_exe = executable(
      'tlsfcompose',
      sources: ['src/main_tlsfcompose.c', 'src/compose_analysis.c',
                'src/compose_games.c', 'src/compose_oxidd.c',
                'src/compose_route.c', 'src/safety_oxidd.c',
                'src/gr1_oxidd.c', 'src/oxidd_common.c', bison_out[1]],
      c_args: ['-DHAVE_OXIDD'],
      dependencies: [oxidd_dep],
      link_with: tlsf_lib,
      include_directories: inc,
      install: true,
    )

    tlsfsolve_exe = executable(
      'tlsfsolve',
      sources: ['src/main_tlsfsolve.c', 'src/safety_oxidd.c',
                'src/gr1_oxidd.c', 'src/oxidd_common.c'],
      c_args: ['-DHAVE_OXIDD'],
      dependencies: [oxidd_dep],
      link_with: tlsf_lib,
      include_directories: inc,
      install: true,
    )
  endif
endif

simd_check_exe = executable(
  'simd_check',
  sources: ['test/simd_check.c'],
  include_directories: inc,
)
test('simd_kernels', simd_check_exe)

decompose_cpp_exe = executable(
  'decompose_cpp',
  sources: ['test/decompose_cpp.cpp'],
  include_directories: inc,
  link_with: tlsf_lib,
  dependencies: lib_deps,
)
test('decompose_cpp', decompose_cpp_exe)

# ---------------------------------------------------------------------------
# Integration / regression tests (golden-output diffs)
#
# Self-contained: a representative set of SYNTCOMP TLSF specs lives under
# test/cases/ with their expected tool output.  No external tools (syfco,
# spot) are needed, so these run anywhere — including CI.
# ---------------------------------------------------------------------------

check = files('test/check.sh')
xfail = files('test/expect_fail.sh')
check_fail_stderr = files('test/check_fail_stderr.sh')
check_solve_wrapper = files('test/check_solve_wrapper.sh')
check_output_dir = files('test/check_output_dir.sh')
check_output_dir_fail = files('test/check_output_dir_fail.sh')

# Cases converted with `tlsf2ltl` (default, minimal parentheses).
ltl_cases = [
  'Patterns_Uright_uright02',
  'Patterns_Uright_uright06',
  'Patterns_GFand_gfand01',
  'Patterns_GFand_gfand05',
  'Random_Lydia_case_03_50_05',
  'Two-player-Game_Nim_nim_02_System-first_nim_02_02',
]

foreach c : ltl_cases
  test('ltl_' + c, check,
    args: [
      files('test/cases/' + c + '.ltl'),
      tlsf2ltl_exe,
      files('test/cases/' + c + '.tlsf'),
    ])
endforeach

# Targeted feature tests.
test('ltl_full_parens', check,
  args: [files('test/cases/Patterns_Uright_uright06.full.ltl'),
         tlsf2ltl_exe, '--parenthesize',
         files('test/cases/Patterns_Uright_uright06.tlsf')])

# Output dialects (--format) and formula transformations.
test('ltl_format_ltl', check,
  args: [files('test/cases/operators.ltlfmt.ltl'),
         tlsf2ltl_exe, '--format', 'ltl',
         files('test/cases/operators.tlsf')])

test('ltl_format_latex', check,
  args: [files('test/cases/operators.latex.ltl'),
         tlsf2ltl_exe, '--format', 'latex',
         files('test/cases/operators.tlsf')])

test('ltl_strong_simplify', check,
  args: [files('test/cases/operators.s1.ltl'),
         tlsf2ltl_exe, '--strong-simplify',
         files('test/cases/operators.tlsf')])

test('ltl_no_derived', check,
  args: [files('test/cases/operators.nd.ltl'),
         tlsf2ltl_exe, '--no-derived',
         files('test/cases/operators.tlsf')])

test('ltl_no_release', check,
  args: [files('test/cases/operators.nr.ltl'),
         tlsf2ltl_exe, '--no-release',
         files('test/cases/operators.tlsf')])

test('ltl_no_strong_release', check,
  args: [files('test/cases/operators.nsr.ltl'),
         tlsf2ltl_exe, '--no-strong-release',
         files('test/cases/operators.tlsf')])

# Finite (ltlxba-fin): W/M auto-eliminated, weak X vs strong X[!] preserved.
test('ltl_finite_wm', check,
  args: [files('test/cases/finite_wm.ltl'),
         tlsf2ltl_exe, files('test/cases/finite_wm.tlsf')])

# Bounded temporal operators G[i:j] / F[i:j].
test('ltl_ranges', check,
  args: [files('test/cases/ranges.ltl'),
         tlsf2ltl_exe, files('test/cases/ranges.tlsf')])

test('tlsf_ranges_reemit', check,
  args: [files('test/cases/ranges.reemit.tlsf'),
         tlsf2tlsf_exe, files('test/cases/ranges.tlsf')])

# 'M' (strong-release keyword) reused as a parameter name and atom.
test('ltl_ident_m', check,
  args: [files('test/cases/ident_m.ltl'),
         tlsf2ltl_exe, files('test/cases/ident_m.tlsf')])

# enum definitions: typed-bus declaration, bus == LABEL bit match, and the
# implicit validity invariant.
test('ltl_enum', check,
  args: [files('test/cases/enum_demo.ltl'),
         tlsf2ltl_exe, files('test/cases/enum_demo.tlsf')])

check_wl = files('test/check_wl.sh')   # normalizes embedded paths to basenames
check_contains = files('test/check_contains.sh')  # asserts output matches a regex

test('tlsf_enum_basic', check,
  args: [files('test/cases/enum_demo.basic.tlsf'),
         tlsf2tlsf_exe, files('test/cases/enum_demo.tlsf')])

if research_tools
# tlsftemplates (M5): certify CSNF for template blocks + soundness declines.
test('tmpl_definition', check_wl,
  args: [files('test/cases/def_demo.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/def_demo.tlsf')])
test('tmpl_round_robin', check_wl,
  args: [files('test/cases/roundrobin2.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/roundrobin2.tlsf')])
test('tmpl_guarded_next', check_wl,
  args: [files('test/cases/gnext_one_sided.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/gnext_one_sided.tlsf')])
test('tmpl_set_reset', check_wl,
  args: [files('test/cases/gnext_demo.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/gnext_demo.tlsf')])
test('tmpl_set_reset_declined', check_wl,
  args: [files('test/cases/gnext_unsafe.csnf'), tlsftemplates_exe,
         '--certify', '--format', 'csnf',
         files('test/cases/gnext_unsafe.tlsf')])
test('tmpl_set_reset_strong_finite_declined', check_wl,
  args: [files('test/cases/gnext_strong_fin.csnf'), tlsftemplates_exe,
         '--certify', '--format', 'csnf',
         files('test/cases/gnext_strong_fin.tlsf')])
test('tmpl_toggle', check_wl,
  args: [files('test/cases/toggle_demo.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/toggle_demo.tlsf')])
test('tmpl_toggle_strong_finite_declined', check_wl,
  args: [files('test/cases/toggle_strong_fin.csnf'), tlsftemplates_exe,
         '--certify', '--format', 'csnf',
         files('test/cases/toggle_strong_fin.tlsf')])
test('tmpl_fixed_delay', check_wl,
  args: [files('test/cases/fdelay_demo.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/fdelay_demo.tlsf')])
test('tmpl_fixed_delay_declined', check_wl,
  args: [files('test/cases/fdelay_blocked.csnf'), tlsftemplates_exe,
         '--certify', '--format', 'csnf',
         files('test/cases/fdelay_blocked.tlsf')])
test('tmpl_fixed_delay_strong_finite_declined', check_wl,
  args: [files('test/cases/fdelay_strong_fin.csnf'), tlsftemplates_exe,
         '--certify', '--format', 'csnf',
         files('test/cases/fdelay_strong_fin.tlsf')])
test('tmpl_delayed_def_strong_finite_declined', check_wl,
  args: [files('test/cases/ddef_strong_fin.csnf'), tlsftemplates_exe,
         '--certify', '--format', 'csnf',
         files('test/cases/ddef_strong_fin.tlsf')])
# Template-coverage expansion: free-liveness family, reaction, delayed-def,
# fair arbiter — each with a solved and a declined (non-free / non-exclusive) case.
foreach name : ['reach_free', 'reach_blocked', 'persist_free', 'reaction_ok',
                'reaction_multi', 'reaction_unsafe', 'ddef_demo',
                'response_free', 'response_blocked', 'inv_const',
                'inv_skolem', 'inv_multi', 'inv_decline', 'inv_valid',
                'dbuchi_switch', 'dbuchi_switch_finite']
  test('tmpl_' + name, check_wl,
    args: [files('test/cases/' + name + '.csnf'), tlsftemplates_exe,
           '--certify', '--solve', '--format', 'csnf',
           files('test/cases/' + name + '.tlsf')])
endforeach
test('tmpl_arbiter', check_wl,
  args: [files('test/cases/arbiter2.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/arbiter2.tlsf')])
# CLI option coverage: --list-templates, --version, --template/--templates
# filter, --param.  These reuse existing goldens where possible.
test('tmpl_list_templates', check,
  args: [files('test/cases/tmpl_list_templates.txt'), tlsftemplates_exe,
         '--list-templates'])
test('tmpl_version', check,
  args: [files('test/cases/tmpl_version.txt'), tlsftemplates_exe, '--version'])
test('tmpl_template_filter', check_wl,
  args: [files('test/cases/reaction_ok.csnf'), tlsftemplates_exe,
         '--template', 'reaction', '--certify', '--solve', '--format', 'csnf',
         files('test/cases/reaction_ok.tlsf')])
test('tmpl_templates_filter', check_wl,
  args: [files('test/cases/reaction_ok.csnf'), tlsftemplates_exe,
         '--templates', 'reaction', '--certify', '--solve', '--format', 'csnf',
         files('test/cases/reaction_ok.tlsf')])
test('tmpl_param', check_wl,
  args: [files('test/cases/tmpl_param_demo.csnf'), tlsftemplates_exe,
         '--param', 'n=5', '--param', 'k=2',
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/param_demo.tlsf')])
# match-normalize (PR3/PR4): equivalence-preserving recognition normalization
# lifts a guarded-next to solved and a mutex to certified.
test('tmpl_match_normalize', check,
  args: [files('test/cases/normalization_patterns.tmpl_matchsafe.txt'),
         tlsftemplates_exe, '--certify', '--solve', '--format', 'text',
         '--match-normalize', 'match-safe:1',
         files('test/cases/normalization_patterns.tlsf')])
# Composition soundness: tlsftemplates --check (whole-spec verdict) and
# tlsfresidual (leftover LTL after the accepted blocks).
foreach name : ['reaction_ok', 'compose_conflict', 'compose_cycle',
                'compose_partial', 'subst_reduce', 'server_merge',
                'arbiter_nomutex']
  test('check_' + name, check_wl,
    args: [files('test/cases/' + name + '.check'), tlsftemplates_exe,
           '--check', '--format', 'csnf', files('test/cases/' + name + '.tlsf')])
endforeach
endif
if research_tools
foreach name : ['response_free', 'reach_blocked', 'compose_conflict',
                'compose_cycle', 'compose_partial', 'subst_reduce',
                'server_merge', 'arbiter_nomutex', 'cluster_split',
                'cluster_assume', 'inv_skolem', 'inv_multi', 'inv_decline']
  test('residual_' + name, check,
    args: [files('test/cases/' + name + '.residual'), tlsfresidual_exe,
           files('test/cases/' + name + '.tlsf')])
endforeach
test('residual_single', check,
  args: [files('test/cases/cluster_split.single'), tlsfresidual_exe,
         '--single', files('test/cases/cluster_split.tlsf')])
# CLI option coverage: --version, --format ltl/ltlxba, --split, --param.
test('residual_version', check,
  args: [files('test/cases/residual_version.txt'), tlsfresidual_exe, '--version'])
test('residual_ltl_format', check,
  args: [files('test/cases/residual_ltl_format.residual'), tlsfresidual_exe,
         '--format', 'ltl', files('test/cases/cluster_split.tlsf')])
test('residual_ltlxba_format', check,
  args: [files('test/cases/cluster_split.residual'), tlsfresidual_exe,
         '--format', 'ltlxba', files('test/cases/cluster_split.tlsf')])
test('residual_split', check,
  args: [files('test/cases/cluster_split.residual'), tlsfresidual_exe,
         '--split', files('test/cases/cluster_split.tlsf')])
test('residual_lowercase', check,
  args: [files('test/cases/upper_atoms.lower.residual'), tlsfresidual_exe,
         '--split', '--lowercase', files('test/cases/upper_atoms.tlsf')])
test('residual_param', check,
  args: [files('test/cases/residual_param_demo.residual'), tlsfresidual_exe,
         '--param', 'n=5', '--param', 'k=2',
         files('test/cases/param_demo.tlsf')])
if have_oxidd
  foreach name : ['compose_demo', 'cluster_split', 'cluster_prune', 'input_gua_skip']
    test('compose_' + name, check,
      args: [files('test/cases/' + name + '.compose'), tlsfcompose_exe,
             files('test/cases/' + name + '.tlsf')])
  endforeach
  test('compose_lowercase', check,
    args: [files('test/cases/upper_atoms.lower.compose'), tlsfcompose_exe,
           '--split', '--lowercase', files('test/cases/upper_atoms.tlsf')])
  test('compose_merge_mode', check,
    args: [files('test/cases/compose_demo.merged.aag'), tlsfcompose_exe,
           '--merge', files('test/cases/compose_demo.merged.aag')])
  test('solve_wrapper_oxidd_presolve', check_solve_wrapper,
    args: [files('test/cases/solve_wrapper_fake.aag'),
           files('scripts/solve.sh'), tlsfcompose_exe,
           files('test/fake_ltlsynt.sh'),
           files('test/cases/compose_demo.tlsf')])
  test('solve_wrapper_fake_ltlsynt', check_solve_wrapper,
    args: [files('test/cases/solve_wrapper_fake_liveness.aag'),
           files('scripts/solve.sh'), tlsfcompose_exe,
           files('test/fake_ltlsynt.sh'),
           files('test/cases/liveness_nested.tlsf')])
  test('compose_output_dir_under_real_wr', check_output_dir,
    args: [files('test/cases/wr_under_real.output_dir'),
           tlsfcompose_exe, '--split', files('test/cases/wr_under_real.tlsf')])
  test('compose_output_dir_over_unreal_wr', check_output_dir_fail,
    args: ['trusted one-sided OxiDD verdict', tlsfcompose_exe, '--split',
           files('test/cases/wr_gated_collapse.tlsf')])
  test('compose_aiger_unclassified_atom', check,
    args: [files('test/cases/aiger_unclassified_atom.compose'), tlsfcompose_exe,
           files('test/cases/aiger_unclassified_atom.tlsf')])
  test('compose_route_stats_gr1', check,
    args: [files('test/cases/gr1_spec.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', files('test/cases/gr1_spec.tlsf')])
  test('compose_route_stats_bounded', check,
    args: [files('test/cases/compose_demo.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', '--experimental-bounded', '4',
           files('test/cases/compose_demo.tlsf')])
  test('compose_route_stats_response_monitor', check,
    args: [files('test/cases/compose_demo.response_monitor.route_stats'),
           tlsfcompose_exe, '--split', '--route-stats',
           files('test/cases/compose_demo.tlsf')])
  test('compose_route_stats_initial_x_assume', check,
    args: [files('test/cases/initial_x_assume.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', files('test/cases/initial_x_assume.tlsf')])
  test('compose_route_stats_delayed_global', check,
    args: [files('test/cases/delayed_global.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', files('test/cases/delayed_global.tlsf')])
  test('compose_route_stats_gr1_recurrence', check,
    args: [files('test/cases/gr1_recurrence.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', files('test/cases/gr1_recurrence.tlsf')])
  test('compose_route_stats_wr_response', check,
    args: [files('test/cases/wr_response.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', files('test/cases/wr_response.tlsf')])
  test('compose_route_stats_reaction_ok', check,
    args: [files('test/cases/reaction_ok.route_stats'), tlsfcompose_exe,
           '--split', '--route-stats', files('test/cases/reaction_ok.tlsf')])
  test('compose_route_stats_response_same_cycle', check,
    args: [files('test/cases/response_same_cycle.route_stats'),
           tlsfcompose_exe, '--split', '--route-stats',
           files('test/cases/response_same_cycle.tlsf')])
  test('compose_route_stats_eventual_output', check,
    args: [files('test/cases/eventual_output.route_stats'),
           tlsfcompose_exe, '--split', '--route-stats',
           files('test/cases/eventual_output.tlsf')])
  test('compose_route_stats_until_input_target', check,
    args: [files('test/cases/until_input_target.route_stats'),
           tlsfcompose_exe, '--split', '--route-stats',
           files('test/cases/until_input_target.tlsf')])
  test('compose_route_stats_policy_off', check,
    args: [files('test/cases/gr1_spec.policy_off.route_stats'),
           tlsfcompose_exe, '--split', '--route-stats',
           '--preprocess-policy', 'off', files('test/cases/gr1_spec.tlsf')])
  test('compose_route_stats_policy_profitable_skip', check,
    args: [files('test/cases/policy_profitable_skip.route_stats'),
           tlsfcompose_exe, '--split', '--route-stats',
           '--preprocess-policy', 'profitable',
           files('test/cases/policy_profitable_skip.tlsf')])
  foreach name : ['liveness_eventual', 'liveness_until', 'liveness_mixed',
                  'liveness_nested']
    test('compose_route_stats_' + name, check,
      args: [files('test/cases/' + name + '.route_stats'), tlsfcompose_exe,
             '--split', '--route-stats',
             files('test/cases/' + name + '.tlsf')])
  endforeach
  # TRUST_OVER boolean-fragment UNREAL pre-check: an input-only G guarantee is
  # caught before plan emission.
  test('precheck_input_only_unreal', check_contains,
    args: ['UNREALIZABLE \\(boolean-fragment pre-check', tlsfcompose_exe,
           files('test/cases/precheck_input_only.tlsf')])
  test('precheck_route_stats', check_contains,
    args: ['unreal_precheck=1', tlsfcompose_exe, '--split', '--route-stats',
           files('test/cases/precheck_input_only.tlsf')])
  # Control: the boolean-G guarantee mentions an output that can satisfy it, so
  # the pre-check stays silent and normal plan emission succeeds.
  test('precheck_outputs_rescue_real', tlsfcompose_exe,
    args: [files('test/cases/precheck_outputs_rescue.tlsf')])
  # Dual TRUST_UNDER early-REAL via the --realizability oracle (self-contained,
  # no solver): outputs satisfy the boolean guarantees -> REALIZABLE; an
  # input-only contradiction -> UNREALIZABLE (always-on UNREAL check); a
  # temporal guarantee -> UNKNOWN (oracle inconclusive).
  test('precheck_real_oracle_real', check_contains,
    args: ['REALIZABLE \\(boolean-fragment pre-check', tlsfcompose_exe,
           '--split', '--realizability',
           files('test/cases/precheck_outputs_rescue.tlsf')])
  test('precheck_real_oracle_unreal', check_contains,
    args: ['UNREALIZABLE \\(boolean-fragment pre-check', tlsfcompose_exe,
           '--split', '--realizability',
           files('test/cases/precheck_input_only.tlsf')])
  test('precheck_real_oracle_unknown', check_contains,
    args: ['realizability UNKNOWN', tlsfcompose_exe,
           '--split', '--realizability',
           files('test/cases/precheck_real_unknown.tlsf')])
endif
endif
if research_tools
# tlsfbenchgraph: per-spec corpus metrics TSV (file column is a basename, so the
# golden is path-independent).
test('benchgraph_tsv', check,
  args: [files('test/cases/bench.tsv'), tlsfbenchgraph_exe,
         '--summary', files('test/cases/arbiter1formula.tlsf'),
         files('test/cases/arbiter2.tlsf'),
         files('test/cases/cluster_split.tlsf'),
         files('test/cases/def_demo.tlsf'),
         files('test/cases/roundrobin2.tlsf')])
if python3.found()
  test('bounded_corpus_harness', check,
    args: [files('test/cases/bounded_corpus.tsv'),
           files('scripts/bounded_corpus.py'), '--benchgraph', tlsfbenchgraph_exe,
           '--mem-mb', '512', '--timeout', '5', '--quiet',
           files('test/cases/def_demo.tlsf'),
           files('test/cases/reaction_ok.tlsf')])
  # norm_sweep (PR11): match-safe:1 is soundness-eligible and lifts a block to
  # solved on the crafted pattern spec.
  test('norm_sweep_match_safe', check_contains,
    args: ['match-safe:1[[:space:]]+1[[:space:]]+0[[:space:]]+2[[:space:]]+1[[:space:]]+1',
           files('scripts/norm_sweep.py'),
           '--tlsfbenchgraph', tlsfbenchgraph_exe,
           files('test/cases/normalization_patterns.tlsf'),
           '--schedules', 'off', 'match-safe:1'])
endif
endif
if research_tools and python3.found() and spot_python_found
  tlsf2ltl_path = join_paths(meson.current_build_dir(), 'tlsf2ltl')
  if have_oxidd
    # tlsfsolve: standalone AIGER game solver.
    test('tlsfsolve_real', check,
      args: [files('test/cases/solve_real.out.aag'),
             tlsfsolve_exe, files('test/cases/solve_real.aag')])
    test('tlsfsolve_unreal', xfail,
      args: [tlsfsolve_exe, files('test/cases/solve_unreal.aag')])
  endif
endif

# tlsfnorm is stable preprocessing functionality.
test('norm_split', check,
  args: [files('test/cases/arbiter1formula.norm.tlsf'),
         tlsfnorm_exe, '--passes', 'split',
         files('test/cases/arbiter1formula.tlsf')])
test('norm_nnf_boolean', check,
  args: [files('test/cases/arbiter1formula.nnfbool.tlsf'),
         tlsfnorm_exe, '--passes', 'nnf,boolean',
         files('test/cases/arbiter1formula.tlsf')])
test('norm_trace', check,
  args: [files('test/cases/arbiter1formula.trace.txt'),
         tlsfnorm_exe, '--passes', 'split', '--format', 'trace',
         files('test/cases/arbiter1formula.tlsf')])
test('norm_param', check,
  args: [files('test/cases/mutual_exclusion.norm3.tlsf'),
         tlsfnorm_exe, '--passes', 'split', '--param', 'n=3',
         files('test/cases/mutual_exclusion.tlsf')])
# Normalization API (PR2): bool-canon sorts/dedups boolean operands; the
# match-safe profile re-emits valid, equivalent TLSF.
test('norm_match_safe', check,
  args: [files('test/cases/normalization_match.matchsafe.tlsf'),
         tlsfnorm_exe, '--passes', 'match-safe:1',
         files('test/cases/normalization_match.tlsf')])
# match-safe pattern rules (PR6): or-to-impl exposes guarded-next, mutex-demorgan
# exposes mutex, equiv-output-side canonicalises the definition orientation.
test('norm_match_patterns', check,
  args: [files('test/cases/normalization_patterns.matchsafe.tlsf'),
         tlsfnorm_exe, '--passes', 'match-safe:1',
         files('test/cases/normalization_patterns.tlsf')])
# route-safe (PR7): NNF + push G/X inward exposes independent safety invariants.
test('norm_route_safe', check,
  args: [files('test/cases/normalization_route.routesafe.tlsf'),
         tlsfnorm_exe, '--passes', 'route-safe:1',
         files('test/cases/normalization_route.tlsf')])
# Sickert Stage 2 (PR9): lift a GF/FG limit node out of its temporal context.
test('norm_sickert2', check,
  args: [files('test/cases/normalization_sickert2.s2.tlsf'),
         tlsfnorm_exe, '--passes', 'sickert-stage2:2', '--norm-max-growth',
         '400', files('test/cases/normalization_sickert2.tlsf')])
# Sickert Stage 3 (PR10): W inside GF -> U inside GF (+ FG-tail disjunct).
test('norm_sickert3', check,
  args: [files('test/cases/normalization_sickert3.s3.tlsf'),
         tlsfnorm_exe, '--passes', 'sickert-stage3:1', '--norm-max-growth',
         '800', files('test/cases/normalization_sickert3.tlsf')])
# Soundness gate (Spot-verified; auto-skips when ltlfilt is absent, e.g. in CI):
# each schedule must preserve the spec's LTL meaning.
check_norm_equiv = files('scripts/check_norm_equiv.sh')
# (check_contains is defined near the top of the test section)
foreach case : [
    ['match-safe:1', 'normalization_patterns.tlsf'],
    ['route-safe:1', 'normalization_route.tlsf'],
    ['sickert-stage2:2', 'normalization_sickert2.tlsf'],
    ['sickert-stage3:1', 'normalization_sickert3.tlsf'],
    ['sickert-bounded', 'normalization_sickert3.tlsf'],
  ]
  test('norm_equiv_' + case[0].underscorify() + '_' + case[1].underscorify(),
    check_norm_equiv,
    args: [tlsfnorm_exe, tlsf2ltl_exe, case[0],
           files('test/cases/' + case[1])])
endforeach
# Sickert passes are infinite-word-only: they must be rejected on Finite specs.
test('norm_finite_rejects_sickert', xfail,
  args: [tlsfnorm_exe, '--passes', 'sickert-stage2:1',
         files('test/cases/Patterns_Uright_uright06.tlsf')])
# Pre-expansion passes (PR5).  The expanded output is unchanged (expand() also
# performs these simplifications); the value is the recorded pre-pass firing,
# so these assert the stats line rather than a byte-identical re-emission.
test('norm_pre_indexed_x', check_contains,
  args: ['pre-xn-flatten: fired=[1-9]', tlsfnorm_exe, '--pre-passes',
         'pre-indexed-x', '--norm-stats',
         files('test/cases/normalization_xn.tlsf')])
test('norm_pre_bounded_bool', check_contains,
  args: ['pre-bounded-empty: fired=[1-9]', tlsfnorm_exe, '--pre-passes',
         'pre-bounded-bool', '--norm-stats',
         files('test/cases/normalization_bounded_bool.tlsf')])
test('norm_pre_spine_split', check_contains,
  args: ['pre-spine-split: fired=[1-9]', tlsfnorm_exe, '--pre-passes',
         'pre-spine-split', '--norm-stats',
         files('test/cases/normalization_pre_split.tlsf')])
# Cross-check: a pre-normalized spec expands to the same TLSF as the original
# (expand(original) == expand(pre_normalize(original))).
test('norm_pre_indexed_x_equiv', check,
  args: [files('test/cases/normalization_xn.split.tlsf'), tlsfnorm_exe,
         '--pre-passes', 'pre-indexed-x', '--passes', 'split',
         files('test/cases/normalization_xn.tlsf')])

# Constant folding (--weak-simplify): non-collapsing, collapse-to-false, and
# collapse-to-true cases exercise every simplify_weak_local rule.
test('ltl_simplify_weak', check,
  args: [files('test/cases/simplify_demo.s0.ltl'),
         tlsf2ltl_exe, '--weak-simplify',
         files('test/cases/simplify_demo.tlsf')])

test('ltl_simplify_strong', check,
  args: [files('test/cases/simplify_demo.s1.ltl'),
         tlsf2ltl_exe, '--strong-simplify',
         files('test/cases/simplify_demo.tlsf')])

test('ltl_simplify_false', check,
  args: [files('test/cases/collapse_demo.s0.ltl'),
         tlsf2ltl_exe, '--weak-simplify',
         files('test/cases/collapse_demo.tlsf')])

test('ltl_simplify_true', check,
  args: [files('test/cases/truths_demo.s0.ltl'),
         tlsf2ltl_exe, '--weak-simplify',
         files('test/cases/truths_demo.tlsf')])

# Push-inwards and pull-outwards rewrites.
foreach rw : [['push-globally-in', 'pgi'], ['push-finally-in', 'pfi'],
              ['push-next-in', 'pxi'], ['pull-globally-out', 'pgo'],
              ['pull-finally-out', 'pfo'], ['pull-next-out', 'pxo']]
  test('ltl_' + rw[1], check,
    args: [files('test/cases/rewrites.' + rw[1] + '.ltl'),
           tlsf2ltl_exe, '--' + rw[0],
           files('test/cases/rewrites.tlsf')])
endforeach

test('tlsf_basic_expand', check,
  args: [files('test/cases/Patterns_Uright_uright06.basic.tlsf'),
         tlsf2tlsf_exe, '--basic',
         files('test/cases/Patterns_Uright_uright06.tlsf')])

test('tlsf_param_subst', check,
  args: [files('test/cases/param_demo.subst.tlsf'),
         tlsf2tlsf_exe, '--param', 'n=5',
         files('test/cases/param_demo.tlsf')])

test('info_block', check,
  args: [files('test/cases/Patterns_Uright_uright06.info'),
         tlsfinfo_exe, '--info',
         files('test/cases/Patterns_Uright_uright06.tlsf')])

foreach c : ['next_n', 'ranges']
  test('info_bounded_' + c, check,
    args: [files('test/cases/' + c + '.bounded'),
           tlsfinfo_exe, '--bounded-temporal',
           files('test/cases/' + c + '.tlsf')])
endforeach

# GR(1) recognition.
foreach c : ['gr0_spec', 'gr1_spec', 'gr2_spec', 'gr4_spec', 'notgr_spec']
  test('gr_' + c, check,
    args: [files('test/cases/' + c + '.gr'),
           tlsfinfo_exe, '--generalized-reactivity', files('test/cases/' + c + '.tlsf')])
endforeach

# tlsfinfo selection flags.
foreach sel : [['--title', 'title'], ['--description', 'description'],
               ['--semantics', 'semantics'], ['--target', 'target'],
               ['--tags', 'tags'], ['--parameters', 'params'],
               ['--input-signals', 'inputs'], ['--output-signals', 'outputs'],
               ['--expanded-ins', 'expanded_ins'],
               ['--expanded-outs', 'expanded_outs'],
               ['--info', 'info']]
  test('info_' + sel[1], check,
    args: [files('test/cases/meta.' + sel[1]),
           tlsfinfo_exe, sel[0], files('test/cases/meta.tlsf')])
endforeach
test('info_all', check,
  args: [files('test/cases/meta.all'), tlsfinfo_exe, files('test/cases/meta.tlsf')])
test('info_check', check,
  args: [files('test/cases/meta.check'), tlsfinfo_exe, '--check',
         files('test/cases/meta.tlsf')])
test('err_check_invalid', xfail,
  args: [tlsfinfo_exe, '--check', files('test/cases/bad_syntax.tlsf')])

# Primed (and @) identifiers, e.g. req' / grant'.
test('primes_inputs', check,
  args: [files('test/cases/primes.inputs'), tlsfinfo_exe, '--input-signals',
         files('test/cases/primes.tlsf')])
test('primes_ltl', check,
  args: [files('test/cases/primes.ltl'), tlsf2ltl_exe,
         files('test/cases/primes.tlsf')])

# Uppercase atom names: ltlxba lowercases them (spot/ltl2ba read uppercase as
# operators, so this is what ltlsynt consumes, matching syfco -f ltlxba); the
# faithful ltl dialect keeps the original case.
test('ltl_upper_atoms_ltlxba', check,
  args: [files('test/cases/upper_atoms.ltlxba.ltl'), tlsf2ltl_exe,
         '--format', 'ltlxba', files('test/cases/upper_atoms.tlsf')])
test('ltl_upper_atoms_ltl', check,
  args: [files('test/cases/upper_atoms.ltl'), tlsf2ltl_exe,
         '--format', 'ltl', files('test/cases/upper_atoms.tlsf')])

# tlsf2ltl modes: safety / liveness selection and -os/-ot overrides.
test('ltl_safety', check,
  args: [files('test/cases/arbiter_simple.safety.ltl'),
         tlsf2ltl_exe, '--safety', files('test/arbiter_simple.tlsf')])
test('ltl_liveness', check,
  args: [files('test/cases/arbiter_simple.liveness.ltl'),
         tlsf2ltl_exe, '--liveness', files('test/arbiter_simple.tlsf')])
test('ltl_os_moore', check,
  args: [files('test/cases/conv_moore_mealy.os.ltl'),
         tlsf2ltl_exe, '--overwrite-semantics', 'Moore', files('test/cases/conv_moore_mealy.tlsf')])

# Exercises the NNF duals (R/W/M/U, <->, !F, !U).
test('ltl_operators', check,
  args: [files('test/cases/operators.ltl'),
         tlsf2ltl_exe, files('test/cases/operators.tlsf')])
test('ltl_operators_full', check,
  args: [files('test/cases/operators.full.ltl'),
         tlsf2ltl_exe, '--parenthesize', files('test/cases/operators.tlsf')])

# tlsf2tlsf default re-emission: GLOBAL section (parameters, definitions,
# definition calls), bus-range expressions, big-operators and SIZEOF.
test('tlsf_reemit', check,
  args: [files('test/cases/meta.reemit.tlsf'),
         tlsf2tlsf_exe, files('test/cases/meta.tlsf')])
test('tlsf_reemit_defs', check,
  args: [files('test/cases/defs.reemit.tlsf'),
         tlsf2tlsf_exe, files('test/cases/defs.tlsf')])
test('tlsf_subst_defs', check,
  args: [files('test/cases/defs.subst.tlsf'),
         tlsf2tlsf_exe, '--param', 'n=5', files('test/cases/defs.tlsf')])
test('tlsf_reemit_quant', check,
  args: [files('test/cases/expand_demo.reemit.tlsf'),
         tlsf2tlsf_exe, files('test/cases/expand_demo.tlsf')])
test('err_tlsf_bad_param', xfail,
  args: [tlsf2tlsf_exe, '--param', 'nope=1', files('test/cases/defs.tlsf')])

# Error paths: these must exit non-zero.
test('err_no_input',     xfail, args: [tlsf2ltl_exe])
test('err_missing_file', xfail, args: [tlsf2ltl_exe, 'does_not_exist.tlsf'])
test('err_bad_param',    xfail,
  args: [tlsf2ltl_exe, '--param', 'oops', files('test/cases/meta.tlsf')])
test('err_bad_semantics', xfail,
  args: [tlsf2ltl_exe, '--overwrite-semantics', 'Bogus', files('test/cases/meta.tlsf')])
test('err_parse',        xfail,
  args: [tlsf2ltl_exe, files('test/cases/bad_syntax.tlsf')])
test('err_strong_next_infinite', xfail,
  args: [tlsf2ltl_exe, files('test/cases/strong_next_infinite.tlsf')])
test('err_strong_next_overwrite', xfail,
  args: [tlsf2ltl_exe, '--overwrite-semantics', 'Mealy',
         files('test/cases/gnext_strong_fin.tlsf')])
# Expansion failure (an unbound parameter) must error.
test('err_expand',       xfail,
  args: [tlsf2ltl_exe, files('test/cases/bad_expand.tlsf')])

# Definition expansion: nullary + parameterised definitions, recursive
# case-definitions (with `otherwise`), integer-returning defs, and SIZEOF.
test('expand_defs_gr', check,
  args: [files('test/cases/defs.gr'), tlsfinfo_exe,
         '--generalized-reactivity', files('test/cases/defs.tlsf')])
test('expand_mutual_exclusion', check,
  args: [files('test/cases/mutual_exclusion.ltl'), tlsf2ltl_exe,
         files('test/cases/mutual_exclusion.tlsf')])
test('expand_recursion', check,
  args: [files('test/cases/recursion.ltl'), tlsf2ltl_exe,
         files('test/cases/recursion.tlsf')])
# X[n] n-fold next operator expands to nested X.
test('next_n', check,
  args: [files('test/cases/next_n.ltl'), tlsf2ltl_exe,
         files('test/cases/next_n.tlsf')])
# Default re-emission of a case-definition (exercises ITE/comparison printing).
test('reemit_cases', check,
  args: [files('test/cases/recursion.reemit.tlsf'), tlsf2tlsf_exe,
         files('test/cases/recursion.tlsf')])
# A call to an undefined definition must error.
test('err_undef_def', xfail,
  args: [tlsf2ltl_exe, files('test/cases/undef_def.tlsf')])

# Exercises the assumptions -> guarantees implication path (the cases above
# are guarantee-only).
test('ltl_assume_guarantee', check,
  args: [files('test/cases/arbiter_simple.ltl'),
         tlsf2ltl_exe, files('test/arbiter_simple.tlsf')])

# Expansion: parameters, parametric bus ranges, bus indexing, bounded
# big-operators (&&[..]/||[..]) and SIZEOF.
test('expand_ltl', check,
  args: [files('test/cases/expand_demo.ltl'),
         tlsf2ltl_exe, files('test/cases/expand_demo.tlsf')])

test('expand_ltl_param', check,
  args: [files('test/cases/expand_demo.n2.ltl'),
         tlsf2ltl_exe, '--param', 'n=2',
         files('test/cases/expand_demo.tlsf')])

test('expand_basic', check,
  args: [files('test/cases/expand_demo.basic.tlsf'),
         tlsf2tlsf_exe, '--basic',
         files('test/cases/expand_demo.tlsf')])

# Full six-section TLSF semantics:
# INITIALLY -> (PRESET & ((G REQUIRE & ASSUME) -> (G ASSERT & GUARANTEE)))
test('semantics_sections', check,
  args: [files('test/cases/sections.ltl'),
         tlsf2ltl_exe, files('test/cases/sections.tlsf')])

# A strict (Strict,*) spec emits the strict weak-until form:
# (PRESET & G ASSERT) W !(INITIALLY & G REQUIRE), plus the liveness implication.
test('semantics_strict', check,
  args: [files('test/cases/sections.strict.ltl'),
         tlsf2ltl_exe, files('test/cases/sections_strict.tlsf')])

# Relax a strict spec by overwriting its semantics to non-strict: plain E -> S.
test('semantics_relax_via_override', check,
  args: [files('test/cases/sections.ltl'),
         tlsf2ltl_exe, '--overwrite-semantics', 'Mealy',
         files('test/cases/sections_strict.tlsf')])

# Mealy/Moore conversion when SEMANTICS and TARGET disagree.
test('semantics_moore_to_mealy', check,
  args: [files('test/cases/conv_moore_mealy.ltl'),
         tlsf2ltl_exe, files('test/cases/conv_moore_mealy.tlsf')])
