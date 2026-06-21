project(
  'tlsf-tools',
  'c',
  version: '0.1.0',
  license: 'MIT',
  default_options: [
    'warning_level=3',
    'werror=false',
    'b_ndebug=if-release',
  ],
)

fs = import('fs')

# ---------------------------------------------------------------------------
# Compiler: force C23 via -std=c23 (meson's c_std enum doesn't map 'c23'
# until meson 1.3+, but clang 16+ and gcc 14+ accept it directly).
# ---------------------------------------------------------------------------

cc = meson.get_compiler('c')
m_dep = cc.find_library('m', required: false)  # WL kernels (sqrt)

c23_flag = cc.get_supported_arguments(['-std=c23', '-std=c2x'])
add_project_arguments(c23_flag, language: 'c')

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
if cpu == 'avx2'
  cpu_flags = ['-mavx2', '-mfma']
elif cpu == 'avx512'
  cpu_flags = ['-mavx512f', '-mavx512bw', '-mavx512vpopcntdq']
elif cpu == 'neon'
  cpu_flags = ['-march=armv8-a+simd']
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
# Optional: only used to test `tlsfcompose --aiger`'s cluster path; CI skips
# those tests when ltlsynt is absent.
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
# In-process safety + GR(1) solver: OxiDD (Rust + C FFI), vendored as a
# submodule and built manually so the default build/CI stay dependency-free.
# `meson compile -C build oxidd-build` produces the static library + cbindgen
# header; reconfigure to pick them up.
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
      'OxiDD feature requested but artifacts are missing. Run ' +
      '`meson compile -C build oxidd-build` (after ' +
      '`meson compile -C build oxidd-submodule`), then reconfigure.',
    )
  endif
  # Rust staticlib pulls in the system threading/dl/math runtime.
  oxidd_dep = declare_dependency(
    include_directories: include_directories('external/oxidd/build/include'),
    link_args: [oxidd_lib_path, '-lpthread', '-ldl', '-lm'],
  )
  have_oxidd = true
  message('OxiDD safety solver enabled (' + oxidd_lib_path + ')')
elif oxidd_feature.auto()
  message('OxiDD safety solver disabled (artifacts absent; build with ' +
          '`meson compile -C build oxidd-build`)')
endif

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
  'src/classify.c',
  'src/apset.c',
  'src/cover.c',
  'src/recognize.c',
  'src/pipeline.c',
  'src/graph.c',
  'src/wl.c',
  'src/templates.c',
  'src/templates_certify.c',
  'src/residual.c',
  'src/aiger.c',
  'src/gr.c',
  'src/print_ltlxba.c',
  'src/print_tlsf.c',
  flex_out[0],
  bison_out[0],
  bison_out[1],   # tlsf_parse.h — declare as a source so the generated lexer
                  # (which #includes it) is compiled only after it exists.
]

tlsf_lib = static_library(
  'tlsf',
  lib_sources,
  include_directories: inc,
  dependencies: m_dep,
  pic: false,
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

tlsfgraph_exe = executable(
  'tlsfgraph',
  sources: ['src/main_tlsfgraph.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

tlsfwl_exe = executable(
  'tlsfwl',
  sources: ['src/main_tlsfwl.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

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

tlsfnorm_exe = executable(
  'tlsfnorm',
  sources: ['src/main_tlsfnorm.c', bison_out[1]],
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
              'src/compose_games.c', 'src/compose_solve.c',
              'src/safety_oxidd.c', 'src/gr1_oxidd.c',
              'src/oxidd_common.c', bison_out[1]],
    c_args: ['-DHAVE_OXIDD'],
    dependencies: [oxidd_dep],
    link_with: tlsf_lib,
    include_directories: inc,
    install: true,
  )

  tlsfsolve_exe = executable(
    'tlsfsolve',
    sources: ['src/main_tlsfsolve.c', 'src/safety_oxidd.c', 'src/gr1_oxidd.c',
              'src/oxidd_common.c'],
    c_args: ['-DHAVE_OXIDD'],
    dependencies: [oxidd_dep],
    link_with: tlsf_lib,
    include_directories: inc,
    install: true,
  )
endif

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

test('tlsf_enum_basic', check,
  args: [files('test/cases/enum_demo.basic.tlsf'),
         tlsf2tlsf_exe, files('test/cases/enum_demo.tlsf')])

# tlsfgraph: GSNF text/gsnf/dot/tsv + template candidates (arbiter pattern).
check_wl = files('test/check_wl.sh')   # normalizes embedded paths to basenames
test('graph_text', check,
  args: [files('test/cases/arbiter2.graph.txt'),
         tlsfgraph_exe, '--templates', files('test/cases/arbiter2.tlsf')])
test('graph_gsnf', check,
  args: [files('test/cases/arbiter2.graph.gsnf'),
         tlsfgraph_exe, '--format', 'gsnf', '--templates',
         files('test/cases/arbiter2.tlsf')])
test('graph_tsv', check,
  args: [files('test/cases/arbiter2.graph.tsv'),
         tlsfgraph_exe, '--format', 'tsv', '--templates',
         files('test/cases/arbiter2.tlsf')])
test('graph_dot', check,
  args: [files('test/cases/arbiter2.graph.dot'),
         tlsfgraph_exe, '--format', 'dot', files('test/cases/arbiter2.tlsf')])
test('graph_filter', check,
  args: [files('test/cases/arbiter2.graph.live.tsv'),
         tlsfgraph_exe, '--format', 'tsv', '--guarantees', '--liveness',
         files('test/cases/arbiter2.tlsf')])
test('graph_constraint_kind', check,
  args: [files('test/cases/arbiter2.graph.cons.gsnf'),
         tlsfgraph_exe, '--format', 'gsnf', '--graph', 'constraint',
         files('test/cases/arbiter2.tlsf')])

# WL features (M4): tlsfgraph --wl and the tlsfwl comparison tool.
test('graph_wl', check_wl,
  args: [files('test/cases/arbiter2.graph.wl'),
         tlsfgraph_exe, '--wl', '2', files('test/cases/arbiter2.tlsf')])
test('wl_matrix', check_wl,
  args: [files('test/cases/wl_matrix.txt'),
         tlsfwl_exe, '--matrix', files('test/cases/arbiter2.tlsf'),
         files('test/cases/resp1.tlsf')])
test('wl_compare', check_wl,
  args: [files('test/cases/wl_compare.txt'),
         tlsfwl_exe, '--compare', files('test/cases/resp1.tlsf'),
         files('test/cases/arbiter2.tlsf'), files('test/cases/resp1.tlsf')])
test('wl_nearest', check,   # output is index-only, no paths to normalize
  args: [files('test/cases/wl_nearest.txt'),
         tlsfwl_exe, '--nearest', '1', '--kernel', 'jaccard',
         files('test/cases/arbiter2.tlsf'), files('test/cases/resp1.tlsf'),
         files('test/cases/arbiter2.tlsf')])
test('wl_version', check,
  args: [files('test/cases/wl_version.txt'), tlsfwl_exe, '--version'])
test('wl_labels_basic', check_wl,
  args: [files('test/cases/wl_labels_basic.txt'), tlsfwl_exe,
         '--labels', 'basic', '--matrix',
         files('test/cases/arbiter2.tlsf'), files('test/cases/resp1.tlsf')])
test('wl_kernel_dot', check_wl,
  args: [files('test/cases/wl_kernel_dot.txt'), tlsfwl_exe,
         '--kernel', 'dot', '--compare', files('test/cases/resp1.tlsf'),
         files('test/cases/arbiter2.tlsf')])
test('wl_split', check_wl,
  args: [files('test/cases/wl_split_matrix.txt'), tlsfwl_exe,
         '--split', '--matrix',
         files('test/cases/arbiter2.tlsf'), files('test/cases/resp1.tlsf')])
test('graph_wl_template', check_wl,
  args: [files('test/cases/arbiter2.graph.wltmpl'),
         tlsfgraph_exe, '--format', 'gsnf', '--wl', '1', '--wl-labels',
         'template', files('test/cases/arbiter2.tlsf')])

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
# Composition soundness: tlsftemplates --check (whole-spec verdict) and
# tlsfresidual (leftover LTL after the accepted blocks).
foreach name : ['reaction_ok', 'compose_conflict', 'compose_cycle',
                'compose_partial', 'subst_reduce', 'server_merge',
                'arbiter_nomutex']
  test('check_' + name, check_wl,
    args: [files('test/cases/' + name + '.check'), tlsftemplates_exe,
           '--check', '--format', 'csnf', files('test/cases/' + name + '.tlsf')])
endforeach
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
  test('compose_aiger_unclassified_atom', check,
    args: [files('test/cases/aiger_unclassified_atom.compose'), tlsfcompose_exe,
           files('test/cases/aiger_unclassified_atom.tlsf')])
  # --aiger local-controller path (no cluster -> no ltlsynt): golden-testable in CI.
  foreach name : ['def_demo', 'inv_skolem', 'reaction_ok', 'dbuchi_switch']
    test('aiger_' + name, check,
      args: [files('test/cases/' + name + '.aag'), tlsfcompose_exe, '--aiger',
             '--ltlsynt', '/bin/false',
             files('test/cases/' + name + '.tlsf')])
  endforeach
  # --aiger merge path: OxiDD solves the bounded-liveness cluster, the
  # combinational controller drives 'o', and the merged AIGER is golden-tested.
  # fake_ltlsynt is passed but not invoked (OxiDD handles the only cluster).
  test('aiger_merge', check,
    args: [files('test/cases/compose_demo.merged.aag'), tlsfcompose_exe, '--aiger',
           '--ltlsynt', files('test/fake_ltlsynt.sh'),
           files('test/cases/compose_demo.tlsf')])
  # Output-free (input-only) guarantee cluster: no controller is merged, but it
  # is realizability-checked via (fake) ltlsynt -- here G F req is realizable
  # given the assumptions, so the merged AIGER is unchanged.
  test('aiger_input_gua_skip', check,
    args: [files('test/cases/input_gua_skip.aag'), tlsfcompose_exe, '--aiger',
           '--ltlsynt', files('test/fake_ltlsynt.sh'),
           files('test/cases/input_gua_skip.tlsf')])
  # Bare W in IMPL antecedent where release is sys output must NOT be encoded as
  # W/R safety (would be a false UNREAL); falls through to ltlsynt.
  test('aiger_wr_impl_bare_w_antecedent', check,
    args: [files('test/cases/wr_impl_bare_w_antecedent.aag'), tlsfcompose_exe,
           '--aiger', '--ltlsynt', files('test/fake_ltlsynt.sh'),
           files('test/cases/wr_impl_bare_w_antecedent.tlsf')])
  # aiger_unclassified_atom: OxiDD correctly identifies this spec as unrealizable
  # (BURST4 is env input; system cannot force req to be true in the consequent).
  test('aiger_unclassified_atom', xfail,
    args: [tlsfcompose_exe, '--aiger', '--ltlsynt', '/bin/false',
           files('test/cases/aiger_unclassified_atom.tlsf')])
  # Uppercase atom names: ltlsynt's parser mishandles them, so the cluster is
  # lowercased for the (fake) ltlsynt call and the returned controller is renamed
  # back -- the merged AIGER must carry the spec's ORIGINAL-case symbols.
  test('aiger_upper_atoms_rename', check,
    args: [files('test/cases/upper_atoms.merged.aag'), tlsfcompose_exe,
           '--aiger', '--ltlsynt', files('test/fake_ltlsynt.sh'),
           files('test/cases/upper_atoms.tlsf')])
  # NOT(G(w)) is liveness: G(w)->false is simplified to NOT(G(w)) by the parser;
  # cluster_shape_visit must detect this as liveness (not W/R-safety).
  test('aiger_not_g_is_liveness', check_fail_stderr,
    args: [files('test/cases/compose_not_g_is_liveness.err'), tlsfcompose_exe,
           '--aiger', '--ltlsynt', '/bin/false',
           files('test/cases/compose_not_g_is_liveness.tlsf')])
  # Self-verification gate mechanism (trivial verifiers; no AbsSynthe needed).
  # /bin/true = "verified" -> controller kept (exit 0);
  # /bin/false = "violation" -> fall back to ltlsynt (here /bin/false -> failure).
  test('aiger_verify_gate_keeps', tlsfcompose_exe,
    args: ['--aiger', '--ltlsynt', '/bin/false', '--verify', '/bin/true',
           files('test/cases/gr1_spec.tlsf')])
  test('aiger_verify_gate_falls_back', xfail,
    args: [tlsfcompose_exe, '--aiger',
           '--ltlsynt', '/bin/false', '--verify', '/bin/false',
           files('test/cases/gr1_spec.tlsf')])
  # --aiger cluster path needs real ltlsynt: only run where it is available.
  if ltlsynt.found()
    test('aiger_cluster', tlsfcompose_exe,
      args: ['--aiger', files('test/cases/compose_demo.tlsf')])
    test('aiger_unrealizable', xfail,
      args: [tlsfcompose_exe, '--aiger', files('test/cases/inv_decline.tlsf')])
    # Regression: with --split, G(o && a) decomposes into G(o) and the
    # input-only G(a); the output-free G(a) must be realizability-checked (not
    # skipped) so the genuinely unrealizable spec is reported UNREALIZABLE.
    test('aiger_unrealizable_split', xfail,
      args: [tlsfcompose_exe, '--split', '--aiger',
             files('test/cases/inv_decline.tlsf')])
  endif
endif
# tlsfbenchgraph: per-spec corpus metrics TSV (file column is a basename, so the
# golden is path-independent).
test('benchgraph_tsv', check,
  args: [files('test/cases/bench.tsv'), tlsfbenchgraph_exe, '--wl', '4',
         '--summary', files('test/cases/arbiter1formula.tlsf'),
         files('test/cases/arbiter2.tlsf'),
         files('test/cases/cluster_split.tlsf'),
         files('test/cases/def_demo.tlsf'),
         files('test/cases/roundrobin2.tlsf')])
if python3.found()
  test('bounded_corpus_harness', check,
    args: [files('test/cases/bounded_corpus.tsv'),
           files('scripts/bounded_corpus.py'), '--benchgraph', tlsfbenchgraph_exe,
           '--mem-mb', '512', '--timeout', '5', '--wl', '4', '--quiet',
           files('test/cases/def_demo.tlsf'),
           files('test/cases/reaction_ok.tlsf')])
  if have_oxidd
    test('bounded_synthesis_harness', python3,
      args: [files('scripts/bounded_synthesis.py'),
             '--compose', tlsfcompose_exe,
             '--ltlsynt', files('test/fake_ltlsynt.sh'),
             '--mem-mb', '512', '--timeout', '5', '--quiet',
             files('test/cases/assume_delay_real.tlsf'),
             files('test/cases/inv_valid.tlsf')])
  endif
endif
if python3.found() and spot_python_found
  tlsf2ltl_path = join_paths(meson.current_build_dir(), 'tlsf2ltl')
  if have_oxidd
    tlsfcompose_path = join_paths(meson.current_build_dir(), 'tlsfcompose')
    test('verify_aiger_reaction_ok', python3,
      args: [files('scripts/verify_aiger_ltl.py'),
             '--compose', tlsfcompose_path,
             '--tlsf2ltl', tlsf2ltl_path,
             '--tlsf', files('test/cases/reaction_ok.tlsf')])
    test('verify_aiger_dbuchi_switch', python3,
      args: [files('scripts/verify_aiger_ltl.py'),
             '--compose', tlsfcompose_path,
             '--ltlsynt', '/bin/false',
             '--tlsf2ltl', tlsf2ltl_path,
             '--tlsf', files('test/cases/dbuchi_switch.tlsf')])
    # OxiDD in-process safety + GR(1) solver: Spot-verify controllers.
    foreach name : ['assume_delay_real', 'cluster_prune_safe',
                    'strict_safety',
                    'bounded_resp', 'bounded_until', 'bounded_wuntil',
                    'wr_response', 'wr_release', 'wr_resp_nox', 'wr_rel_resp',
                    'wr_assume', 'wr_distributable_impl', 'wr_gated_nox',
                    'wr_xdelay2', 'wr_r_collapse', 'wr_r_x_in_body']
      test('verify_aiger_oxidd_' + name, python3,
        args: [files('scripts/verify_aiger_ltl.py'),
               '--compose', tlsfcompose_path,
               '--ltlsynt', '/bin/false',
               '--tlsf2ltl', tlsf2ltl_path,
               '--tlsf', files('test/cases/' + name + '.tlsf')])
    endforeach
    # wr_gated_collapse is unrealizable; OxiDD correctly exits non-zero.
    test('verify_aiger_oxidd_wr_gated_collapse_unreal', xfail,
      args: [tlsfcompose_exe,
             '--aiger', '--ltlsynt', '/bin/false',
             files('test/cases/wr_gated_collapse.tlsf')])
    # GR(1): in-process OxiDD PPS fixpoint solver, Spot-verified.
    foreach name : ['gr1_spec', 'gr1_response', 'gr1_multifair', 'gr1_init',
                    'gr1_preset', 'gr1_weak', 'gr1_strict', 'gr1_strict_sticky',
                    'gr1_strict_multi']
      test('verify_aiger_oxidd_gr1_' + name, python3,
        args: [files('scripts/verify_aiger_ltl.py'),
               '--compose', tlsfcompose_path,
               '--ltlsynt', '/bin/false',
               '--tlsf2ltl', tlsf2ltl_path,
               '--tlsf', files('test/cases/' + name + '.tlsf')])
    endforeach
    # OxiDD correctly identifies these specs as unrealizable.
    foreach name : ['inv_decline', 'cluster_assume']
      test('verify_aiger_oxidd_' + name + '_unreal', xfail,
        args: [tlsfcompose_exe,
               '--aiger', '--ltlsynt', '/bin/false',
               files('test/cases/' + name + '.tlsf')])
    endforeach
    # tlsfsolve: standalone AIGER game solver.
    test('tlsfsolve_real', check,
      args: [files('test/cases/solve_real.out.aag'),
             tlsfsolve_exe, files('test/cases/solve_real.aag')])
    test('tlsfsolve_unreal', xfail,
      args: [tlsfsolve_exe, files('test/cases/solve_unreal.aag')])
  endif
endif

# Constraint decomposition: cover --split exposes shapes inside a single
# conjunctive formula; tlsfnorm re-emits the split spec.
test('graph_split_off', check,
  args: [files('test/cases/arbiter1formula.graph.txt'),
         tlsfgraph_exe, '--templates', files('test/cases/arbiter1formula.tlsf')])
test('graph_split_on', check,
  args: [files('test/cases/arbiter1formula.split.txt'),
         tlsfgraph_exe, '--split', '--templates',
         files('test/cases/arbiter1formula.tlsf')])
# CLI option coverage: --version, --param, --safety, --assumptions, --liveness.
test('graph_version', check,
  args: [files('test/cases/graph_version.txt'), tlsfgraph_exe, '--version'])
test('graph_param', check,
  args: [files('test/cases/graph_param_demo.graph.txt'), tlsfgraph_exe,
         '--param', 'n=5', '--param', 'k=2',
         files('test/cases/param_demo.tlsf')])
test('graph_safety_filter', check,
  args: [files('test/cases/graph_arbiter2_safety.txt'), tlsfgraph_exe,
         '--safety', files('test/cases/arbiter2.tlsf')])
test('graph_assumptions_filter', check,
  args: [files('test/cases/graph_arbiter2_assumptions.txt'), tlsfgraph_exe,
         '--assumptions', files('test/cases/arbiter2.tlsf')])
test('graph_liveness_filter', check,
  args: [files('test/cases/graph_param_demo_liveness.txt'), tlsfgraph_exe,
         '--liveness', '--param', 'n=5', '--param', 'k=2',
         files('test/cases/param_demo.tlsf')])
test('graph_roles_guarantee', check,
  args: [files('test/cases/arbiter2.no_tmpl.txt'), tlsfgraph_exe,
         '--roles', 'GUARANTEE', files('test/cases/arbiter2.tlsf')])
test('graph_wl_labels_basic', check_wl,
  args: [files('test/cases/arbiter2.wl0_basic.txt'), tlsfgraph_exe,
         '--wl', '0', '--wl-labels', 'basic', files('test/cases/arbiter2.tlsf')])
test('graph_template_named', check,
  args: [files('test/cases/arbiter1formula.tmpl_reaction.txt'), tlsfgraph_exe,
         '--template', 'reaction', files('test/cases/arbiter1formula.tlsf')])
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
