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

# Optional safety backend dependency.  AbsSynthe is vendored as a submodule so
# CI and offline builds can stay self-contained after the initial checkout.
abssynthe_dir = join_paths(meson.project_source_root(), 'external', 'AbsSynthe')
abssynthe_build_sh = join_paths(abssynthe_dir, 'build.sh')
abssynthe_bin = join_paths(abssynthe_dir, 'binary', 'abssynthe')
abssynthe_submodule_ready = fs.exists(abssynthe_build_sh)
abssynthe_local = find_program(abssynthe_bin, required: false)
abssynthe_system = find_program('abssynthe', required: false)

if git.found()
  run_target(
    'abssynthe-submodule',
    command: [
      git,
      'submodule',
      'update',
      '--init',
      '--recursive',
      'external/AbsSynthe',
    ],
  )
endif

if abssynthe_submodule_ready
  message('AbsSynthe submodule found at external/AbsSynthe')
  if bash.found()
    run_target('abssynthe-build', command: [bash, abssynthe_build_sh])
  endif
else
  warning(
    'AbsSynthe submodule is not initialized. Run `meson compile -C build ' +
    'abssynthe-submodule` or `git submodule update --init --recursive ' +
    'external/AbsSynthe` before using the AbsSynthe backend.',
  )
endif

if abssynthe_local.found()
  message('AbsSynthe binary found at ' + abssynthe_bin)
elif abssynthe_system.found()
  message('AbsSynthe binary found in PATH')
elif abssynthe_submodule_ready
  warning(
    'AbsSynthe submodule is present but binary/abssynthe is missing. Run ' +
    '`meson compile -C build abssynthe-build`.',
  )
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
  'src/graph.c',
  'src/wl.c',
  'src/templates.c',
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

tlsfcompose_exe = executable(
  'tlsfcompose',
  sources: ['src/main_tlsfcompose.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

# ---------------------------------------------------------------------------
# Integration / regression tests (golden-output diffs)
#
# Self-contained: a representative set of SYNTCOMP TLSF specs lives under
# test/cases/ with their expected tool output.  No external tools (syfco,
# spot) are needed, so these run anywhere — including CI.
# ---------------------------------------------------------------------------

check = files('test/check.sh')
xfail = files('test/expect_fail.sh')

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
                'reaction_unsafe', 'ddef_demo', 'response_free',
                'response_blocked', 'inv_const', 'inv_skolem', 'inv_multi',
                'inv_decline', 'inv_valid']
  test('tmpl_' + name, check_wl,
    args: [files('test/cases/' + name + '.csnf'), tlsftemplates_exe,
           '--certify', '--solve', '--format', 'csnf',
           files('test/cases/' + name + '.tlsf')])
endforeach
test('tmpl_arbiter', check_wl,
  args: [files('test/cases/arbiter2.csnf'), tlsftemplates_exe,
         '--certify', '--solve', '--format', 'csnf',
         files('test/cases/arbiter2.tlsf')])
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
foreach name : ['compose_demo', 'cluster_split']
  test('compose_' + name, check,
    args: [files('test/cases/' + name + '.compose'), tlsfcompose_exe,
           files('test/cases/' + name + '.tlsf')])
endforeach
# --aiger combinational path (no cluster -> no ltlsynt): golden-testable in CI.
foreach name : ['def_demo', 'inv_skolem', 'reaction_ok']
  test('aiger_' + name, check,
    args: [files('test/cases/' + name + '.aag'), tlsfcompose_exe, '--aiger',
           files('test/cases/' + name + '.tlsf')])
endforeach
# --aiger reader/merge path with a fake ltlsynt stub (deterministic, no real
# ltlsynt): exercises run_ltlsynt + aig_read_aag + aig_merge in CI.
test('aiger_merge', check,
  args: [files('test/cases/compose_demo.merged.aag'), tlsfcompose_exe, '--aiger',
         '--ltlsynt', files('test/fake_ltlsynt.sh'),
         files('test/cases/compose_demo.tlsf')])
# --aiger cluster path needs real ltlsynt: only run where it is available.
if ltlsynt.found()
  test('aiger_cluster', tlsfcompose_exe,
    args: ['--aiger', files('test/cases/compose_demo.tlsf')])
  test('aiger_unrealizable', xfail,
    args: [tlsfcompose_exe, '--aiger', files('test/cases/inv_decline.tlsf')])
endif
test('tmpl_sat_unimplemented', xfail,
  args: [tlsftemplates_exe, '--side-conditions', 'sat',
         files('test/cases/def_demo.tlsf')])
test('tmpl_from_gsnf_unimplemented', xfail,
  args: [tlsftemplates_exe, '--from-gsnf', files('test/cases/def_demo.tlsf')])

# tlsfbenchgraph: per-spec corpus metrics TSV (file column is a basename, so the
# golden is path-independent).
test('benchgraph_tsv', check,
  args: [files('test/cases/bench.tsv'), tlsfbenchgraph_exe, '--wl', '4',
         '--summary', files('test/cases/arbiter2.tlsf'),
         files('test/cases/def_demo.tlsf'),
         files('test/cases/roundrobin2.tlsf')])
test('benchgraph_jobs_unimplemented', xfail,
  args: [tlsfbenchgraph_exe, '--jobs', '4', files('test/cases/def_demo.tlsf')])

# Constraint decomposition: cover --split exposes shapes inside a single
# conjunctive formula; tlsfnorm re-emits the split spec.
test('graph_split_off', check,
  args: [files('test/cases/arbiter1formula.graph.txt'),
         tlsfgraph_exe, '--templates', files('test/cases/arbiter1formula.tlsf')])
test('graph_split_on', check,
  args: [files('test/cases/arbiter1formula.split.txt'),
         tlsfgraph_exe, '--split', '--templates',
         files('test/cases/arbiter1formula.tlsf')])
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
test('norm_macro_unimplemented', xfail,
  args: [tlsfnorm_exe, '--passes', 'macro',
         files('test/cases/arbiter1formula.tlsf')])

# Reserved (later-milestone) flags must error, not be silently ignored.
test('graph_norm_unimplemented', xfail,
  args: [tlsfgraph_exe, '--norm-depth', '3', files('test/cases/arbiter2.tlsf')])
test('graph_quotient_unimplemented', xfail,
  args: [tlsfgraph_exe, '--graph', 'quotient', files('test/cases/arbiter2.tlsf')])
test('wl_from_gsnf_unimplemented', xfail,
  args: [tlsfwl_exe, '--from-gsnf', files('test/cases/arbiter2.tlsf')])

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
