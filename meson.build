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

# ---------------------------------------------------------------------------
# Compiler: force C23 via -std=c23 (meson's c_std enum doesn't map 'c23'
# until meson 1.3+, but clang 16+ and gcc 14+ accept it directly).
# ---------------------------------------------------------------------------

cc = meson.get_compiler('c')

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
