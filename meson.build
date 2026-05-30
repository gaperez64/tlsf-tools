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
  'src/expand.c',
  'src/nnf.c',
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
         tlsfinfo_exe, '-i',
         files('test/cases/Patterns_Uright_uright06.tlsf')])

# GR(1) recognition.
foreach c : ['gr0_spec', 'gr1_spec', 'gr2_spec', 'notgr_spec']
  test('gr_' + c, check,
    args: [files('test/cases/' + c + '.gr'),
           tlsfinfo_exe, '-gr', files('test/cases/' + c + '.tlsf')])
endforeach

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
# (INITIALLY & G REQUIRE & ASSUME) -> (PRESET & G ASSERT & GUARANTEE)
test('semantics_sections', check,
  args: [files('test/cases/sections.ltl'),
         tlsf2ltl_exe, files('test/cases/sections.tlsf')])

# --relax-semantics on a strict spec applies the strict->non-strict
# translation: (PRESET & G ASSERT) W !(INITIALLY & G REQUIRE), plus the
# liveness implication.
test('semantics_relax_strict', check,
  args: [files('test/cases/sections.strict.ltl'),
         tlsf2ltl_exe, '--relax-semantics',
         files('test/cases/sections_strict.tlsf')])

# Without the flag a strict spec emits the plain E -> S formula (same as the
# non-strict spec); --relax is idempotent on non-strict specs.
test('semantics_strict_default', check,
  args: [files('test/cases/sections.ltl'),
         tlsf2ltl_exe, files('test/cases/sections_strict.tlsf')])

# Mealy/Moore conversion when SEMANTICS and TARGET disagree.
test('semantics_moore_to_mealy', check,
  args: [files('test/cases/conv_moore_mealy.ltl'),
         tlsf2ltl_exe, files('test/cases/conv_moore_mealy.tlsf')])
