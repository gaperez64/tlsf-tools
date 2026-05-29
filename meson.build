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

executable(
  'tlsf2ltl',
  sources: ['src/main_tlsf2ltl.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

executable(
  'tlsf2tlsf',
  sources: ['src/main_tlsf2tlsf.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)

executable(
  'tlsfinfo',
  sources: ['src/main_tlsfinfo.c', bison_out[1]],
  link_with: tlsf_lib,
  include_directories: inc,
  install: true,
)
