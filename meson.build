project(
  'tlsf-tools',
  'c',
  'cpp',
  version: run_command(
    'scripts/git-version.py',
    check: true,
  ).stdout().strip(),
  meson_version: '>= 1.7.0',
  license: 'MIT',
  default_options: [
    'warning_level=3',
    'werror=false',
    'b_ndebug=if-release',
    'cpp_std=c++20',
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
# matching compile-time path in src/lib/simd.h (via the predefined
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
  add_project_arguments(san_flags, language: ['c', 'cpp'])
  add_project_link_arguments(san_flags, language: ['c', 'cpp'])
endif

# ---------------------------------------------------------------------------
# Dependencies: flex and bison
# ---------------------------------------------------------------------------

flex  = find_program('flex',  required: true)
bison = find_program('bison', required: true)
yyjson_dep = dependency('yyjson', version: '>=0.12.0',
                        fallback: ['yyjson', 'yyjson_dep'])
git = find_program('git', required: false)
git_version = find_program('scripts/git-version.py')
bash = find_program('bash', required: false)
python3 = find_program('python3')
# OxiDD is a required part of libtlsf. All generated artifacts live in the
# build tree and are dependencies of every consumer, including source exports.
oxidd_dir = meson.current_source_dir() / 'external/oxidd'
oxidd_stamp_py = files('scripts/oxidd_stamp.py')
oxidd_inc = include_directories('.')
subdir('oxidd')
meson.add_dist_script(python3, files('scripts/dist_oxidd.py'))

# ---------------------------------------------------------------------------
# Sources
#
#   include/tlsf/   public API: every header there is installed
#   src/lib/        libtlsf and its private headers, plus tlsf-oxidd
#   src/tools/      one directory per command-line tool
#   test/           unit, api, cli, oracle suites and their fixtures
# ---------------------------------------------------------------------------

public_inc = include_directories('include')
subdir('include/tlsf')
subdir('src/lib')
subdir('src/tools')

# Declared here rather than in src/tools so every binary stays at build/<tool>.
exe = {}
foreach name, tool : tools
  exe += {name: executable(name, tool['sources'],
                           dependencies: tool['dependencies'], install: true)}
endforeach

subdir('examples')
subdir('test')
