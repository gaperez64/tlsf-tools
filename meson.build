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
native_gr1 = get_option('native_gr1').enabled()

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
# Optional: used by wrapper/benchmark tests that shell out to ltlsynt.
ltlsynt = find_program('ltlsynt', required: false)
spot_dep = dependency('libspot', required: false)
yyjson_dep = dependency('yyjson', version: '>=0.12.0',
                        fallback: ['yyjson', 'yyjson_dep'])
git = find_program('git', required: false)
git_version = find_program('scripts/git-version.py')
bash = find_program('bash', required: false)
python3 = find_program('python3', required: false)
spot_python = python3
spot_python_env = environment()
spot_python_found = false
if python3.found()
  spot_python_found = run_command(
    python3,
    '-c',
    'import spot',
    check: false,
  ).returncode() == 0
endif
# The param-lift monitor tools can fall back to the locally installed Spot
# bindings when the generic Python cannot import them.  Keep the selected
# interpreter and its environment together so a not-found fallback is never
# used merely because an earlier probe succeeded.
if not spot_python_found
  spot_python_fallback = find_program('python3.13', required: false)
  spot_python_fallback_env = environment()
  spot_python_fallback_env.set(
    'PYTHONPATH', '/usr/local/lib64/python3.13/site-packages')
  spot_python_fallback_env.set('LD_LIBRARY_PATH', '/usr/local/lib:/usr/local/lib64')
  if spot_python_fallback.found() and run_command(
      spot_python_fallback,
      '-c',
      'import spot',
      env: spot_python_fallback_env,
      check: false,
    ).returncode() == 0
    spot_python = spot_python_fallback
    spot_python_env = spot_python_fallback_env
    spot_python_found = true
  endif
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
oxidd_patch_info_path = join_paths(oxidd_dir, 'build', 'oxidd-gc-thread-retirement-info.txt')
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

oxidd_ready = fs.exists(oxidd_lib_path) and fs.exists(oxidd_capi_h) and fs.exists(oxidd_patch_info_path)
oxidd_patch_record = 'none'
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
  oxidd_verify = run_command(bash, oxidd_build_sh, '--verify', check: false)
  if oxidd_verify.returncode() != 0
    error('OxiDD patch verification failed: ' + oxidd_verify.stderr().strip())
  endif
  oxidd_patch_record = fs.read(oxidd_patch_info_path).strip()
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

if native_gr1 and not have_oxidd
  error('native_gr1 requires -Doxidd=enabled and the built OxiDD archive and headers')
endif
if native_gr1 and not spot_dep.found()
  error('native_gr1 requires libspot (set PKG_CONFIG_PATH if needed)')
endif
if have_oxidd
  # Static consumers of libtlsf also need OxiDD's archive and C API.
  install_subdir('external/oxidd/build/include/oxidd',
                 install_dir: get_option('includedir'))
  install_data(oxidd_lib_path, install_dir: get_option('libdir'))
endif

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
