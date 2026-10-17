cargo = find_program('cargo')
cbindgen = find_program('cbindgen')
# Cargo tracks its Rust inputs, but Ninja must also know when to invoke it.
oxidd_inputs = run_command(python3, files('../scripts/oxidd_sources.py'),
                          oxidd_dir, check: true).stdout().strip().split('\n')
oxidd_build = custom_target(
  'oxidd-ffi',
  input: files(oxidd_inputs),
  output: ['liboxidd_ffi_c.a', 'capi.h', 'config.h', 'oxidd-build-stamp',
           'oxidd_build_stamp.h'],
  command: [python3, files('../scripts/build_oxidd.py'), oxidd_dir,
            meson.current_build_dir(), cargo, cbindgen],
  depend_files: [oxidd_stamp_py],
  install: true,
  install_dir: [get_option('libdir'), get_option('includedir') / 'oxidd',
                get_option('includedir') / 'oxidd', false, false],
)
# Verify even an otherwise up-to-date build before consumers can relink.
# This catches an archive changed outside Ninja without recompiling Rust.
oxidd_verified = custom_target(
  'oxidd-verified',
  input: [oxidd_build[0], oxidd_build[3]],
  output: 'oxidd_verified.h',
  command: [python3, oxidd_stamp_py, 'check', oxidd_dir,
            '@INPUT0@', '@INPUT1@', '@OUTPUT@'],
  build_always_stale: true,
)
oxidd_link_args = ['-lpthread', '-lm']
if host_machine.system() != 'darwin'
  oxidd_link_args += ['-ldl']
endif
oxidd_dep = declare_dependency(
  include_directories: oxidd_inc,
  sources: [oxidd_build[1], oxidd_build[2], oxidd_build[4], oxidd_verified],
  link_with: oxidd_build[0],
  link_args: oxidd_link_args,
)
