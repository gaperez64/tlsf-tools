decoder = static_library('fuzz-decode', 'decode.c')
replayer = static_library('fuzz-replay', 'replay.c')
dpa_checks = static_library('fuzz-dpa-checks', 'dpa_checks.c',
                            dependencies: tlsf_dep)

foreach target : ['roundtrip', 'alloc', 'dpa']
  if target == 'alloc' and host_machine.system() != 'linux'
    message('SKIP fuzz-alloc: requires GNU ld --wrap, like objective_alloc')
    continue
  endif
  extra_links = []
  if target == 'alloc'
    # Wrap the library arena entry points as well as heap/host allocations.
    foreach name : ['malloc', 'calloc', 'realloc', 'free', 'oxidd_host_calloc',
                     'arena_alloc_aligned', 'arena_alloc_array']
      extra_links += ['-Wl,--wrap=' + name]
    endforeach
  endif
  checks = target == 'roundtrip' ? [] : [dpa_checks]
  harness = static_library('fuzz-' + target + '-harness',
                           target + '.c', link_with: [decoder] + checks,
                           dependencies: tlsf_dep)
  replay = executable('fuzz-' + target + '-replay',
                      link_whole: [harness, replayer], link_args: extra_links,
                      dependencies: tlsf_dep)
  test('fuzz-' + target, replay, suite: 'unit',
       args: [meson.current_source_dir() / 'corpus' / target])
  if fuzz
    executable('fuzz-' + target, link_whole: harness, dependencies: tlsf_dep,
               link_args: extra_links + ['-fsanitize=fuzzer,address,undefined'])
  endif
endforeach
