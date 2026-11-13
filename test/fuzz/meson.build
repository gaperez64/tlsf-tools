decoder = static_library('fuzz-decode', 'decode.c')
replayer = static_library('fuzz-replay', 'replay.c', c_args: ['-DFUZZ_REPLAY'])

foreach mode : fuzz ? ['replay', 'fuzzer'] : ['replay']
  check_args = mode == 'replay' ? ['-DFUZZ_REPLAY'] : []
  dpa_checks = static_library('fuzz-dpa-checks-' + mode, 'dpa_checks.c',
                              c_args: check_args, dependencies: tlsf_dep)
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
    harness = static_library('fuzz-' + target + '-harness-' + mode,
                             target + '.c', link_with: [decoder] + checks,
                             c_args: check_args, dependencies: tlsf_dep)
    if mode == 'replay'
      replay = executable('fuzz-' + target + '-replay',
                          link_whole: [harness, replayer], link_args: extra_links,
                          dependencies: tlsf_dep)
      test('fuzz-witness-' + target, replay, suite: 'unit',
           args: ['--witness', target.substring(0, 1).to_upper(),
                  meson.current_source_dir() / 'corpus' / target])
    else
      executable('fuzz-' + target, link_whole: harness, dependencies: tlsf_dep,
                 link_args: extra_links + ['-fsanitize=fuzzer,address,undefined'])
    endif
  endforeach
endforeach
