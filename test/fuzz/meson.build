foreach target : ['roundtrip']
  harness = static_library('fuzz-' + target + '-harness',
                           [target + '.c', 'decode.c'], dependencies: tlsf_dep)
  replay = executable('fuzz-' + target + '-replay', 'replay.c',
                      link_with: harness, dependencies: tlsf_dep)
  test('fuzz-' + target, replay, suite: 'unit',
       args: [meson.current_source_dir() / 'corpus' / target])
  if fuzz
    executable('fuzz-' + target, link_with: harness, dependencies: tlsf_dep,
               link_args: ['-fsanitize=fuzzer,address,undefined'])
  endif
endforeach
