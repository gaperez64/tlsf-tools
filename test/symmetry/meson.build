foreach name : ['symmetric', 'cyclic', 'asymmetric', 'mixed', 'edges']
  test('tlsfsym_' + name, python3, suite: 'unit',
    args: [files('../unit/check_symmetry.py'), exe['tlsfsym'],
           meson.project_source_root() / 'test/fixtures/symmetry', name])
endforeach
