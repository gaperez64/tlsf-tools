fake_ltlsynt = files('fake_ltlsynt.sh')
fake_automata_generator = files('fake_automata_generator.py')
# Kept beside cases/ so the corpus-wide oracles do not pick it up.
arbiter_simple = files('arbiter_simple.tlsf')

if research_tools and have_oxidd
  # tlsfsolve's own main against solvers that always fail, so the CLI's
  # failure reporting can be checked without a failing game.
  tlsfsolve_failure_exe = executable(
    'tlsfsolve-failure-stub',
    'tlsfsolve_failure_stub.c',
    objects: exe['tlsfsolve'].extract_all_objects(recursive: false),
    dependencies: tlsf_oxidd_dep,
  )
endif
