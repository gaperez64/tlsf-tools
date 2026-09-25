# The command-line tools against golden outputs, exit statuses and schemas.

if python3.found()
  test('frontend_provenance', python3,
    args: [files('test_frontend_provenance.py'),
           '--tlsf2tlsf', exe['tlsf2tlsf'],
           '--tlsfinfo', exe['tlsfinfo'],
           '--tlsf2ltl', exe['tlsf2ltl']],
    timeout: 60,
  )
endif


# ---------------------------------------------------------------------------
# Integration / regression tests (golden-output diffs)
#
# Self-contained: a representative set of SYNTCOMP TLSF specs lives under
# test/fixtures/cases/ with their expected tool output.  No external tools (syfco,
# spot) are needed, so these run anywhere — including CI.
# ---------------------------------------------------------------------------

check = files('check.sh')
xfail = files('expect_fail.sh')
check_fail_stderr = files('check_fail_stderr.sh')
check_status = files('check_status.sh')
check_solve_wrapper = files('check_solve_wrapper.sh')
check_output_dir = files('check_output_dir.sh')
check_output_dir_fail = files('check_output_dir_fail.sh')
check_version = files('check_version.sh')

test('version_tlsf2ltl', check_version, args: ['tlsf2ltl', exe['tlsf2ltl']])
test('version_tlsf2tlsf', check_version, args: ['tlsf2tlsf', exe['tlsf2tlsf']])
test('version_tlsfinfo', check_version, args: ['tlsfinfo', exe['tlsfinfo']])
test('version_tlsfnorm', check_version, args: ['tlsfnorm', exe['tlsfnorm']])
test('version_mealy2moore', check_version,
  args: ['mealy2moore', exe['mealy2moore']])
if research_tools
  test('version_tlsftemplates', check_version,
    args: ['tlsftemplates', exe['tlsftemplates']])
  test('version_tlsfbenchgraph', check_version,
    args: ['tlsfbenchgraph', exe['tlsfbenchgraph']])
  test('tlsfbenchgraph_schema', files('check_benchgraph_schema.sh'),
    args: [exe['tlsfbenchgraph'],
           files(cases / 'normalization_match.tlsf')])
  test('version_tlsfresidual', check_version,
    args: ['tlsfresidual', exe['tlsfresidual']])
  if python3.found()
    test('automata_study_bundle', files('check_automata_study.sh'),
      args: [files(scripts / 'automata_study.py'), exe['tlsfnorm'],
             exe['tlsf2ltl'], exe['tlsfinfo'], exe['tlsfbenchgraph'],
             fake_automata_generator,
             files(cases / 'normalization_match.tlsf')])
    test('automata_study_evaluator', python3,
      args: [files('check_evaluate_automata_study.py'),
             files(scripts / 'evaluate_automata_study.py')])
  endif
  if have_oxidd
    test('version_tlsfcompose', check_version,
      args: ['tlsfcompose', exe['tlsfcompose']])
    test('version_tlsfsolve', check_version,
      args: ['tlsfsolve', exe['tlsfsolve']])
    test('version_tlsfcertcheck', check_version,
      args: ['tlsfcertcheck', exe['tlsfcertcheck']])
  endif
endif

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
      files(cases / c + '.ltl'),
      exe['tlsf2ltl'],
      files(cases / c + '.tlsf'),
    ])
endforeach

# Targeted feature tests.
foreach c : ['simple', 'latch', 'const']
  test('mealy2moore_' + c, check,
    args: [files(cases / 'mealy2moore_' + c + '.out.aag'),
           exe['mealy2moore'],
           files(cases / 'mealy2moore_' + c + '.in.aag')])
endforeach

test('ltl_full_parens', check,
  args: [files(cases / 'Patterns_Uright_uright06.full.ltl'),
         exe['tlsf2ltl'], '--parenthesize',
         files(cases / 'Patterns_Uright_uright06.tlsf')])

# Output dialects (--format) and formula transformations.
test('ltl_format_ltl', check,
  args: [files(cases / 'operators.ltlfmt.ltl'),
         exe['tlsf2ltl'], '--format', 'ltl',
         files(cases / 'operators.tlsf')])

test('ltl_format_latex', check,
  args: [files(cases / 'operators.latex.ltl'),
         exe['tlsf2ltl'], '--format', 'latex',
         files(cases / 'operators.tlsf')])

test('ltl_strong_simplify', check,
  args: [files(cases / 'operators.s1.ltl'),
         exe['tlsf2ltl'], '--strong-simplify',
         files(cases / 'operators.tlsf')])

test('ltl_no_derived', check,
  args: [files(cases / 'operators.nd.ltl'),
         exe['tlsf2ltl'], '--no-derived',
         files(cases / 'operators.tlsf')])

test('ltl_no_release', check,
  args: [files(cases / 'operators.nr.ltl'),
         exe['tlsf2ltl'], '--no-release',
         files(cases / 'operators.tlsf')])

test('ltl_no_strong_release', check,
  args: [files(cases / 'operators.nsr.ltl'),
         exe['tlsf2ltl'], '--no-strong-release',
         files(cases / 'operators.tlsf')])

# Environment fairness: scalar + parameterized bus inputs, preserved existing
# assumptions, rewrites and safety/liveness guarantee selection.
test('ltl_fair_environment', check,
  args: [files(cases / 'fair_environment.ltl'), exe['tlsf2ltl'],
         '--fair-environment', files(cases / 'fair_environment.tlsf')])
test('ltl_fair_environment_no_finally', check,
  args: [files(cases / 'fair_environment.no_finally.ltl'), exe['tlsf2ltl'],
         '--fair-environment', '--no-finally',
         files(cases / 'fair_environment.tlsf')])
test('ltl_fair_environment_safety', check,
  args: [files(cases / 'fair_environment.safety.ltl'), exe['tlsf2ltl'],
         '--fair-environment', '--safety',
         files(cases / 'fair_environment.tlsf')])
test('ltl_fair_environment_liveness', check,
  args: [files(cases / 'fair_environment.liveness.ltl'), exe['tlsf2ltl'],
         '--fair-environment', '--liveness',
         files(cases / 'fair_environment.tlsf')])
test('tlsf_fair_environment', check,
  args: [files(cases / 'fair_environment.reemit.tlsf'), exe['tlsf2tlsf'],
         '--fair-environment', files(cases / 'fair_environment.tlsf')])
test('tlsf_fair_environment_basic', check,
  args: [files(cases / 'fair_environment.basic.tlsf'), exe['tlsf2tlsf'],
         '--fair-environment', '--basic',
         files(cases / 'fair_environment.tlsf')])
test('ltl_fair_environment_no_inputs', check,
  args: [files(cases / 'fair_environment_no_inputs.ltl'), exe['tlsf2ltl'],
         '--fair-environment',
         files(cases / 'fair_environment_no_inputs.tlsf')])
test('tlsf_fair_environment_no_inputs', check,
  args: [files(cases / 'fair_environment_no_inputs.reemit.tlsf'),
         exe['tlsf2tlsf'], '--fair-environment',
         files(cases / 'fair_environment_no_inputs.tlsf')])

foreach tool : [['tlsf2ltl', exe['tlsf2ltl'],
                 files(cases / 'fair_environment_ltl.stderr')],
                ['tlsf2tlsf', exe['tlsf2tlsf'],
                 files(cases / 'fair_environment_tlsf.stderr')]]
  test(tool[0] + '_fair_environment_finite', check_status,
    args: ['1', files(cases / 'empty'), tool[2], tool[1],
           '--fair-environment', files(cases / 'finite_wm.tlsf')])
  test(tool[0] + '_fair_environment_finite_override', check_status,
    args: ['1', files(cases / 'empty'), tool[2], tool[1],
           '--fair-environment', '--overwrite-semantics', 'Finite,Mealy',
           files(cases / 'fair_environment.tlsf')])
endforeach

# Finite (ltlxba-fin): W/M auto-eliminated, weak X vs strong X[!] preserved.
test('ltl_finite_wm', check,
  args: [files(cases / 'finite_wm.ltl'),
         exe['tlsf2ltl'], files(cases / 'finite_wm.tlsf')])

# Bounded temporal operators G[i:j] / F[i:j].
test('ltl_ranges', check,
  args: [files(cases / 'ranges.ltl'),
         exe['tlsf2ltl'], files(cases / 'ranges.tlsf')])

test('tlsf_ranges_reemit', check,
  args: [files(cases / 'ranges.reemit.tlsf'),
         exe['tlsf2tlsf'], files(cases / 'ranges.tlsf')])

# 'M' (strong-release keyword) reused as a parameter name and atom.
test('ltl_ident_m', check,
  args: [files(cases / 'ident_m.ltl'),
         exe['tlsf2ltl'], files(cases / 'ident_m.tlsf')])

foreach c : ['ident_m_function', 'ident_m_signal', 'ident_m_formal',
             'ident_m_enum', 'ident_m_quantifier']
  test('ltl_' + c, check,
    args: [files(cases / c + '.ltl'),
           exe['tlsf2ltl'], files(cases / c + '.tlsf')])
endforeach

test('err_infix_m_v12', check_fail_stderr,
  args: [files(cases / 'bad_infix_m.stderr'), exe['tlsf2ltl'],
         files(cases / 'bad_infix_m.tlsf')])

test('ltl_precedence_v12', check,
  args: [files(cases / 'precedence_v12.ltl'), exe['tlsf2ltl'],
         '--parenthesize', files(cases / 'precedence_v12.tlsf')])

test('ltl_sets_v12', check,
  args: [files(cases / 'sets_v12.ltl'), exe['tlsf2ltl'],
         files(cases / 'sets_v12.tlsf')])
test('tlsf_sets_v12_reemit', check,
  args: [files(cases / 'sets_v12.reemit.tlsf'), exe['tlsf2tlsf'],
         files(cases / 'sets_v12.tlsf')])
test('ltl_aliases_v12', check,
  args: [files(cases / 'aliases_v12.ltl'), exe['tlsf2ltl'],
         files(cases / 'aliases_v12.tlsf')])
test('ltl_strong_bounds_v12', check,
  args: [files(cases / 'strong_bounds_v12.ltl'), exe['tlsf2ltl'],
         files(cases / 'strong_bounds_v12.tlsf')])
test('ltl_pattern_v12', check,
  args: [files(cases / 'pattern_v12.ltl'), exe['tlsf2ltl'],
         files(cases / 'pattern_v12.tlsf')])
test('err_pattern_conflict_v12', check_fail_stderr,
  args: [files(cases / 'pattern_conflict_v12.stderr'), exe['tlsf2ltl'],
         files(cases / 'pattern_conflict_v12.tlsf')])

test('ltl_nnf_m_v12', check,
  args: [files(cases / 'nnf_m_v12.nnf.ltl'), exe['tlsf2ltl'], '--nnf',
         files(cases / 'nnf_m_v12.tlsf')])
test('ltl_nnf_m_lowered_v12', check,
  args: [files(cases / 'nnf_m_v12.nsr.ltl'), exe['tlsf2ltl'], '--nnf',
         '--no-strong-release', files(cases / 'nnf_m_v12.tlsf')])
test('tlsf_nnf_m_v12', check,
  args: [files(cases / 'nnf_m_v12.norm.tlsf'), exe['tlsfnorm'],
         '--passes', 'nnf', files(cases / 'nnf_m_v12.tlsf')])
test('tlsf_nnf_m_roundtrip_v12', files('check_roundtrip.sh'),
  args: [exe['tlsfnorm'], exe['tlsf2ltl'],
         files(cases / 'nnf_m_v12.tlsf')])

# enum definitions: typed-bus declaration, bus == LABEL bit match, and the
# implicit validity invariant.
test('ltl_enum', check,
  args: [files(cases / 'enum_demo.ltl'),
         exe['tlsf2ltl'], files(cases / 'enum_demo.tlsf')])
test('ltl_enum_wildcards_strict', check,
  args: [files(cases / 'enum_wildcards_strict.ltl'),
         exe['tlsf2ltl'], files(cases / 'enum_wildcards_strict.tlsf')])
test('err_enum_width', xfail,
  args: [exe['tlsf2ltl'], files(cases / 'err_enum_width.tlsf')])

check_wl = files('check_wl.sh')   # normalizes embedded paths to basenames
check_contains = files('check_contains.sh')  # asserts output matches a regex

test('tlsf_enum_basic', check,
  args: [files(cases / 'enum_demo.basic.tlsf'),
         exe['tlsf2tlsf'], files(cases / 'enum_demo.tlsf')])

if research_tools
# The obligation census: a stable schema, and the counts a two-client arbiter
# must produce.
test('obligation_census', files('check_obligation_census.sh'),
  args: [exe['tlsftemplates'], files(cases / 'arbiter1formula.nnfbool.tlsf')])

# tlsftemplates (M5): certify CSNF for template blocks + soundness declines.
test('tmpl_definition', check_wl,
  args: [files(cases / 'def_demo.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'def_demo.tlsf')])
test('tmpl_round_robin', check_wl,
  args: [files(cases / 'roundrobin2.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'roundrobin2.tlsf')])
test('tmpl_guarded_next', check_wl,
  args: [files(cases / 'gnext_one_sided.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'gnext_one_sided.tlsf')])
test('tmpl_set_reset', check_wl,
  args: [files(cases / 'gnext_demo.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'gnext_demo.tlsf')])
test('tmpl_set_reset_declined', check_wl,
  args: [files(cases / 'gnext_unsafe.csnf'), exe['tlsftemplates'],
         '--certify', '--format', 'csnf',
         files(cases / 'gnext_unsafe.tlsf')])
test('tmpl_set_reset_strong_finite_declined', check_wl,
  args: [files(cases / 'gnext_strong_fin.csnf'), exe['tlsftemplates'],
         '--certify', '--format', 'csnf',
         files(cases / 'gnext_strong_fin.tlsf')])
test('tmpl_toggle', check_wl,
  args: [files(cases / 'toggle_demo.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'toggle_demo.tlsf')])
test('tmpl_toggle_strong_finite_declined', check_wl,
  args: [files(cases / 'toggle_strong_fin.csnf'), exe['tlsftemplates'],
         '--certify', '--format', 'csnf',
         files(cases / 'toggle_strong_fin.tlsf')])
test('tmpl_fixed_delay', check_wl,
  args: [files(cases / 'fdelay_demo.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'fdelay_demo.tlsf')])
test('tmpl_fixed_delay_declined', check_wl,
  args: [files(cases / 'fdelay_blocked.csnf'), exe['tlsftemplates'],
         '--certify', '--format', 'csnf',
         files(cases / 'fdelay_blocked.tlsf')])
test('tmpl_fixed_delay_strong_finite_declined', check_wl,
  args: [files(cases / 'fdelay_strong_fin.csnf'), exe['tlsftemplates'],
         '--certify', '--format', 'csnf',
         files(cases / 'fdelay_strong_fin.tlsf')])
test('tmpl_delayed_def_strong_finite_declined', check_wl,
  args: [files(cases / 'ddef_strong_fin.csnf'), exe['tlsftemplates'],
         '--certify', '--format', 'csnf',
         files(cases / 'ddef_strong_fin.tlsf')])
# Template-coverage expansion: free-liveness family, reaction, delayed-def,
# fair arbiter — each with a solved and a declined (non-free / non-exclusive) case.
foreach name : ['reach_free', 'reach_blocked', 'persist_free', 'reaction_ok',
                'reaction_multi', 'reaction_unsafe', 'ddef_demo',
                'response_free', 'response_blocked', 'inv_const',
                'inv_skolem', 'inv_multi', 'inv_decline', 'inv_valid',
                'dbuchi_switch', 'dbuchi_switch_finite']
  test('tmpl_' + name, check_wl,
    args: [files(cases / name + '.csnf'), exe['tlsftemplates'],
           '--certify', '--solve', '--format', 'csnf',
           files(cases / name + '.tlsf')])
endforeach
test('tmpl_arbiter', check_wl,
  args: [files(cases / 'arbiter2.csnf'), exe['tlsftemplates'],
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'arbiter2.tlsf')])
# CLI option coverage: --list-templates, --template/--templates filter, --param.
test('tmpl_list_templates', check,
  args: [files(cases / 'tmpl_list_templates.txt'), exe['tlsftemplates'],
         '--list-templates'])
test('tmpl_template_filter', check_wl,
  args: [files(cases / 'reaction_ok.csnf'), exe['tlsftemplates'],
         '--template', 'reaction', '--certify', '--solve', '--format', 'csnf',
         files(cases / 'reaction_ok.tlsf')])
test('tmpl_templates_filter', check_wl,
  args: [files(cases / 'reaction_ok.csnf'), exe['tlsftemplates'],
         '--templates', 'reaction', '--certify', '--solve', '--format', 'csnf',
         files(cases / 'reaction_ok.tlsf')])
test('tmpl_param', check_wl,
  args: [files(cases / 'tmpl_param_demo.csnf'), exe['tlsftemplates'],
         '--param', 'n=5', '--param', 'k=2',
         '--certify', '--solve', '--format', 'csnf',
         files(cases / 'param_demo.tlsf')])
# match-normalize (PR3/PR4): equivalence-preserving recognition normalization
# lifts a guarded-next to solved and a mutex to certified.
test('tmpl_match_normalize', check,
  args: [files(cases / 'normalization_patterns.tmpl_matchsafe.txt'),
         exe['tlsftemplates'], '--certify', '--solve', '--format', 'text',
         '--match-normalize', 'match-safe:1',
         files(cases / 'normalization_patterns.tlsf')])
# Composition soundness: tlsftemplates --check (whole-spec verdict) and
# tlsfresidual (leftover LTL after the accepted blocks).
foreach name : ['reaction_ok', 'compose_conflict', 'compose_cycle',
                'compose_partial', 'subst_reduce', 'server_merge',
                'arbiter_nomutex']
  test('check_' + name, check_wl,
    args: [files(cases / name + '.check'), exe['tlsftemplates'],
           '--check', '--format', 'csnf', files(cases / name + '.tlsf')])
endforeach
endif
if research_tools
foreach name : ['response_free', 'reach_blocked', 'compose_conflict',
                'compose_cycle', 'compose_partial', 'subst_reduce',
                'server_merge', 'arbiter_nomutex', 'cluster_split',
                'cluster_assume', 'inv_skolem', 'inv_multi', 'inv_decline']
  test('residual_' + name, check,
    args: [files(cases / name + '.residual'), exe['tlsfresidual'],
           files(cases / name + '.tlsf')])
endforeach
test('residual_single', check,
  args: [files(cases / 'cluster_split.single'), exe['tlsfresidual'],
         '--single', files(cases / 'cluster_split.tlsf')])
# CLI option coverage: --format ltl/ltlxba, --split, --param.
test('residual_ltl_format', check,
  args: [files(cases / 'residual_ltl_format.residual'), exe['tlsfresidual'],
         '--format', 'ltl', files(cases / 'cluster_split.tlsf')])
test('residual_ltlxba_format', check,
  args: [files(cases / 'cluster_split.residual'), exe['tlsfresidual'],
         '--format', 'ltlxba', files(cases / 'cluster_split.tlsf')])
test('residual_split', check,
  args: [files(cases / 'cluster_split.residual'), exe['tlsfresidual'],
         '--split', files(cases / 'cluster_split.tlsf')])
test('residual_lowercase', check,
  args: [files(cases / 'upper_atoms.lower.residual'), exe['tlsfresidual'],
         '--split', '--lowercase', files(cases / 'upper_atoms.tlsf')])
test('residual_param', check,
  args: [files(cases / 'residual_param_demo.residual'), exe['tlsfresidual'],
         '--param', 'n=5', '--param', 'k=2',
         files(cases / 'param_demo.tlsf')])
if have_oxidd
  foreach name : ['compose_demo', 'cluster_split', 'cluster_prune', 'input_gua_skip']
    test('compose_' + name, check,
      args: [files(cases / name + '.compose'), exe['tlsfcompose'],
             files(cases / name + '.tlsf')])
  endforeach
  test('compose_lowercase', check,
    args: [files(cases / 'upper_atoms.lower.compose'), exe['tlsfcompose'],
           '--split', '--lowercase', files(cases / 'upper_atoms.tlsf')])
  test('compose_merge_mode', check,
    args: [files(cases / 'compose_demo.merged.aag'), exe['tlsfcompose'],
           '--merge', files(cases / 'compose_demo.merged.aag')])
  test('solve_wrapper_oxidd_presolve', check_solve_wrapper,
    args: [files(cases / 'solve_wrapper_fake.aag'),
           files(scripts / 'solve.sh'), exe['tlsfcompose'],
           fake_ltlsynt,
           files(cases / 'compose_demo.tlsf')])
  test('solve_wrapper_fake_ltlsynt', check_solve_wrapper,
    args: [files(cases / 'solve_wrapper_fake_liveness.aag'),
           files(scripts / 'solve.sh'), exe['tlsfcompose'],
           fake_ltlsynt,
           files(cases / 'liveness_nested.tlsf')])
  test('compose_output_dir_under_real_wr', check_output_dir,
    args: [files(cases / 'wr_under_real.output_dir'),
           exe['tlsfcompose'], '--split', files(cases / 'wr_under_real.tlsf')])
  test('compose_output_dir_over_unreal_wr', check_output_dir_fail,
    args: ['trusted one-sided OxiDD verdict', exe['tlsfcompose'], '--split',
           files(cases / 'wr_gated_collapse.tlsf')])
  test('compose_aiger_unclassified_atom', check,
    args: [files(cases / 'aiger_unclassified_atom.compose'), exe['tlsfcompose'],
           files(cases / 'aiger_unclassified_atom.tlsf')])
  test('compose_route_stats_gr1', check,
    args: [files(cases / 'gr1_spec.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'gr1_spec.tlsf')])
  test('compose_route_stats_bounded', check,
    args: [files(cases / 'compose_demo.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', '--experimental-bounded', '4',
           files(cases / 'compose_demo.tlsf')])
  test('compose_route_stats_response_monitor', check,
    args: [files(cases / 'compose_demo.response_monitor.route_stats'),
           exe['tlsfcompose'], '--split', '--route-stats',
           files(cases / 'compose_demo.tlsf')])
  test('compose_route_stats_initial_x_assume', check,
    args: [files(cases / 'initial_x_assume.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'initial_x_assume.tlsf')])
  test('compose_route_stats_delayed_global', check,
    args: [files(cases / 'delayed_global.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'delayed_global.tlsf')])
  test('compose_route_stats_gr1_recurrence', check,
    args: [files(cases / 'gr1_recurrence.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'gr1_recurrence.tlsf')])
  test('compose_route_stats_strict_safety', check,
    args: [files(cases / 'strict_safety.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'strict_safety.tlsf')])
  test('compose_route_stats_wr_response', check,
    args: [files(cases / 'wr_response.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'wr_response.tlsf')])
  test('compose_route_stats_reaction_ok', check,
    args: [files(cases / 'reaction_ok.route_stats'), exe['tlsfcompose'],
           '--split', '--route-stats', files(cases / 'reaction_ok.tlsf')])
  test('compose_route_stats_response_same_cycle', check,
    args: [files(cases / 'response_same_cycle.route_stats'),
           exe['tlsfcompose'], '--split', '--route-stats',
           files(cases / 'response_same_cycle.tlsf')])
  test('compose_route_stats_eventual_output', check,
    args: [files(cases / 'eventual_output.route_stats'),
           exe['tlsfcompose'], '--split', '--route-stats',
           files(cases / 'eventual_output.tlsf')])
  test('compose_route_stats_until_input_target', check,
    args: [files(cases / 'until_input_target.route_stats'),
           exe['tlsfcompose'], '--split', '--route-stats',
           files(cases / 'until_input_target.tlsf')])
  test('compose_route_stats_policy_off', check,
    args: [files(cases / 'gr1_spec.policy_off.route_stats'),
           exe['tlsfcompose'], '--split', '--route-stats',
           '--preprocess-policy', 'off', files(cases / 'gr1_spec.tlsf')])
  test('compose_route_stats_policy_profitable_skip', check,
    args: [files(cases / 'policy_profitable_skip.route_stats'),
           exe['tlsfcompose'], '--split', '--route-stats',
           '--preprocess-policy', 'profitable',
           files(cases / 'policy_profitable_skip.tlsf')])
  foreach name : ['liveness_eventual', 'liveness_until', 'liveness_mixed',
                  'liveness_nested']
    test('compose_route_stats_' + name, check,
      args: [files(cases / name + '.route_stats'), exe['tlsfcompose'],
             '--split', '--route-stats',
             files(cases / name + '.tlsf')])
  endforeach
  # TRUST_OVER boolean-fragment UNREAL pre-check: an input-only G guarantee is
  # caught before plan emission.
  test('precheck_input_only_unreal', check_contains,
    args: ['UNREALIZABLE \\(boolean-fragment pre-check', exe['tlsfcompose'],
           files(cases / 'precheck_input_only.tlsf')])
  test('precheck_route_stats', check_contains,
    args: ['unreal_precheck=1', exe['tlsfcompose'], '--split', '--route-stats',
           files(cases / 'precheck_input_only.tlsf')])
  # Control: the boolean-G guarantee mentions an output that can satisfy it, so
  # the pre-check stays silent and normal plan emission succeeds.
  test('precheck_outputs_rescue_real', exe['tlsfcompose'],
    args: [files(cases / 'precheck_outputs_rescue.tlsf')])
  # Dual TRUST_UNDER early-REAL via the --realizability oracle (self-contained,
  # no solver): outputs satisfy the boolean guarantees -> REALIZABLE; an
  # input-only contradiction -> UNREALIZABLE (always-on UNREAL check); a
  # temporal guarantee -> UNKNOWN (oracle inconclusive).
  test('precheck_real_oracle_real', check_contains,
    args: ['REALIZABLE \\(boolean-fragment pre-check', exe['tlsfcompose'],
           '--split', '--realizability',
           files(cases / 'precheck_outputs_rescue.tlsf')])
  test('precheck_real_oracle_unreal', check_contains,
    args: ['UNREALIZABLE \\(boolean-fragment pre-check', exe['tlsfcompose'],
           '--split', '--realizability',
           files(cases / 'precheck_input_only.tlsf')])
  test('precheck_real_oracle_unknown', check_contains,
    args: ['realizability UNKNOWN', exe['tlsfcompose'],
           '--split', '--realizability',
           files(cases / 'precheck_real_unknown.tlsf')])
endif
endif
if research_tools
# tlsfbenchgraph: per-spec corpus metrics TSV (file column is a basename, so the
# golden is path-independent).
test('benchgraph_tsv', check,
  args: [files(cases / 'bench.tsv'), exe['tlsfbenchgraph'],
         '--summary', files(cases / 'arbiter1formula.tlsf'),
         files(cases / 'arbiter2.tlsf'),
         files(cases / 'cluster_split.tlsf'),
         files(cases / 'def_demo.tlsf'),
         files(cases / 'roundrobin2.tlsf')])
if python3.found()
  test('bounded_corpus_harness', check,
    args: [files(cases / 'bounded_corpus.tsv'),
           files(scripts / 'bounded_corpus.py'), '--benchgraph', exe['tlsfbenchgraph'],
           '--mem-mb', '512', '--timeout', '5', '--quiet',
           files(cases / 'def_demo.tlsf'),
           files(cases / 'reaction_ok.tlsf')])
  # norm_sweep (PR11): match-safe:1 is soundness-eligible and lifts a block to
  # solved on the crafted pattern spec.
  test('norm_sweep_match_safe', check_contains,
    args: ['match-safe:1[[:space:]]+1[[:space:]]+0[[:space:]]+2[[:space:]]+1[[:space:]]+1',
           files(scripts / 'norm_sweep.py'),
           '--tlsfbenchgraph', exe['tlsfbenchgraph'],
           files(cases / 'normalization_patterns.tlsf'),
           '--schedules', 'off', 'match-safe:1'])
endif
endif
if research_tools and have_oxidd
  test('gr1_fairness_alternating_unreal', check_status,
    args: ['1', files(cases / 'empty'),
           files(cases / 'solve_unreal.stderr'), exe['tlsfsolve'],
           '--game-profile=gr1',
           files(cases / 'gr1_fairness_alternating.aag')])
  test('tlsfsolve_help_defaults', files('check_tlsfsolve_help.sh'),
    args: [exe['tlsfsolve']])
  if python3.found()
    test('tlsfsolve_measurement_runner', python3,
      args: [files('check_measure_tlsfsolve_memory.py')])
    test('oxidd_cone_analysis', python3,
      args: [files('check_oxidd_cone.py')])
    test('oxidd_diagnostic_runner', python3,
      args: [files('check_diagnose.py')])
    corpus = get_option('issue24_corpus')
    if corpus != ''
      foreach i : range(5)
        test('issue24_correctness_' + i.to_string(), python3,
          args: [files('check_issue24.py'), exe['tlsfsolve'], corpus, i.to_string()],
          suite: 'issue24-correctness', is_parallel: false, timeout: 130)
        test('issue24_memory_' + i.to_string(), python3,
          args: [files('check_issue24.py'), exe['tlsfsolve'], corpus, i.to_string(),
                 '--memory-out', join_paths(meson.project_build_root(),
                                           'issue24-memory-' + i.to_string() + '.json')],
          suite: 'issue24-memory', is_parallel: false, timeout: 130)
      endforeach
    endif
  endif
  # tlsfsolve: exact status, stdout and stderr for win, loss and solver failure.
  test('tlsfsolve_real', check_status,
    args: ['0', files(cases / 'solve_real.out.aag'),
           files(cases / 'empty'), exe['tlsfsolve'],
           files(cases / 'solve_real.aag')])
  test('tlsfsolve_legacy_unnamed_output', check_status,
    args: ['0', files(cases / 'solve_real.out.aag'),
           files(cases / 'empty'), exe['tlsfsolve'],
           files(cases / 'solve_real_unnamed_output.aag')])
  test('tlsfsolve_unreal', check_status,
    args: ['1', files(cases / 'empty'),
           files(cases / 'solve_unreal.stderr'), exe['tlsfsolve'],
           files(cases / 'solve_unreal.aag')])
  test('tlsfsolve_multi_bad_explicit', check_status,
    args: ['1', files(cases / 'empty'),
           files(cases / 'solve_unreal.stderr'), exe['tlsfsolve'],
           '--game-profile=multi-safety',
           files(cases / 'solve_multi_bad_unreal.aag')])
  test('tlsfsolve_multi_bad_auto_refuses', check_contains,
    args: ['cannot infer synthesis game profile.*multi-safety', exe['tlsfsolve'],
           files(cases / 'solve_multi_bad_unreal.aag')])
  test('tlsfsolve_gr1_fair1_unreal', check_status,
    args: ['1', files(cases / 'empty'),
           files(cases / 'solve_unreal.stderr'), exe['tlsfsolve'],
           files(cases / 'gr1_fair1.aag')])
  test('tlsfsolve_gr1_fair2_unreal', check_status,
    args: ['1', files(cases / 'empty'),
           files(cases / 'solve_unreal.stderr'), exe['tlsfsolve'],
           files(cases / 'gr1_fair2.aag')])
  test('tlsfsolve_gr1_input_fairness_unreal', check_status,
    args: ['1', files(cases / 'empty'),
           files(cases / 'solve_unreal.stderr'), exe['tlsfsolve'],
           files(cases / 'gr1_input_fairness.aag')])
  test('tlsfsolve_failure', check_status,
    args: ['2', files(cases / 'empty'),
           files(cases / 'solve_failure.stderr'), tlsfsolve_failure_exe,
           files(cases / 'solve_real.aag')])
endif

# tlsfnorm is stable preprocessing functionality.
test('norm_split', check,
  args: [files(cases / 'arbiter1formula.norm.tlsf'),
         exe['tlsfnorm'], '--passes', 'split',
         files(cases / 'arbiter1formula.tlsf')])
test('norm_nnf_boolean', check,
  args: [files(cases / 'arbiter1formula.nnfbool.tlsf'),
         exe['tlsfnorm'], '--passes', 'nnf,boolean',
         files(cases / 'arbiter1formula.tlsf')])
test('norm_trace', check,
  args: [files(cases / 'arbiter1formula.trace.txt'),
         exe['tlsfnorm'], '--passes', 'split', '--format', 'trace',
         files(cases / 'arbiter1formula.tlsf')])
test('norm_param', check,
  args: [files(cases / 'mutual_exclusion.norm3.tlsf'),
         exe['tlsfnorm'], '--passes', 'split', '--param', 'n=3',
         files(cases / 'mutual_exclusion.tlsf')])
# Normalization API (PR2): bool-canon sorts/dedups boolean operands; the
# match-safe profile re-emits valid, equivalent TLSF.
test('norm_match_safe', check,
  args: [files(cases / 'normalization_match.matchsafe.tlsf'),
         exe['tlsfnorm'], '--passes', 'match-safe:1',
         files(cases / 'normalization_match.tlsf')])
# match-safe pattern rules (PR6): or-to-impl exposes guarded-next, mutex-demorgan
# exposes mutex, equiv-output-side canonicalises the definition orientation.
test('norm_match_patterns', check,
  args: [files(cases / 'normalization_patterns.matchsafe.tlsf'),
         exe['tlsfnorm'], '--passes', 'match-safe:1',
         files(cases / 'normalization_patterns.tlsf')])
# route-safe (PR7): NNF + push G/X inward exposes independent safety invariants.
test('norm_route_safe', check,
  args: [files(cases / 'normalization_route.routesafe.tlsf'),
         exe['tlsfnorm'], '--passes', 'route-safe:1',
         files(cases / 'normalization_route.tlsf')])
# Sickert Stage 2 (PR9): lift a GF/FG limit node out of its temporal context.
test('norm_sickert2', check,
  args: [files(cases / 'normalization_sickert2.s2.tlsf'),
         exe['tlsfnorm'], '--passes', 'sickert-stage2:2', '--norm-max-growth',
         '400', files(cases / 'normalization_sickert2.tlsf')])
# Sickert Stage 3 (PR10): W inside GF -> U inside GF (+ FG-tail disjunct).
test('norm_sickert3', check,
  args: [files(cases / 'normalization_sickert3.s3.tlsf'),
         exe['tlsfnorm'], '--passes', 'sickert-stage3:1', '--norm-max-growth',
         '800', files(cases / 'normalization_sickert3.tlsf')])
# Soundness gate (Spot-verified; auto-skips when ltlfilt is absent, e.g. in CI):
# each schedule must preserve the spec's LTL meaning.
check_norm_equiv = files(scripts / 'check_norm_equiv.sh')
# (check_contains is defined near the top of the test section)
foreach case : [
    ['match-safe:1', 'normalization_patterns.tlsf'],
    ['route-safe:1', 'normalization_route.tlsf'],
    ['sickert-stage2:2', 'normalization_sickert2.tlsf'],
    ['sickert-stage3:1', 'normalization_sickert3.tlsf'],
    ['sickert-bounded', 'normalization_sickert3.tlsf'],
  ]
  test('norm_equiv_' + case[0].underscorify() + '_' + case[1].underscorify(),
    check_norm_equiv,
    args: [exe['tlsfnorm'], exe['tlsf2ltl'], case[0],
           files(cases / case[1])])
endforeach
# Sickert passes are infinite-word-only: they must be rejected on Finite specs.
test('norm_finite_rejects_sickert', xfail,
  args: [exe['tlsfnorm'], '--passes', 'sickert-stage2:1',
         files(cases / 'Patterns_Uright_uright06.tlsf')])
# Pre-expansion passes (PR5).  The expanded output is unchanged (expand() also
# performs these simplifications); the value is the recorded pre-pass firing,
# so these assert the stats line rather than a byte-identical re-emission.
test('norm_pre_indexed_x', check_contains,
  args: ['pre-xn-flatten: fired=[1-9]', exe['tlsfnorm'], '--pre-passes',
         'pre-indexed-x', '--norm-stats',
         files(cases / 'normalization_xn.tlsf')])
test('norm_pre_bounded_bool', check_contains,
  args: ['pre-bounded-empty: fired=[1-9]', exe['tlsfnorm'], '--pre-passes',
         'pre-bounded-bool', '--norm-stats',
         files(cases / 'normalization_bounded_bool.tlsf')])
test('norm_pre_spine_split', check_contains,
  args: ['pre-spine-split: fired=[1-9]', exe['tlsfnorm'], '--pre-passes',
         'pre-spine-split', '--norm-stats',
         files(cases / 'normalization_pre_split.tlsf')])
# Cross-check: a pre-normalized spec expands to the same TLSF as the original
# (expand(original) == expand(pre_normalize(original))).
test('norm_pre_indexed_x_equiv', check,
  args: [files(cases / 'normalization_xn.split.tlsf'), exe['tlsfnorm'],
         '--pre-passes', 'pre-indexed-x', '--passes', 'split',
         files(cases / 'normalization_xn.tlsf')])

# Constant folding (--weak-simplify): non-collapsing, collapse-to-false, and
# collapse-to-true cases exercise every simplify_weak_local rule.
test('ltl_simplify_weak', check,
  args: [files(cases / 'simplify_demo.s0.ltl'),
         exe['tlsf2ltl'], '--weak-simplify',
         files(cases / 'simplify_demo.tlsf')])

test('ltl_simplify_strong', check,
  args: [files(cases / 'simplify_demo.s1.ltl'),
         exe['tlsf2ltl'], '--strong-simplify',
         files(cases / 'simplify_demo.tlsf')])

test('ltl_simplify_false', check,
  args: [files(cases / 'collapse_demo.s0.ltl'),
         exe['tlsf2ltl'], '--weak-simplify',
         files(cases / 'collapse_demo.tlsf')])

test('ltl_simplify_true', check,
  args: [files(cases / 'truths_demo.s0.ltl'),
         exe['tlsf2ltl'], '--weak-simplify',
         files(cases / 'truths_demo.tlsf')])

# Push-inwards and pull-outwards rewrites.
foreach rw : [['push-globally-in', 'pgi'], ['push-finally-in', 'pfi'],
              ['push-next-in', 'pxi'], ['pull-globally-out', 'pgo'],
              ['pull-finally-out', 'pfo'], ['pull-next-out', 'pxo']]
  test('ltl_' + rw[1], check,
    args: [files(cases / 'rewrites.' + rw[1] + '.ltl'),
           exe['tlsf2ltl'], '--' + rw[0],
           files(cases / 'rewrites.tlsf')])
endforeach

test('tlsf_basic_expand', check,
  args: [files(cases / 'Patterns_Uright_uright06.basic.tlsf'),
         exe['tlsf2tlsf'], '--basic',
         files(cases / 'Patterns_Uright_uright06.tlsf')])

test('tlsf_param_subst', check,
  args: [files(cases / 'param_demo.subst.tlsf'),
         exe['tlsf2tlsf'], '--param', 'n=5',
         files(cases / 'param_demo.tlsf')])

test('info_block', check,
  args: [files(cases / 'Patterns_Uright_uright06.info'),
         exe['tlsfinfo'], '--info',
         files(cases / 'Patterns_Uright_uright06.tlsf')])

foreach c : ['next_n', 'ranges']
  test('info_bounded_' + c, check,
    args: [files(cases / c + '.bounded'),
           exe['tlsfinfo'], '--bounded-temporal',
           files(cases / c + '.tlsf')])
endforeach

# GR(1) recognition.
foreach c : ['gr0_spec', 'gr1_spec', 'gr2_spec', 'gr4_spec', 'notgr_spec']
  test('gr_' + c, check,
    args: [files(cases / c + '.gr'),
           exe['tlsfinfo'], '--generalized-reactivity', files(cases / c + '.tlsf')])
endforeach

# tlsfinfo selection flags.
foreach sel : [['--title', 'title'], ['--description', 'description'],
               ['--semantics', 'semantics'], ['--target', 'target'],
               ['--tags', 'tags'], ['--parameters', 'params'],
               ['--input-signals', 'inputs'], ['--output-signals', 'outputs'],
               ['--expanded-ins', 'expanded_ins'],
               ['--expanded-outs', 'expanded_outs'],
               ['--info', 'info']]
  test('info_' + sel[1], check,
    args: [files(cases / 'meta.' + sel[1]),
           exe['tlsfinfo'], sel[0], files(cases / 'meta.tlsf')])
endforeach
test('info_all', check,
  args: [files(cases / 'meta.all'), exe['tlsfinfo'], files(cases / 'meta.tlsf')])
test('info_check', check,
  args: [files(cases / 'meta.check'), exe['tlsfinfo'], '--check',
         files(cases / 'meta.tlsf')])
test('err_check_invalid', xfail,
  args: [exe['tlsfinfo'], '--check', files(cases / 'bad_syntax.tlsf')])

# Primed (and @) identifiers, e.g. req' / grant'.
test('primes_inputs', check,
  args: [files(cases / 'primes.inputs'), exe['tlsfinfo'], '--input-signals',
         files(cases / 'primes.tlsf')])
test('primes_ltl', check,
  args: [files(cases / 'primes.ltl'), exe['tlsf2ltl'],
         files(cases / 'primes.tlsf')])

# Uppercase atom names: ltlxba lowercases them (spot/ltl2ba read uppercase as
# operators, so this is what ltlsynt consumes, matching syfco -f ltlxba); the
# faithful ltl dialect keeps the original case.
test('ltl_upper_atoms_ltlxba', check,
  args: [files(cases / 'upper_atoms.ltlxba.ltl'), exe['tlsf2ltl'],
         '--format', 'ltlxba', files(cases / 'upper_atoms.tlsf')])
test('ltl_upper_atoms_ltl', check,
  args: [files(cases / 'upper_atoms.ltl'), exe['tlsf2ltl'],
         '--format', 'ltl', files(cases / 'upper_atoms.tlsf')])

# tlsf2ltl modes: safety / liveness selection and -os/-ot overrides.
test('ltl_safety', check,
  args: [files(cases / 'arbiter_simple.safety.ltl'),
         exe['tlsf2ltl'], '--safety', arbiter_simple])
test('ltl_liveness', check,
  args: [files(cases / 'arbiter_simple.liveness.ltl'),
         exe['tlsf2ltl'], '--liveness', arbiter_simple])
test('ltl_os_moore', check,
  args: [files(cases / 'conv_moore_mealy.os.ltl'),
         exe['tlsf2ltl'], '--overwrite-semantics', 'Moore', files(cases / 'conv_moore_mealy.tlsf')])

# Exercises the NNF duals (R/W/M/U, <->, !F, !U).
test('ltl_operators', check,
  args: [files(cases / 'operators.ltl'),
         exe['tlsf2ltl'], files(cases / 'operators.tlsf')])
test('ltl_operators_full', check,
  args: [files(cases / 'operators.full.ltl'),
         exe['tlsf2ltl'], '--parenthesize', files(cases / 'operators.tlsf')])

# tlsf2tlsf default re-emission: GLOBAL section (parameters, definitions,
# definition calls), bus-range expressions, big-operators and SIZEOF.
test('tlsf_reemit', check,
  args: [files(cases / 'meta.reemit.tlsf'),
         exe['tlsf2tlsf'], files(cases / 'meta.tlsf')])
test('tlsf_reemit_defs', check,
  args: [files(cases / 'defs.reemit.tlsf'),
         exe['tlsf2tlsf'], files(cases / 'defs.tlsf')])
test('tlsf_subst_defs', check,
  args: [files(cases / 'defs.subst.tlsf'),
         exe['tlsf2tlsf'], '--param', 'n=5', files(cases / 'defs.tlsf')])
test('tlsf_reemit_quant', check,
  args: [files(cases / 'expand_demo.reemit.tlsf'),
         exe['tlsf2tlsf'], files(cases / 'expand_demo.tlsf')])
test('err_tlsf_bad_param', xfail,
  args: [exe['tlsf2tlsf'], '--param', 'nope=1', files(cases / 'defs.tlsf')])

# Error paths: these must exit non-zero.
test('err_no_input',     xfail, args: [exe['tlsf2ltl']])
test('err_missing_file', xfail, args: [exe['tlsf2ltl'], 'does_not_exist.tlsf'])
test('err_bad_param',    xfail,
  args: [exe['tlsf2ltl'], '--param', 'oops', files(cases / 'meta.tlsf')])
test('err_bad_semantics', xfail,
  args: [exe['tlsf2ltl'], '--overwrite-semantics', 'Bogus', files(cases / 'meta.tlsf')])
test('err_parse',        xfail,
  args: [exe['tlsf2ltl'], files(cases / 'bad_syntax.tlsf')])
test('err_strong_next_infinite', xfail,
  args: [exe['tlsf2ltl'], files(cases / 'strong_next_infinite.tlsf')])
test('err_strong_next_overwrite', xfail,
  args: [exe['tlsf2ltl'], '--overwrite-semantics', 'Mealy',
         files(cases / 'gnext_strong_fin.tlsf')])
# Expansion failure (an unbound parameter) must error.
test('err_expand',       xfail,
  args: [exe['tlsf2ltl'], files(cases / 'bad_expand.tlsf')])

# Definition expansion: nullary + parameterised definitions, recursive
# case-definitions (with `otherwise`), integer-returning defs, and SIZEOF.
test('expand_defs_gr', check,
  args: [files(cases / 'defs.gr'), exe['tlsfinfo'],
         '--generalized-reactivity', files(cases / 'defs.tlsf')])
test('expand_mutual_exclusion', check,
  args: [files(cases / 'mutual_exclusion.ltl'), exe['tlsf2ltl'],
         files(cases / 'mutual_exclusion.tlsf')])
test('expand_recursion', check,
  args: [files(cases / 'recursion.ltl'), exe['tlsf2ltl'],
         files(cases / 'recursion.tlsf')])
# X[n] n-fold next operator expands to nested X.
test('next_n', check,
  args: [files(cases / 'next_n.ltl'), exe['tlsf2ltl'],
         files(cases / 'next_n.tlsf')])
# Default re-emission of a case-definition (exercises ITE/comparison printing).
test('reemit_cases', check,
  args: [files(cases / 'recursion.reemit.tlsf'), exe['tlsf2tlsf'],
         files(cases / 'recursion.tlsf')])
# A call to an undefined definition must error.
test('err_undef_def', xfail,
  args: [exe['tlsf2ltl'], files(cases / 'undef_def.tlsf')])

# Exercises the assumptions -> guarantees implication path (the cases above
# are guarantee-only).
test('ltl_assume_guarantee', check,
  args: [files(cases / 'arbiter_simple.ltl'),
         exe['tlsf2ltl'], arbiter_simple])

# Expansion: parameters, parametric bus ranges, bus indexing, bounded
# big-operators (&&[..]/||[..]) and SIZEOF.
test('expand_ltl', check,
  args: [files(cases / 'expand_demo.ltl'),
         exe['tlsf2ltl'], files(cases / 'expand_demo.tlsf')])

test('expand_ltl_param', check,
  args: [files(cases / 'expand_demo.n2.ltl'),
         exe['tlsf2ltl'], '--param', 'n=2',
         files(cases / 'expand_demo.tlsf')])

test('expand_basic', check,
  args: [files(cases / 'expand_demo.basic.tlsf'),
         exe['tlsf2tlsf'], '--basic',
         files(cases / 'expand_demo.tlsf')])

# Full six-section TLSF semantics:
# INITIALLY -> (PRESET & ((G REQUIRE & ASSUME) -> (G ASSERT & GUARANTEE)))
test('semantics_sections', check,
  args: [files(cases / 'sections.ltl'),
         exe['tlsf2ltl'], files(cases / 'sections.tlsf')])

# Strict semantics follows TLSF §3.2: INITIALLY guards the consequent, PRESET is
# a step-0 conjunct, and raw ASSERT/REQUIRE invariants form the weak-until.
test('semantics_strict', check,
  args: [files(cases / 'sections.strict.ltl'),
         exe['tlsf2ltl'], files(cases / 'sections_strict.tlsf')])

test('semantics_strict_preset_liveness', check,
  args: [files(cases / 'strict_preset_liveness.ltl'),
         exe['tlsf2ltl'], files(cases / 'strict_preset_liveness.tlsf')])

# Relax a strict spec by overwriting its semantics to non-strict: plain E -> S.
test('semantics_relax_via_override', check,
  args: [files(cases / 'sections.ltl'),
         exe['tlsf2ltl'], '--overwrite-semantics', 'Mealy',
         files(cases / 'sections_strict.tlsf')])

# Mealy/Moore conversion when SEMANTICS and TARGET disagree.
test('semantics_moore_to_mealy', check,
  args: [files(cases / 'conv_moore_mealy.ltl'),
         exe['tlsf2ltl'], files(cases / 'conv_moore_mealy.tlsf')])
test('semantics_mealy_to_moore', check,
  args: [files(cases / 'conv_mealy_moore.ltl'),
         exe['tlsf2ltl'], files(cases / 'conv_mealy_moore.tlsf')])

# The installed checker must not pull in a GR(1) solve.
if research_tools and have_oxidd and native_gr1 and python3.found()
  test('checker_link_independence', python3,
    args: [files('checker_link_independence.py'), meson.project_build_root(),
           exe['tlsfcertcheck']],
    is_parallel: false)
endif
