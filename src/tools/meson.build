# Command-line tools: one directory per tool, holding its main and any code
# only that tool uses. common/ has the file helpers several tools share. The
# top-level meson.build turns each entry of `tools` into build/<tool>.

tools_common = static_library('tlsf-tools-common', 'common/cli.c')
tool_dep = declare_dependency(
  include_directories: include_directories('common'),
  link_with: tools_common,
  dependencies: tlsf_internal_dep,
)

tools = {
  'tlsf2ltl': {'sources': files('tlsf2ltl/main.c'),
               'dependencies': tool_dep},
  'tlsf2tlsf': {'sources': files('tlsf2tlsf/main.c'),
                'dependencies': tool_dep},
  'tlsfinfo': {'sources': files('tlsfinfo/main.c'),
               'dependencies': tool_dep},
  'tlsfnorm': {'sources': files('tlsfnorm/main.c'),
               'dependencies': tool_dep},
  'mealy2moore': {'sources': files('mealy2moore/main.c'),
                  'dependencies': tlsf_internal_dep},
}

if research_tools
  tools += {
    'tlsftemplates': {'sources': files('tlsftemplates/main.c'),
                      'dependencies': tool_dep},
    'tlsfbenchgraph': {'sources': files('tlsfbenchgraph/main.c'),
                       'dependencies': tool_dep},
    'tlsfresidual': {'sources': files('tlsfresidual/main.c'),
                     'dependencies': tool_dep},
  }
  if have_oxidd
    tools += {
      'tlsfcompose': {
        'sources': files('tlsfcompose/main.c',
                         'tlsfcompose/compose_analysis.c',
                         'tlsfcompose/compose_games.c',
                         'tlsfcompose/compose_oxidd.c',
                         'tlsfcompose/compose_route.c'),
        'dependencies': [tool_dep, tlsf_oxidd_dep],
      },
      'tlsfsolve': {'sources': files('tlsfsolve/main.c'),
                    'dependencies': tlsf_oxidd_dep},
      'tlsfcertcheck': {'sources': files('tlsfcertcheck/main.c'),
                        'dependencies': tlsf_oxidd_dep},
    }
  endif
endif
