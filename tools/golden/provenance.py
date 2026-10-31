"""Offline provenance rules: distinguish reference checks from native snapshots."""
from collections import Counter


def describe(name, records):
    labels = Counter(row[0] for row in records)
    checks = []
    if labels['verdict']:
        checks.append('Spot 2.16 synthesis verdicts')
    if labels['language']:
        checks.append('Spot 2.16 lasso memberships (bounded language evidence)')
    if name.startswith('norm-'):
        checks.append('Spot 2.16 normalized formula equivalence')
    if name == 'conversion':
        checks.append('Spot 2.16 AST/string formula equivalence')
    snapshots = sorted(set(labels) - {'verdict', 'language', 'normalized'})
    if name == 'conversion':
        snapshots = ['export serialization and cluster partitions']
    return {'status': 'independently confirmed' if checks else 'native snapshot',
            'independent_checks': checks, 'native_snapshot': snapshots}


def required(name):
    if name.startswith(('compose-', 'review4-')) and name != 'compose-wrapper':
        return {'verdict'}
    if name.startswith('norm-') or name == 'conversion':
        return {'equivalence'}
    return {'native-language': {'language'}, 'monitor-game': {'language', 'verdict'},
            'decomposition': {'verdict'}, 'disjoint-assumptions': {'language', 'verdict'}}.get(name, set())
