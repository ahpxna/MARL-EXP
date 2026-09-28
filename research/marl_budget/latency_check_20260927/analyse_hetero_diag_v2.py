"""Summarise diag v2 (read-only).  Operating point +28 B first, then the other caps."""
import json, sys
from collections import defaultdict
import numpy as np

rep = json.load(open(sys.argv[1]))
R = rep['results']
fam = defaultdict(list)
for name, res in R.items():
    fam[name.split('/')[0]].append(res)
first = next(iter(R.values()))['caps']
print('oracle (stored candidates):', {c: round(first[c]['oracle_R1']['gain'], 2) for c in first})
for cap in ['+28', '+0', '+56', 'none']:
    print(f'\n== cap {cap} ==')
    for f, runs in fam.items():
        for pol in ('repair_R1', 'direct'):
            gains = [r['caps'][cap][pol]['gain'] for r in runs]
            eps = [sum(v > 1e-9 for v in r['caps'][cap][pol]['gain_by_episode'].values()) for r in runs]
            s = lambda k: np.mean([r['caps'][cap][pol][k] for r in runs])
            hw = defaultdict(list)
            for r in runs:
                for h, v in r['caps'][cap][pol]['gain_by_headway'].items():
                    hw[h].append(v)
            taus = [r['tau'][pol] for r in runs]
            print(f'  {f:22s} {pol:9s} gain {min(gains):+6.2f}..{max(gains):+6.2f} ep+ {eps} '
                  f'edit {s("edit_rate"):.2f} harm/grp {s("harm_rate_over_groups"):.2f} harm/edit {s("harm_over_edits"):.2f} '
                  f'actchg {s("action_change_rate"):.2f} {s("extra_bytes"):+5.1f}B tau {["never" if t is None else round(t, 2) for t in taus]} '
                  f'hw ' + ' '.join(f'{h}:{np.mean(v):+.2f}' for h, v in sorted(hw.items())))
print('\nselection info:', {n: r['selection'] for n, r in R.items() if 'ridge' in n})
print('ridge margins:', {n: r['margins'] for n, r in R.items() if 'ridge' in n})
