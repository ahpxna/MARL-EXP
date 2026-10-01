"""Step 3 pilot test analysis (read-only): paired gains over the SAME base prefix, per cap.

Per (method, critic variant, cap): value gain over prefix averaged over (snapshot, K) inside
each test episode, then over the 8 test episodes; episodes with positive mean; extra bytes;
paired learned_R1 - direct_unrestricted; search error exact_R1 - oracle_search_R1 (uncapped).
Critic seeds are averaged inside an episode (they are initialisations, not traffic seeds).
"""
import gzip, json, sys
from collections import defaultdict
import numpy as np

rows = [json.loads(l) for l in gzip.open(sys.argv[1], 'rt')]
cell = defaultdict(lambda: defaultdict(list))      # (method, variant, cap) -> episode -> gains
byte = defaultdict(lambda: defaultdict(list))
pair = defaultdict(lambda: defaultdict(list))
ref = defaultdict(lambda: defaultdict(list))
ctx = defaultdict(dict)
for r in rows:
    cap = 'none' if r['cap_extra'] is None else f"+{r['cap_extra']}"
    variant = 'oracle' if r['critic'] is None else r['critic'].split('/')[0]
    key = (r['method'], variant, cap)
    g = r['value'] - r['prefix_value']
    cell[key][r['episode_id']].append(g); byte[key][r['episode_id']].append(r['bytes'] - r['prefix_bytes'])
    ck = (r['episode_id'], r['t'], r['k_index'], cap, r['critic'])
    ctx[ck][r['method']] = r['value']
    if r['cap_extra'] is None and r['method'] == 'oracle_search_R1':
        ref['exact_R1_minus_prefix'][r['episode_id']].append(r['exact_R1'] - r['prefix_value'])
        ref['exact_private_minus_prefix'][r['episode_id']].append(r['exact_private'] - r['prefix_value'])
        ref['search_error_R1'][r['episode_id']].append(r['exact_R1'] - r['value'])
for (e, t, kx, cap, critic), d in ctx.items():
    if critic is not None and 'learned_R1' in d and 'direct_unrestricted' in d:
        pair[(critic.split('/')[0], cap)][e].append(d['learned_R1'] - d['direct_unrestricted'])

def summ(d):
    ep = np.array([np.mean(v) for v in d.values()])
    return f'{ep.mean():+7.2f}  [{ep.min():+6.2f},{ep.max():+6.2f}]  pos {int((ep > 1e-9).sum())}/{len(ep)}'

print('references (uncapped, true value):')
for k in ('exact_R1_minus_prefix', 'exact_private_minus_prefix', 'search_error_R1'):
    print(f'  {k:28s} {summ(ref[k])}')
print('\ngain over the same base prefix: mean over episodes [min,max] episodes>0 | extra bytes')
for key in sorted(cell, key=lambda k: (k[1], k[0], k[2])):
    print(f'  {key[0]:22s} {key[1]:10s} cap {key[2]:5s} {summ(cell[key])} | '
          f'{np.mean([np.mean(v) for v in byte[key].values()]):+6.1f} B')
print('\npaired learned_R1 - direct_unrestricted (same critic, same calls, same cap):')
for key in sorted(pair):
    print(f'  {key[0]:10s} cap {key[1]:5s} {summ(pair[key])}')
