"""PROTOCOL_HETERO_v0 §4 decision rule on the exact oracle records (read-only).

Per episode: average over K_eval vectors, then over the preregistered snapshots.  Uncertified
(x, K) (a product above the cap) are excluded and counted.
(a) mean(adv_R1 - adv_R0) > 0 in >= 12 of 16 episodes
(b) across episodes, mean(adv_R1 - adv_R0) >= 0.25 * mean(private - adv_R0)
"""
import gzip, json, sys
from collections import defaultdict
import numpy as np

rows = [json.loads(l) for l in gzip.open(sys.argv[1], 'rt')]
Q = ['adv_R0', 'adv_R1', 'adv_R2', 'heur_R0', 'heur_R1', 'heur_R2', 'private']
ep = defaultdict(lambda: defaultdict(list)); skipped = 0; total = 0
for r in rows:
    snap = defaultdict(list)
    for e in r['evals']:
        total += 1
        if any(e[q] is None for q in Q):
            skipped += 1; continue
        v = {q: e[q]['value'] for q in Q}; b = {q: e[q]['bytes'] for q in Q}
        v['known_shared'] = e['known_shared']; b['known_shared'] = e['known_shared_bytes']
        for q in v:
            snap['v_' + q].append(v[q]); snap['b_' + q].append(b[q])
    for key, vals in snap.items():
        ep[r['episode_id']][key].append(np.mean(vals))
E = {e: {k: np.mean(v) for k, v in d.items()} for e, d in ep.items()}
def diff(a, b, pre='v_'):
    return np.array([E[e][pre + a] - E[e][pre + b] for e in sorted(E)])
d1 = diff('adv_R1', 'adv_R0'); d2 = diff('adv_R2', 'adv_R0'); dp = diff('private', 'adv_R0')
dk = diff('known_shared', 'adv_R0'); h1 = diff('heur_R1', 'heur_R0'); h2 = diff('heur_R2', 'heur_R0')
hp = diff('private', 'heur_R0'); ah = diff('adv_R0', 'heur_R0')
b1 = diff('adv_R1', 'adv_R0', 'b_'); bp = diff('private', 'adv_R0', 'b_'); bh1 = diff('heur_R1', 'heur_R0', 'b_')
def s(x): return f'{np.mean(x):+.2f} (episodes {np.min(x):+.2f}..{np.max(x):+.2f}; positive {int((x > 1e-9).sum())}/{len(x)})'
print(f'records {len(rows)}, (snapshot,K) pairs {total}, uncertified skipped {skipped}, episodes {len(E)}')
print('value gains (held-phase value units; higher is better):')
print('  adv_R1 - adv_R0      ', s(d1))
print('  adv_R2 - adv_R0      ', s(d2))
print('  private - adv_R0     ', s(dp))
print('  known_shared - adv_R0', s(dk), ' (cost of preparing before the reveal)')
print('  adv_R0 - heur_R0     ', s(ah), ' (oracle advance order vs public heuristic)')
print('  heur_R1 - heur_R0    ', s(h1))
print('  heur_R2 - heur_R0    ', s(h2))
print('  private - heur_R0    ', s(hp))
print('extra bytes:')
print('  adv_R1 - adv_R0', s(b1)); print('  heur_R1 - heur_R0', s(bh1)); print('  private - adv_R0', s(bp))
a = int((d1 > 1e-9).sum()) >= 12
ratio = np.mean(d1) / np.mean(dp) if np.mean(dp) > 1e-9 else float('nan')
b = np.mean(dp) > 1e-9 and ratio >= 0.25
print(f'DECISION RULE: (a) {int((d1 > 1e-9).sum())}/16 episodes positive -> {a}; '
      f'(b) R1 recovers {ratio:.2f} of private gap -> {b}; SUPPORTED = {a and b}')
