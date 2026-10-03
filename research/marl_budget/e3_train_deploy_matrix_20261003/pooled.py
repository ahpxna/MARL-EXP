import json, numpy as np
from pathlib import Path
W = Path(__file__).parent; C = json.load(open(W / 'matrix.json'))['cells']
rng = np.random.default_rng(2)
cell = {(c['grid'], c['panel'], c['fam'], c['K']): c for c in C}
print('pooled matrix: per seed, average over the panels where the cell exists; seed bootstrap 95 %; [panel-mean range]')
for grid, fam in sorted({(c['grid'], c['fam']) for c in C}):
    out = []
    for K in ('K1', 'K2', 'K3', 'iid'):
        cs = [c for c in C if c['grid'] == grid and c['fam'] == fam and c['K'] == K]
        if not cs: out.append(f'{K}: —'); continue
        per = {}
        for c in cs:
            for s, g in zip(c['seeds'], c['per_seed']): per.setdefault(s, []).append(g)
        v = np.array([np.mean(x) for x in per.values()]); bs = v[rng.integers(0, len(v), (20000, len(v)))].mean(1); lo, hi = np.percentile(bs, [2.5, 97.5])
        pm = [c['mean'] for c in cs]
        out.append(f'{K}: {v.mean():+.2f} [{lo:+.2f},{hi:+.2f}] {int((v > 0).sum())}/{len(v)} seeds, {len(cs)} panels [{min(pm):+.2f}..{max(pm):+.2f}]')
    print(f'  {grid} {fam:16s} ' + ' | '.join(out))
# bridge: CK2 vs MIX at K2 through relay6Cage on each panel (unpaired panels)
def d(p, a, b, K):
    A = dict(zip(cell[('3x3', p, a, K)]['seeds'], cell[('3x3', p, a, K)]['per_seed'])); B = dict(zip(cell[('3x3', p, b, K)]['seeds'], cell[('3x3', p, b, K)]['per_seed']))
    S = [s for s in A if s in B]; return np.mean([A[s] - B[s] for s in S]), len(S)
print('bridge at K2 (gain minus relay6Cage gain, same panel, paired seeds): CK2 3901 %+.2f (n %d); MIX 3801 %+.2f (n %d); MIX 4501 %+.2f (n %d); MIX2 4501 %+.2f (n %d)' % (
    *d(3901, 'relayCK2_st', 'relay6Cage_st', 'K2'), *d(3801, 'relayMIX_st', 'relay6Cage_st', 'K2'), *d(4501, 'relayMIX_st', 'relay6Cage_st', 'K2'), *d(4501, 'relayMIX2_st', 'relay6Cage_st', 'K2')))
print('bridge at K2 vs CK1 (same panel): CK2-CK1 3901 %+.2f; MIX-CK1 3801 %+.2f, 4501 %+.2f; MIX2-CK1 4501 %+.2f' % (
    d(3901, 'relayCK2_st', 'relayCK1_st', 'K2')[0], d(3801, 'relayMIX_st', 'relayCK1_st', 'K2')[0], d(4501, 'relayMIX_st', 'relayCK1_st', 'K2')[0], d(4501, 'relayMIX2_st', 'relayCK1_st', 'K2')[0]))
