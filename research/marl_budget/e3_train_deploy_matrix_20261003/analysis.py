import json, numpy as np
from pathlib import Path
from scipy.stats import spearmanr
W = Path(__file__).parent; D = json.load(open(W / 'matrix.json')); C = D['cells']
ORDER = ['K1', 'K2', 'K3', 'iid']; DIAG = {'relay6Cage_st': {'iid'}, 'relayCage_st': {'iid'}, 'relayAttnCage_st': {'iid'}, 'relaySCCage_st': {'iid'},
       'relayCK1_st': {'K1'}, 'relayCK2_st': {'K2'}, 'relayMIX_st': {'K1', 'K2', 'K3', 'iid'}, 'relayMIX2_st': {'K1', 'iid'}}
cell = {(c['grid'], c['panel'], c['fam'], c['K']): c for c in C}
rng = np.random.default_rng(1)
def sboot(v, B=20000):
    v = np.asarray(v); return np.percentile(v[rng.integers(0, len(v), (B, len(v)))].mean(1), [2.5, 97.5])
print('(1) per receiver x panel: best deployment cell, diagonal marked; paired (same seeds) off-diagonal loss = gain(K) - gain(diag)')
recs = sorted({(c['grid'], c['fam']) for c in C})
summary = {}
for grid, fam in recs:
    for p in sorted({c['panel'] for c in C if c['grid'] == grid and c['fam'] == fam}):
        ks = [k for k in ORDER + ['K4', 'K5', 'K6', 'K7'] if (grid, p, fam, k) in cell]
        if len(ks) < 2: continue
        means = {k: cell[(grid, p, fam, k)]['mean'] for k in ks}; best = max(means, key=means.get)
        line = f'  {grid} {p} {fam:16s} ' + ' '.join(f'{k}{"*" if k in DIAG[fam] else ""}:{means[k]:+.2f}' for k in ks) + f' | best {best}{"(diag)" if best in DIAG[fam] else ""}'
        dg = [k for k in ks if k in DIAG[fam]]
        if len(dg) == 1 and fam not in ('relayMIX_st', 'relayMIX2_st'):
            d = dg[0]; S = cell[(grid, p, fam, d)]['seeds']; gd = dict(zip(S, cell[(grid, p, fam, d)]['per_seed']))
            for k in ks:
                if k == d: continue
                Sk = cell[(grid, p, fam, k)]['seeds']; gk = dict(zip(Sk, cell[(grid, p, fam, k)]['per_seed'])); ss = [s for s in S if s in gk]
                diff = [gk[s] - gd[s] for s in ss]; lo, hi = sboot(diff)
                direction = 'UP' if (ORDER + ['K4','K5','K6','K7']).index(k) > (ORDER + ['K4','K5','K6','K7']).index(d) else 'DOWN'
                summary.setdefault((grid, fam, d, k, direction), []).append((p, np.mean(diff), lo, hi, sum(x < 0 for x in diff), len(diff)))
        print(line)
print('\n    off-diagonal loss (gain at deployment K minus gain on the training channel), per panel: mean [seed-boot 95 %] (seeds < 0)')
for (grid, fam, d, k, direction), L in sorted(summary.items()):
    pm = np.mean([x[1] for x in L])
    print(f'  {grid} {fam:16s} {d}->{k:4s} {direction:4s} mean over {len(L)} panels {pm:+6.2f} | ' + '; '.join(f'{p}: {m:+.2f} [{lo:+.2f},{hi:+.2f}] ({n}/{N})' for p, m, lo, hi, n, N in L))
print('\n(2) mixture premium on each specialist own channel (paired by seed, same panel): direct ratio -(sum MIX / sum SPEC - 1)*100 and gain difference')
import re
M = Path('/Users/phanan/cig-amf-main/research/marl_budget')
def rows(top, tag):
    r = json.loads((M / top / tag / 'rows.json').read_text()); return {x['episode']: x['queue_sum'] for x in r if x['rule'] == 'prefix'}
TOPS = {3801: ('e3_mixed_channel_20261002', 'R_{f}_s{s}_{K}'), 4501: ('e3_mix2_20261002', 'R_{f}_s{s}_{K}'), 4401: ('e3_switch_20261002', 'R_{f}_s{s}_{K}')}
KT = {3801: {'K1': 'K1', 'iid': 'K0', 'K2': 'K2', 'K3': 'K3'}, 4501: {'K1': 'K1', 'iid': 'K0', 'K2': 'K2', 'K3': 'K3'}, 4401: {'K1': 'k1', 'iid': 'iid'}}
for mix in ('relayMIX_st', 'relayMIX2_st'):
    for spec, K in (('relayCK1_st', 'K1'), ('relay6Cage_st', 'iid')):
        for p in (3801, 4401, 4501):
            if ('3x3', p, mix, K) not in cell or ('3x3', p, spec, K) not in cell: continue
            S = [s for s in cell[('3x3', p, mix, K)]['seeds'] if s in cell[('3x3', p, spec, K)]['seeds']]
            top, pat = TOPS[p]; r = []
            for s in S:
                a = rows(top, pat.format(f=mix, s=s, K=KT[p][K])); b = rows(top, pat.format(f=spec, s=s, K=KT[p][K])); e = sorted(a)
                r.append(-(sum(a[x] for x in e) / sum(b[x] for x in e) - 1) * 100)
            gm = dict(zip(cell[('3x3', p, mix, K)]['seeds'], cell[('3x3', p, mix, K)]['per_seed'])); gs = dict(zip(cell[('3x3', p, spec, K)]['seeds'], cell[('3x3', p, spec, K)]['per_seed']))
            gd = [gm[s] - gs[s] for s in S]; lo, hi = sboot(r)
            print(f'  {p} {mix} vs {spec} at {K} (n={len(S)}, seeds {S[0]}-{S[-1]}): ratio {np.mean(r):+.2f} [{lo:+.2f},{hi:+.2f}] (>0 {sum(x > 0 for x in r)}/{len(r)}) | gain diff {np.mean(gd):+.2f}')
print('  CK2 vs MIX at K2: never on the same panel (CK2 only 3901; MIX on 3801/4401/4501) -> unpaired: CK2@K2 3901 %+.2f vs MIX@K2 3801 %+.2f / 4501 %+.2f' % (
    cell[('3x3', 3901, 'relayCK2_st', 'K2')]['mean'], cell[('3x3', 3801, 'relayMIX_st', 'K2')]['mean'], cell[('3x3', 4501, 'relayMIX_st', 'K2')]['mean']))
print('\n(3) shape over channel quality K1 < K2 < K3 < iid: per seed Spearman(order, gain), seeds monotone non-decreasing, seeds with iid < K1')
for grid, fam in recs:
    for p in sorted({c['panel'] for c in C if c['grid'] == grid and c['fam'] == fam}):
        ks = [k for k in ORDER if (grid, p, fam, k) in cell]
        if len(ks) < 3: continue
        S = sorted(set.intersection(*[set(cell[(grid, p, fam, k)]['seeds']) for k in ks]))
        G = np.array([[dict(zip(cell[(grid, p, fam, k)]['seeds'], cell[(grid, p, fam, k)]['per_seed']))[s] for k in ks] for s in S])
        rho = [spearmanr(range(len(ks)), g)[0] for g in G]; mono = sum(np.all(np.diff(g) >= 0) for g in G)
        hz = sum(g[-1] < g[0] for g in G) if ks[0] == 'K1' and ks[-1] == 'iid' else None
        mm = G.mean(0); shape = 'monotone up' if np.all(np.diff(mm) >= 0) else ('monotone down' if np.all(np.diff(mm) <= 0) else 'non-monotone')
        print(f'  {grid} {p} {fam:16s} K {ks} mean shape: {shape:13s} | per-seed rho mean {np.mean(rho):+.2f} (rho>0 {sum(r > 0 for r in rho)}/{len(S)}), monotone-up seeds {mono}/{len(S)}' + (f', iid<K1 seeds {hz}/{len(S)}' if hz is not None else ''))
