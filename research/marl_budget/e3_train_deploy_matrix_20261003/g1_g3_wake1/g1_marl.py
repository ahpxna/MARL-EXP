"""G1 on MARL panels: paired-by-seed information/excess split from raw rows.json (read-only)."""
import json, hashlib, sys
from pathlib import Path
import numpy as np
ROOT = Path('/Users/phanan/cig-amf-main'); M = ROOT / 'research/marl_budget'
PANELS = {
 '4x4 train-match': dict(dir='e3_g4_train_match_20261002', ts=(4201, 4264), seeds=list(range(10)), cage='relayCage_st', ck1='relayCK1_st'),
 '3x3 train-match': dict(dir='e3_train_match_20261001', ts=(3201, 3264), seeds=list(range(5)), cage='relay6Cage_st', ck1='relayCK1_st'),
 '3x3 mixed-channel': dict(dir='e3_mixed_channel_20261002', ts=(3801, 3864), seeds=list(range(5)), cage='relay6Cage_st', ck1='relayCK1_st'),
}
PROV = {}
def load(P, tag, rule, ck):
    d = M / P['dir'] / tag; m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    a = m['args']; assert f'{ck}/ckpt_best.pt' in str(a), (tag, a)
    ts = a['traffic_seeds']; assert ts[0] == P['ts'][0] and ts[-1] == P['ts'][1] and len(ts) == 64, (tag, ts[:2])
    eps = [f'seed{s}_load{h}' for s in range(P['ts'][0], P['ts'][1] + 1) for h in (8, 16)]
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    assert sorted(rows) == sorted(eps), (tag, len(rows))
    ckp = a.get('relay') or (a.get('actors') or [''])[0].split('=')[-1]
    PROV[(P['dir'], tag)] = dict(ckpt=ckp, sha_manifest=m.get('checkpoint_sha256'), K=m.get('K', a.get('capacity')))
    return np.array([rows[e] for e in eps], float), eps
def gain(x, z, ii=None):
    return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100
def ci_seed(v, B=20000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v); bs = v[rng.integers(0, len(v), (B, len(v)))].mean(1); return np.percentile(bs, [2.5, 97.5])
out = {}
for name, P in PANELS.items():
    S = P['seeds']; Z = {}; X = {}
    for s in S:
        Z[s], eps = load(P, f'Z_s{s}', 'none', f'distill_none_s{s}')
        for a in (P['cage'], P['ck1']):
            for K in (0, 1):
                X[(a, s, K)], _ = load(P, f'R_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}')
    ts = sorted({e.split('_')[0] for e in eps}); idx = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in ts}
    c, k = P['cage'], P['ck1']
    def comps(s, ii=None):
        g = lambda a, K: gain(X[(a, s, K)], Z[s], ii)
        up_info = g(c, 0) - g(k, 1); up_exc = g(k, 0) - g(c, 0); up_tot = g(k, 0) - g(k, 1)
        dn_info = g(k, 1) - g(c, 0); dn_exc = g(c, 1) - g(k, 1); dn_tot = g(c, 1) - g(c, 0)
        return np.array([g(k, 1), g(k, 0), g(c, 0), g(c, 1), up_info, up_exc, up_tot, dn_info, dn_exc, dn_tot])
    names = ['g(CK1@K1)', 'g(CK1@iid)', 'g(Cage@iid)', 'g(Cage@K1)', 'UP info = g(Cage@iid)-g(CK1@K1)', 'UP excess = g(CK1@iid)-g(Cage@iid)',
             'UP total = g(CK1@iid)-g(CK1@K1)', 'DOWN info = g(CK1@K1)-g(Cage@iid)', 'DOWN excess = g(Cage@K1)-g(CK1@K1)', 'DOWN total = g(Cage@K1)-g(Cage@iid)']
    V = np.array([comps(s) for s in S])
    ident = np.max(np.abs(V[:, 4] + V[:, 5] - V[:, 6])), np.max(np.abs(V[:, 7] + V[:, 8] - V[:, 9]))
    # two-level bootstrap (seeds, then traffic seeds shared within a draw across arms of one seed, as the report scripts do)
    rng = np.random.default_rng(0); BS = []
    for _ in range(2000):
        ss = rng.choice(S, len(S)); ii = np.concatenate([idx[ts[j]] for j in rng.choice(len(ts), len(ts))])
        BS.append(np.mean([comps(s, ii) for s in ss], 0))
    BS = np.array(BS)
    print(f'\n=== {name}: {P["dir"]}, panel {P["ts"][0]}-{P["ts"][1]} x 8/16 (128 episodes), seeds {S} (n = {len(S)}); identity max |err| up {ident[0]:.1e} down {ident[1]:.1e}')
    for j, nm in enumerate(names):
        lo, hi = ci_seed(V[:, j]); l2, h2 = np.percentile(BS[:, j], [2.5, 97.5])
        print(f'  {nm:40s} mean {V[:, j].mean():+6.2f}  seed-boot [{lo:+.2f},{hi:+.2f}]  2-level [{l2:+.2f},{h2:+.2f}]  >0: {(V[:, j] > 0).sum()}/{len(S)}  per seed ' + ' '.join(f'{v:+.2f}' for v in V[:, j]))
    sh = V[:, 5] / V[:, 6]; print('  excess share of UP total per seed:', ' '.join(f'{v:.2f}' for v in sh), '| share of mean', round(V[:, 5].mean() / V[:, 6].mean(), 3))
    out[name] = dict(names=names, per_seed=V.tolist(), seeds=S)
# provenance: checkpoint sha (manifest vs file now; same student across panels?)
print('\n=== provenance')
shas = {}
for (dr, tag), p in PROV.items():
    if 'Z_' in tag and not p['sha_manifest']:
        f = ROOT / p['ckpt'];
    f = ROOT / p['ckpt']; now = hashlib.sha256(f.read_bytes()).hexdigest() if f.exists() else None
    shas.setdefault(p['ckpt'], set()).add((p['sha_manifest'], now))
bad = {k: v for k, v in shas.items() if any(sm is not None and sm != nw for sm, nw in v)}
nosha = sorted({k for k, v in shas.items() if any(sm is None for sm, _ in v)})
print('checkpoints used:', len(shas), '| manifest sha != current file sha:', len(bad), bad if bad else '')
print('checkpoints with NO sha in some manifest:', len(nosha), nosha[:6], '...' if len(nosha) > 6 else '')
json.dump(out, open(Path(__file__).with_suffix('.json'), 'w'))
