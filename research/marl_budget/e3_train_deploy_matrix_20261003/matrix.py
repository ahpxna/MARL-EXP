"""E3 TRAIN x DEPLOY matrix from finished panels, recomputed from rows.json (read-only).
gain vs Z = -(sum R / sum Z - 1) * 100 per seed (ratio of sums over the panel's 128 episodes), mean over seeds;
95 % CI: two-level bootstrap (seeds, then traffic seeds shared within a draw) as scripts/MARL_e3_g4_train_match_report.py."""
import json, re, hashlib, os
from pathlib import Path
import numpy as np
ROOT = Path('/Users/phanan/cig-amf-main'); M = ROOT / 'research/marl_budget'
K4 = {'K1': 'K1', 'K2': 'K2', 'K3': 'K3', 'K0': 'iid', 'const1': 'K1', 'const2': 'K2', 'const3': 'K3', 'const4': 'K4', 'const5': 'K5',
      'const6': 'K6', 'const7': 'K7', 'iid': 'iid', 'k1': 'K1', 'k1_iid': 'sw:k1_iid', 'iid_k1': 'sw:iid_k1', 'alt4': 'sw:alt4'}
# panel spec: (grid, dir, first traffic seed, evaluator family, list of (regex on tag -> receiver-family group), Z tag regex)
PANELS = [
 ('3x3', 'e3_train_match_20261001', 3201, r'^R_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('3x3', 'e3_ageclip_prospective_20261001', 3101, r'^R_s(\d)_(K\d)_A-1$'),
 ('3x3', 'e3_gate_prospective_20261001', 3401, r'^R_s(\d)_(K\d)$'),
 ('3x3', 'e3_demand_frontier_20261001', 2801, r'^R_s(\d)_(const\d)$'),
 ('3x3', 'e3_harm_prospective_20261001', 3001, r'^R_s(\d)_(const\d)$'),
 ('3x3', 'e3_arch_control_20261001', 3601, r'^R_(relay\w+?_st)_s(\d)_(const\d|iid)$'),
 ('3x3', 'e3_mismatch_law_20261002', 3701, r'^R_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('3x3', 'e3_mixed_channel_20261002', 3801, r'^R_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('3x3', 'e3_w1_prospective_20261002', 3901, r'^R_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('3x3', 'e3_age_remap_20261002', 4001, r'^P_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('3x3', 'e3_support_projection_20261002', 4101, r'^P_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('3x3', 'e3_switch_20261002', 4401, r'^R_(relay\w+?_st)_s(\d)_(k1|iid|k1_iid|iid_k1|alt4)$'),
 ('3x3', 'e3_mix2_20261002', 4501, r'^R_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('4x4', 'e3_g4_train_match_20261002', 4201, r'^R_(relay\w+?_st)_s(\d)_(K\d)$'),
 ('4x4', 'e3_g4_constk_20261001', 3301, r'^R_s(\d)_(K\d)_A-1$'),
 ('4x4', 'e3_g4_time_projection_20261002', 4301, r'^P_s(\d)_(K\d)$'),
 ('4x4', 'e3_g4_replication_20261001', 2901, r'^R_s(\d)_(iid)$'),
]
SHA = {}
def sha(p):
    if p not in SHA: SHA[p] = hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
    return SHA[p]
def rows_of(d, rule):
    r = json.loads((d / 'rows.json').read_text()); return {x['episode']: x['queue_sum'] for x in r if x['rule'] == rule}
DATA = {}; PROV = []
for grid, top, t0, rx in PANELS:
    P = M / top; eps = [f'seed{s}_load{h}' for s in range(t0, t0 + 64) for h in (8, 16)]
    Z = {}
    for d in sorted(P.glob('Z_s*')):
        if not (d / 'manifest.json').exists(): continue
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m.get('self_check') == 'PASS', d
        a = m['args']; ts = a['traffic_seeds']; assert ts[0] == t0 and len(ts) == 64, (d, ts[:2])
        s = int(re.search(r'Z_s(\d)$', d.name).group(1)); ck = a['actors'][0].split('=')[1]; assert f'distill_none_s{s}/' in ck, d
        rr = rows_of(d, 'none'); assert sorted(rr) == sorted(eps), d; Z[s] = np.array([rr[e] for e in eps])
        PROV.append(dict(top=top, tag=d.name, ck=ck, sha_m=m.get('checkpoint_sha256'), mt_ok=os.path.getmtime(ROOT / ck) < os.path.getmtime(d / 'rows.json')))
    for d in sorted(P.iterdir()):
        mm = re.match(rx, d.name)
        if not mm or not (d / 'manifest.json').exists(): continue
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m.get('self_check') == 'PASS', d
        a = m['args']; ts = a['traffic_seeds']; assert ts[0] == t0 and ts[-1] == t0 + 63 and len(ts) == 64, (d, ts[:2])
        ck = a['relay'] if str(a.get('relay', '')).endswith('.pt') else a['actors'][0].split('=')[1]
        g = mm.groups(); fam = g[0] if len(g) == 3 else re.search(r'/(relay\w+?_st)_s\d', ck).group(1); s = int(g[-2]); K = K4[g[-1]]
        assert f'{fam}_s{s}/' in ck, (d, ck)
        if a.get('A') not in (None, -1.0) or a.get('project') not in (None, 'none'): continue
        rr = rows_of(d, 'prefix'); assert sorted(rr) == sorted(eps), (d, len(rr))
        DATA[(grid, top, t0, fam, K, s)] = np.array([rr[e] for e in eps])
        PROV.append(dict(top=top, tag=d.name, ck=ck, sha_m=m.get('checkpoint_sha256'), mt_ok=os.path.getmtime(ROOT / ck) < os.path.getmtime(d / 'rows.json')))
    DATA[(grid, top, t0, 'Z', None, None)] = Z
def gain(x, z, ii=None): return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100
rng = np.random.default_rng(0)
def boot2(pairs, B=2000):
    """pairs: list of (X, Z) arrays per seed (same panel); two-level bootstrap of the mean gain."""
    n = len(pairs); ts = np.arange(64); out = []
    for _ in range(B):
        ss = rng.integers(0, n, n); tt = rng.integers(0, 64, 64); ii = np.concatenate([2 * tt, 2 * tt + 1])
        out.append(np.mean([gain(pairs[i][0], pairs[i][1], ii) for i in ss]))
    return np.percentile(out, [2.5, 97.5])
CELLS = []
keys = sorted({k[:5] for k in DATA if k[3] != 'Z'}, key=lambda k: (k[0], k[2], k[3], k[4]))
for grid, top, t0, fam, K in keys:
    Z = DATA[(grid, top, t0, 'Z', None, None)]
    S = sorted(k[5] for k in DATA if k[:5] == (grid, top, t0, fam, K))
    S = [s for s in S if s in Z]
    pairs = [(DATA[(grid, top, t0, fam, K, s)], Z[s]) for s in S]; g = np.array([gain(x, z) for x, z in pairs])
    lo, hi = boot2(pairs) if len(S) > 1 else (np.nan, np.nan)
    CELLS.append(dict(grid=grid, panel=t0, top=top, fam=fam, K=K, seeds=S, per_seed=g.tolist(), mean=float(g.mean()), lo=float(lo), hi=float(hi), npos=int((g > 0).sum())))
json.dump(dict(cells=CELLS, prov=PROV), open(Path(__file__).with_name('matrix.json'), 'w'), default=float)
# provenance summary
bad = [p for p in PROV if p['sha_m'] and p['sha_m'] != sha(p['ck'])]
nosha = sorted({(p['top'], p['ck'].split('/')[-2].rsplit('_s', 1)[0]) for p in PROV if not p['sha_m']})
mt_bad = [p for p in PROV if not p['mt_ok']]
print(f'manifests checked {len(PROV)}; sha recorded {sum(1 for p in PROV if p["sha_m"])}, mismatching current file: {len(bad)}; ckpt newer than eval rows: {len(mt_bad)}')
print('no sha recorded (top, family):', nosha)
for c in CELLS:
    print(f"{c['grid']} {c['panel']} {c['fam']:16s} {c['K']:10s} n={len(c['seeds'])} seeds {c['seeds'][0]}-{c['seeds'][-1]}  {c['mean']:+6.2f} [{c['lo']:+.2f},{c['hi']:+.2f}]  >0 {c['npos']}/{len(c['seeds'])}")
