"""Recompute, from rows.json, the newly allowed finished panels used by F1 / F4 / F5:
 test D (4x4, e3_g4_mix_20261002, panel 4601-4664; relayMIX / relayCage / relayCK1 x K1, K2, K3, iid; seeds 0-9),
 support fallback (e3_fallback_20261002: 3x3 panel 4801-4864 seeds 0-4, 4x4 panel 4901-4964 seeds 0-9; RELAY / FB_S),
 age emulation (e3_age_emulation_20261003: panel 5101-5164; 4x4 seeds 0-9, 3x3 seeds 0-4; PLAIN / EMU / LAB).
Provenance: manifest COMPLETE + PASS, panel traffic seeds exact, checkpoint path family/seed, checkpoint sha vs current file."""
import json, re
from pathlib import Path
import numpy as np
from common import *
CK = {}
def ck_check(m, d):
    a = m['args']; p = a.get('relay') or (a.get('actors') or [''])[0].split('=')[-1]
    s = m.get('checkpoint_sha256') or m.get('relay_sha256')
    if p:
        cur = CK.setdefault(p, sha_file(ROOT / p)); ok = (s is None) or (s == cur)
        return p, s is not None, ok
    return None, False, True
prov = []; out = {}
def panel_check(m, t0, d):
    ts = m['args']['traffic_seeds']; assert ts[0] == t0 and ts[-1] == t0 + 63 and len(ts) == 64, (d, ts[:2])
# ---- test D
P = MB / 'e3_g4_mix_20261002'; eps = episodes(4601); Z = {}
for s in range(10):
    m = manifest(P / f'Z_s{s}'); panel_check(m, 4601, P); Z[s] = load_rows(P / f'Z_s{s}', 'rule', 'none', eps)
    prov.append(('testD', f'Z_s{s}', *ck_check(m, P)))
KN = {'K1': 'K1', 'K2': 'K2', 'K3': 'K3', 'K0': 'iid'}
for fam in ('relayMIX_st', 'relayCage_st', 'relayCK1_st'):
    for K in ('K1', 'K2', 'K3', 'K0'):
        per = []; pairs = []
        for s in range(10):
            d = P / f'R_{fam}_s{s}_{K}'; m = manifest(d); panel_check(m, 4601, d); assert f'{fam}_s{s}/' in str(m['args']), d
            x = load_rows(d, 'rule', 'prefix', eps); per.append(gain(x, Z[s])); pairs.append((x, Z[s])); prov.append(('testD', d.name, *ck_check(m, d)))
        lo, hi = boot2(pairs)
        out[f'4x4|4601|{fam}|{KN[K]}'] = dict(seeds=list(range(10)), per_seed=per, mean=float(np.mean(per)), lo=lo, hi=hi, npos=int(sum(v > 0 for v in per)), source=f'{P.name}/R_{fam}_s*_{K}/rows.json (rule prefix) vs Z_s*/rows.json (rule none)')
# ---- fallback
for net, t0, seeds, arms in (('3x3', 4801, range(5), ('relay6Cage_st', 'relayCK1_st', 'relayMIX_st', 'relayMIX2_st')), ('4x4', 4901, range(10), ('relayCage_st', 'relayCK1_st'))):
    P = MB / 'e3_fallback_20261002' / net; eps = episodes(t0); Z = {}
    for s in seeds:
        m = manifest(P / f'Z_s{s}'); panel_check(m, t0, P); Z[s] = load_rows(P / f'Z_s{s}', 'system', 'Z', eps)
    for fam in arms:
        for K in ('K1', 'K0'):
            for sysn in ('RELAY', 'FB_S'):
                per = []; pairs = []
                for s in seeds:
                    d = P / f'FB_{fam}_s{s}_{K}'; m = manifest(d); panel_check(m, t0, d); assert f'{fam}_s{s}/' in str(m['args']), d
                    x = load_rows(d, 'system', sysn, eps); per.append(gain(x, Z[s])); pairs.append((x, Z[s])); prov.append(('fallback', f'{net}/{d.name}', *ck_check(m, d)))
                lo, hi = boot2(pairs)
                out[f'{net}|{t0}|{fam}|{KN[K]}|{sysn}'] = dict(seeds=list(seeds), per_seed=per, mean=float(np.mean(per)), lo=lo, hi=hi, npos=int(sum(v > 0 for v in per)),
                                                             source=f'e3_fallback_20261002/{net}/FB_{fam}_s*_{K}/rows.json (system {sysn}) vs Z_s*/rows.json (system Z)')
# ---- age emulation
for net, seeds, cage in (('4x4', range(10), 'relayCage_st'), ('3x3', range(5), 'relay6Cage_st')):
    P = MB / 'e3_age_emulation_20261003' / net; eps = episodes(5101); Z = {}
    for s in seeds:
        m = manifest(P / f'Z_s{s}'); panel_check(m, 5101, P); Z[s] = load_rows(P / f'Z_s{s}', 'rule', 'none', eps)
    for fam, Ks in (('relayCK1_st', ('K1', 'K0')), (cage, ('K0',))):
        for K in Ks:
            for md in ('plain', 'emu', 'lab'):
                per = []; pairs = []
                for s in seeds:
                    d = P / f'EM_{fam}_s{s}_{K}'; m = manifest(d); panel_check(m, 5101, d); assert f'{fam}_s{s}/' in str(m['args']), d
                    x = load_rows(d, 'mode', md, eps); per.append(gain(x, Z[s])); pairs.append((x, Z[s])); prov.append(('emulation', f'{net}/{d.name}', *ck_check(m, d)))
                lo, hi = boot2(pairs)
                out[f'{net}|5101|{fam}|{KN[K]}|{md.upper()}'] = dict(seeds=list(seeds), per_seed=per, mean=float(np.mean(per)), lo=lo, hi=hi, npos=int(sum(v > 0 for v in per)),
                                                                   source=f'e3_age_emulation_20261003/{net}/EM_{fam}_s*_{K}/rows.json (mode {md}) vs Z_s*/rows.json (rule none)')
json.dump(dict(cells=out, provenance=dict(n=len(prov), with_sha=sum(p[3] for p in prov), sha_mismatch=[p for p in prov if not p[4]],
                                           no_sha=sorted({(p[0], re.sub(r'_s\d.*', '', p[1].split('/')[-1])) for p in prov if not p[3]}))), open(OUT / 'extra_data.json', 'w'), indent=1, default=float)
for k, v in out.items():
    print(f'{k:44s} {v["mean"]:+6.2f} [{v["lo"]:+.2f},{v["hi"]:+.2f}] {v["npos"]}/{len(v["seeds"])}')
print('provenance: manifests', len(prov), 'with ckpt sha', sum(p[3] for p in prov), 'mismatch', [p for p in prov if not p[4]])
print('no sha:', sorted({(p[0], re.sub(r'_s\d.*', '', p[1].split('/')[-1])) for p in prov if not p[3]}))
