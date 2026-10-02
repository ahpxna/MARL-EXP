#!/usr/bin/env python3
"""Report of PROTOCOL_E3_G4_REPLICATION_20261001.md (written 01/10/2026 11:1x EDT, before any target run).

R1 main effect (two-level bootstrap, upper < 0 in iid / cap4 / low), R2 Spearman(N_s, gain_s) >= 0.5, R3 N_s beats D_s.
Seeds with an incomplete chain are excluded and named; fewer than 8 complete seeds -> INCOMPLETE.
"""
from __future__ import annotations
import json, re
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); E = M / 'e3_g4_replication_20261001'; A = M / 'e3_grid4x4_20260930/actors'
EPS = [f'seed{s}_load{h}' for s in range(2901, 2965) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CONDS = {'iid': ('iid', 'prefix'), 'cap4': ('iid', 'cap4'), 'low': ('low', 'prefix')}


def rows(tag, rule):
    d = E / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    if m.get('status') != 'COMPLETE' or m.get('self_check') not in ('PASS', None):
        return None
    r = {x['episode']: x['queue_sum'] for x in json.loads((d / 'rows.json').read_text()) if x['rule'] == rule}
    return np.array([r[e] for e in EPS], float) if sorted(r) == sorted(EPS) else None


def N_of(s):
    d = E / f'VD_s{s}'
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    if m.get('self_check') != 'PASS' or int(m.get('parity_episodes', 0)) != 64:
        return None
    z = np.load(d / 'depth.npz'); return float(1 - np.mean(z['minset'][:, 1] == 0))


def D_of(s):
    f = A / f'distill_none_s{s}.log'
    if not f.exists():
        return None
    a = re.findall(r'agree ([0-9.]+)', f.read_text()); return 1 - float(a[-1]) if a else None


def eff(x, z, ii=None):
    return x.sum() / z.sum() - 1 if ii is None else x[ii].sum() / z[ii].sum() - 1


def main():
    data = {}
    for s in range(10):
        Z = rows(f'Z_s{s}', 'none'); X = {c: rows(f'R_s{s}_{t}', r) for c, (t, r) in CONDS.items()}
        N = N_of(s); D = D_of(s)
        if Z is not None and all(v is not None for v in X.values()) and N is not None and D is not None:
            data[s] = dict(Z=Z, X=X, N=N, D=D)
    missing = [s for s in range(10) if s not in data]; L = [f'complete seeds {sorted(data)}; excluded {missing}']
    out = dict(complete=sorted(data), excluded=missing)
    if len(data) < 8:
        L.append('INCOMPLETE: fewer than 8 complete seeds, no verdict')
    else:
        S = sorted(data); rng = np.random.default_rng(0); r1 = True
        for c in CONDS:
            est = float(np.mean([eff(data[s]['X'][c], data[s]['Z']) for s in S])); bs = []
            for _ in range(4000):
                ss = rng.choice(S, len(S))
                bs.append(np.mean([eff(data[s]['X'][c], data[s]['Z'], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
            lo, hi = np.percentile(bs, [2.5, 97.5]); r1 &= bool(hi < 0)
            out[f'R1_{c}'] = dict(mean=100 * est, lo=100 * lo, hi=100 * hi)
            L.append(f'R1 {c:5s}: {100*est:+.2f} % [{100*lo:+.2f}, {100*hi:+.2f}]')
        gain = {s: -100 * float(np.mean([eff(data[s]['X'][c], data[s]['Z']) for c in CONDS])) for s in S}
        rN = float(spearmanr([data[s]['N'] for s in S], [gain[s] for s in S]).correlation)
        rD = float(spearmanr([data[s]['D'] for s in S], [gain[s] for s in S]).correlation)
        out.update(R1=bool(r1), R2=bool(rN >= 0.5), R3=bool(rN > rD), rho_N=rN, rho_D=rD,
                   per_seed={s: dict(gain=gain[s], N=data[s]['N'], D=data[s]['D']) for s in S})
        # ADDENDUM 1 (11:2x, before any 4x4 result): R4 specificity beyond teacher confidence
        mg = {}
        for s in S:
            f = E / f'MG_s{s}' / 'manifest.json'
            if f.exists():
                mm = json.loads(f.read_text())
                if mm.get('self_check') == 'PASS' and int(mm.get('parity_episodes', 0)) == 64:
                    mg[s] = float(mm['mean_margin'])
        if len(mg) == len(S):
            from scipy.stats import rankdata
            rM = float(spearmanr([mg[s] for s in S], [gain[s] for s in S]).correlation)
            def res(y, x):
                y = rankdata([y[s] for s in S]); x = rankdata([x[s] for s in S]); b = np.polyfit(x, y, 1); return y - np.polyval(b, x)
            pr = float(np.corrcoef(res(gain, mg), res({s: data[s]['N'] for s in S}, mg))[0, 1])
            out.update(R4=bool(rN > rM and pr >= 0.3), rho_margin=rM, partial_N_given_margin=pr)
            L.append(f'R4 Spearman(margin, gain) = {rM:.3f}; partial(N | margin) = {pr:+.3f} -> {"SUPPORTED" if out["R4"] else "NOT SUPPORTED"}')
        else:
            L.append(f'R4 INCOMPLETE: margin probes for {sorted(mg)}')
        L.append(f'R1 (upper < 0 in all three): {"SUPPORTED" if r1 else "NOT SUPPORTED"}')
        L.append(f'R2 Spearman(N_s, gain_s) = {rN:.3f} -> {"SUPPORTED" if rN >= 0.5 else "NOT SUPPORTED"}')
        L.append(f'R3 Spearman(D_s, gain_s) = {rD:.3f} -> {"SUPPORTED" if rN > rD else "NOT SUPPORTED"} (N beats D)')
        for s in S:
            L.append(f'  s{s}: gain {gain[s]:+.2f} %  N {data[s]["N"]:.3f}  D {data[s]["D"]:.3f}')
    text = '\n'.join(L); print(text)
    (M / 'e3_g4_replication_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_g4_replication_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
