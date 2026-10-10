#!/usr/bin/env python3
"""Report of B2 / B3 / B3-X (research/city_sim/PROTOCOL_CITY_COTRAIN_20261004.md; written 04/10/2026 wake 2 while training ran, before
any B3-X row existed for a new checkpoint).  SELF-CHECKS: completeness (650 configs x 5 seeds) and bit-identity with the h0 panel on
every shared configuration.  Endpoints C-1 .. C-3 (two-level bootstrap: training index x evaluation seed, 2000 draws, rng 0), C-4 and C-5
reported."""
import json
from pathlib import Path
import numpy as np

X2 = Path('research/city_sim/xplay2_20261004'); H0 = Path('research/city_sim/xplay_h0_20261004'); COT = Path('research/city_sim/cotrain_20261004')
SEEDS = [100, 101, 102, 103, 104]; K = [0, 1, 2, 3]; ARMS = ['SIM-halt', 'ALT-halt', 'SIM-delay']
LIGHTS = ['ACT', 'FT'] + [f'{f}:{t}' for f in ('RL-H', 'RL-C50', 'RL-J') for t in K] + [f'{a}:{k}' for a in ARMS for k in K]
FLEETS = ['human'] + [f'{f}:{t}' for f in ('L-ACT', 'L-FT', 'L-RLH') for t in K] + [f'{a}:{k}' for a in ARMS for k in K]
FAM = {a: ([f'{a}:{k}' for k in K], [f'{a}:{k}' for k in K]) for a in ARMS}
FAM['S1 (RL-H, L-RLH)'] = ([f'RL-H:{t}' for t in K], [f'L-RLH:{t}' for t in K]); FAM['S2 (RL-J, L-ACT)'] = ([f'RL-J:{t}' for t in K], [f'L-ACT:{t}' for t in K])
FAM['C50 (RL-C50, L-ACT)'] = ([f'RL-C50:{t}' for t in K], [f'L-ACT:{t}' for t in K]); FAM['H (RL-H, L-ACT)'] = ([f'RL-H:{t}' for t in K], [f'L-ACT:{t}' for t in K])
B = 2000


def load(d, key):
    R = {}
    for f in d.glob('*.json'):
        if f.name.startswith('report'):
            continue
        x = json.loads(f.read_text())
        if x.get('status') == 'COMPLETE':
            for r in x['rows']:
                R[key(r)] = r
    return R


def boot(fn, rng):
    """two-level bootstrap of a statistic fn(idx over 4 training indices, sdx over 5 seeds)."""
    v = [fn(rng.integers(0, 4, 4), rng.integers(0, 5, 5)) for _ in range(B)]
    v = np.array([x for x in v if np.isfinite(x)])
    return np.percentile(v, [2.5, 97.5]), len(v)


def main():
    R = load(X2, lambda r: (r['light'], r['fleet'], r['seed'])); out = [f'== B3-X all lights x all fleets ({len(R)} runs)']
    miss = [(l, f, s) for l in LIGHTS for f in FLEETS for s in SEEDS if (l, f, s) not in R]
    H = load(H0, lambda r: (r['light'], r['fleet'], r['seed']) if r['sense'] == 'default' else None); H.pop(None, None)
    shared = [k for k in H if k in R]; diff = [k for k in shared if any(R[k][m] != H[k][m] for m in ('timeloss', 'hidden_a', 'hidden_h', 'unfinished'))
                                                or ('approach_cost' in H[k] and R[k]['approach_cost'] != H[k]['approach_cost'])]
    ok = not miss and len(shared) == 390 and not diff                # 13 lights x 6 fleets x 5 seeds
    out.append(f'SELF-CHECK completeness: {len(LIGHTS)} lights x {len(FLEETS)} fleets x 5 seeds, missing {len(miss)} {miss[:3]}; '
               f'bit-identity with the h0 panel: {len(shared) - len(diff)}/{len(shared)} shared runs {diff[:3]} -> {"PASS" if ok else "FAIL"}')
    if not ok:
        (X2 / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    TL = lambda l, f, s: R[(l, f, s)]['timeloss']
    # training logs (B2 / B3)
    for f in sorted(COT.glob('*.log.json')):
        L = json.loads(f.read_text()); tele = [r['teleports'] for r in L]
        out.append(f"  train {f.name[:-9]:14s} episodes {len(L):3d}  teleports first 5 {tele[:5]} last 5 {tele[-5:]}  "
                   f"last-10 r_L {np.nanmean([r.get('r_L', np.nan) for r in L[-10:]]):+.3f} r_F {np.nanmean([r.get('r_F', np.nan) for r in L[-10:]]):+.3f}")
    rng = np.random.default_rng(0); res = {}

    def own(fam):
        Ls, Fs = FAM[fam]; return np.array([[TL(Ls[k], Fs[k], s) for s in SEEDS] for k in K])

    def cube(fam):
        Ls, Fs = FAM[fam]; return np.array([[[TL(Ls[i], Fs[j], s) for s in SEEDS] for j in K] for i in K])

    def spec(C, idx, sdx):
        Cs = C[:, :, sdx].mean(2); d = [Cs[i, i] for i in idx]; o = [Cs[i, j] for i in idx for j in idx if i != j]
        return np.mean(o) - np.mean(d) if o else np.nan
    out.append('Own-pair city time loss (s/veh; mean over 4 training indices x 5 seeds) and partner specificity Spec = off-diagonal - diagonal:')
    for fam in FAM:
        O, C = own(fam), cube(fam); sp = spec(C, np.arange(4), np.arange(5)); (lo, hi), n = boot(lambda i, s: spec(C, i, s), rng)
        res[fam] = dict(own=O.mean(), own_k=O.mean(1).tolist(), spec=sp, spec_ci=[lo, hi], cross=C.mean(2).tolist())
        out.append(f"  {fam:22s} own {O.mean():7.2f} (per index {' '.join(f'{x:6.2f}' for x in O.mean(1))})  Spec {sp:+7.2f} [{lo:+.2f}, {hi:+.2f}] ({n} draws)")
    paired = lambda A, Bm: (lambda i, s: (A - Bm)[i][:, s].mean())
    D1 = own('SIM-halt') - own('S1 (RL-H, L-RLH)'); (lo, hi), _ = boot(paired(own('SIM-halt'), own('S1 (RL-H, L-RLH)')), rng)
    out.append(f"C-1 SIM-halt own - S1 own: {D1.mean():+.2f} [{lo:+.2f}, {hi:+.2f}] -> {'SUPPORTED' if hi < 0 else 'NOT SUPPORTED'}")
    C2 = res['SIM-halt']; out.append(f"C-2 Spec(SIM-halt) {C2['spec']:+.2f} [{C2['spec_ci'][0]:+.2f}, {C2['spec_ci'][1]:+.2f}] -> {'SUPPORTED' if C2['spec_ci'][0] > 0 else 'NOT SUPPORTED'}")
    Ca, Cb = cube('SIM-halt'), cube('S1 (RL-H, L-RLH)'); d2 = spec(Ca, np.arange(4), np.arange(5)) - spec(Cb, np.arange(4), np.arange(5))
    (lo, hi), n = boot(lambda i, s: spec(Ca, i, s) - spec(Cb, i, s), rng)
    out.append(f"C-2b Spec(SIM-halt) - Spec(S1): {d2:+.2f} [{lo:+.2f}, {hi:+.2f}] ({n} draws) -> {'SUPPORTED' if lo > 0 else 'NOT SUPPORTED'}")
    D3 = own('SIM-delay') - own('SIM-halt'); (lo, hi), _ = boot(paired(own('SIM-delay'), own('SIM-halt')), rng)
    out.append(f"C-3 SIM-delay own - SIM-halt own: {D3.mean():+.2f} [{lo:+.2f}, {hi:+.2f}] -> {'SUPPORTED' if hi < 0 else 'NOT SUPPORTED'}")
    for a, b in (('ALT-halt', 'SIM-halt'), ('S2 (RL-J, L-ACT)', 'S1 (RL-H, L-RLH)')):
        (lo, hi), _ = boot(paired(own(a), own(b)), rng); out.append(f"C-4 {a} own - {b} own: {(own(a) - own(b)).mean():+.2f} [{lo:+.2f}, {hi:+.2f}]")
    act_h = np.mean([TL('ACT', 'human', s) for s in SEEDS])
    out.append(f"C-4 light gain with human traffic (ACT {act_h:.2f} s/veh minus light): " +
               ', '.join(f"{l} {act_h - np.mean([TL(l, 'human', s) for s in SEEDS]):+.2f}" for l in LIGHTS if l not in ('ACT',)))
    out.append('C-4 fleets in an ACT city (TL with fleet, ACT light): ' + ', '.join(f"{f} {np.mean([TL('ACT', f, s) for s in SEEDS]):.2f}" for f in FLEETS))
    # C-5 decomposition
    for name, Ls, Fs, m in (('city TL', LIGHTS, FLEETS, 'timeloss'), ('fleet approach cost', LIGHTS, FLEETS[1:], 'approach_cost')):
        M = np.array([[np.mean([R[(l, f, s)][m] for s in SEEDS]) for f in Fs] for l in Ls]); g = M.mean(); r = M.mean(1) - g; c = M.mean(0) - g
        I = M - g - r[:, None] - c[None, :]; ss = np.array([len(Fs) * (r ** 2).sum(), len(Ls) * (c ** 2).sum(), (I ** 2).sum()])
        out.append(f"C-5 {name}: {len(Ls)} x {len(Fs)} cell means; shares light {ss[0] / ss.sum():.2f}, fleet {ss[1] / ss.sum():.2f}, interaction {ss[2] / ss.sum():.2f}")
        res[f'C5_{m}'] = dict(M=M.tolist(), shares=(ss / ss.sum()).tolist())
    for fam in FAM:
        C = cube(fam).mean(2); g = C.mean(); r = C.mean(1) - g; c = C.mean(0) - g; I = C - g - r[:, None] - c[None, :]
        ss = np.array([4 * (r ** 2).sum(), 4 * (c ** 2).sum(), (I ** 2).sum()])
        out.append(f"   within {fam:22s} 4x4 city TL: light {ss[0] / ss.sum():.2f} fleet {ss[1] / ss.sum():.2f} interaction {ss[2] / ss.sum():.2f}; "
                   f"agent vs human TL own pairs {np.mean([R[(FAM[fam][0][k], FAM[fam][1][k], s)]['timeloss_agent'] for k in K for s in SEEDS]):.2f} / "
                   f"{np.mean([R[(FAM[fam][0][k], FAM[fam][1][k], s)]['timeloss_human'] for k in K for s in SEEDS]):.2f}; teleports own {np.mean([R[(FAM[fam][0][k], FAM[fam][1][k], s)]['teleports'] for k in K for s in SEEDS]):.1f}")
    txt = '\n'.join(out) + '\n'; (X2 / 'report.txt').write_text(txt); (X2 / 'report.json').write_text(json.dumps(res, indent=1, default=float)); print(txt)


if __name__ == '__main__':
    main()
