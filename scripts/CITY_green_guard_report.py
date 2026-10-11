#!/usr/bin/env python3
"""Report of L4 (research/city_sim/PROTOCOL_CITY_GREEN_GUARD_20261004.md; written 04/10/2026 wake 3 while the panel ran, before any
L4 row was read).  SELF-CHECK: guard 'none' rows = the h0 panel bit for bit (SELECT; every shared config).  GG-1..GG-5 as registered."""
import json
from pathlib import Path
import numpy as np

G = Path('research/city_sim/green_guard_20261004'); H0 = Path('research/city_sim/xplay_h0_20261004')
SEL = [100, 101, 102, 103, 104]; TST = list(range(200, 210)); T = [0, 1, 2, 3]


def load(d, key):
    R = {}
    for f in d.glob('*.json'):
        if f.name.startswith('report'):
            continue
        x = json.loads(f.read_text())
        if x.get('status') == 'COMPLETE':
            for r in x['rows']:
                k = key(r)
                if k is not None:
                    R[k] = r
    return R


def boot(D, rng):
    n, m = D.shape; bs = [D[rng.integers(0, n, n)][:, rng.integers(0, m, m)].mean() for _ in range(2000)]
    return np.percentile(bs, [2.5, 97.5])


def main():
    S = load(G / 'select', lambda r: (r['light'], r['fleet'], r['guard'], r['seed'])); X = load(G / 'test', lambda r: (r['light'], r['fleet'], r['guard'], r['seed']))
    P = load(H0, lambda r: (r['light'], r['fleet'], r['seed']) if r['sense'] == 'default' else None)
    lights = ['ACT'] + [f'{f}:{t}' for f in ('RL-H', 'RL-C50', 'RL-J') for t in T]; fleets = [f'L-ACT:{t}' for t in T]
    miss = [(l, f, g, s) for l in lights for f in fleets for g in ('none', 'green', 'green+oos') for s in SEL if (l, f, g, s) not in S]
    miss += [(l, f, g, s) for l in ['ACT'] + [f'RL-H:{t}' for t in T] for f in fleets for g in ('none', 'green+oos') for s in TST if (l, f, g, s) not in X]
    bad = [k for k in P if (k[0], k[1], 'none', k[2]) in S and any(S[(k[0], k[1], 'none', k[2])][m] != P[k][m] for m in ('timeloss', 'timeloss_agent', 'timeloss_human', 'unfinished'))]
    shared = sum(1 for k in P if (k[0], k[1], 'none', k[2]) in S)
    out = [f'== L4 green-release guard ({len(S)} SELECT + {len(X)} TEST runs)']
    ok = not miss and not bad and shared == 260
    out.append(f"SELF-CHECK: 'none' rows = h0 panel on {shared - len(bad)}/{shared} shared runs (expect 260/260); missing {len(miss)} {miss[:3]} -> {'PASS' if ok else 'FAIL'}")
    if not ok:
        (G / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    rng = np.random.default_rng(0); res = {}
    cells = lambda fam: [(f'{fam}:{i}', f'L-ACT:{j}') for i in T for j in T]
    for fam in ('RL-H', 'RL-C50', 'RL-J'):
        for g in ('green+oos', 'green'):
            D = np.array([[S[(l, f, g, s)]['timeloss_agent'] - S[(l, f, 'none', s)]['timeloss_agent'] for s in SEL] for l, f in cells(fam)]); lo, hi = boot(D, rng)
            city = np.array([np.mean([S[(l, f, g, s)]['timeloss'] for s in SEL]) for l, f in cells(fam)])
            act = np.array([np.mean([S[('ACT', f, 'none', s)]['timeloss'] for s in SEL]) for l, f in cells(fam)])
            plain = np.array([np.mean([S[(l, f, 'none', s)]['timeloss'] for s in SEL]) for l, f in cells(fam)])
            dh = np.mean([[S[(l, f, g, s)]['timeloss_human'] - S[(l, f, 'none', s)]['timeloss_human'] for s in SEL] for l, f in cells(fam)])
            share = np.mean([S[(l, f, g, s)]['released'] / max(1, S[(l, f, g, s)]['decisions']) for l, f in cells(fam) for s in SEL])
            res[f'{fam}/{g}'] = dict(dA=float(D.mean()), ci=[float(lo), float(hi)], city=city.tolist(), act=act.tolist(), plain=plain.tolist(), dh=float(dh), share=float(share))
            tag = {('RL-H', 'green+oos'): 'GG-1', ('RL-C50', 'green+oos'): 'GG-3'}.get((fam, g), 'GG-5')
            out.append(f"{tag} {fam} x L-ACT, guard {g}: agent TL change {D.mean():+.2f} [{lo:+.2f}, {hi:+.2f}] s/veh; city TL {city.mean():.2f} (plain {plain.mean():.2f}, ACT baseline {act.mean():.2f}); "
                       f"cells below ACT {int((city < act).sum())}/16 (plain {int((plain < act).sum())}/16); human TL change {dh:+.2f}; released share {share:.3f}"
                       + (f" -> {'SUPPORTED' if hi < 0 else 'NOT SUPPORTED'}" if tag in ('GG-1', 'GG-3') else ''))
            if (fam, g) == ('RL-H', 'green+oos'):
                out.append(f"GG-2 (SELECT) city TL below ACT baseline in {int((city < act).sum())}/16 (>= 12) -> {'SUPPORTED' if (city < act).sum() >= 12 else 'NOT SUPPORTED'}")
    cityT = np.array([np.mean([X[(f'RL-H:{i}', f'L-ACT:{j}', 'green+oos', s)]['timeloss'] for s in TST]) for i in T for j in T])
    actT = np.array([np.mean([X[('ACT', f'L-ACT:{j}', 'none', s)]['timeloss'] for s in TST]) for i in T for j in T])
    plainT = np.array([np.mean([X[(f'RL-H:{i}', f'L-ACT:{j}', 'none', s)]['timeloss'] for s in TST]) for i in T for j in T])
    out.append(f"GG-2T (TEST 200-209) city TL with green+oos {cityT.mean():.2f} (plain {plainT.mean():.2f}, ACT baseline {actT.mean():.2f}); cells below ACT {int((cityT < actT).sum())}/16 (>= 12) -> "
               f"{'SUPPORTED' if (cityT < actT).sum() >= 12 else 'NOT SUPPORTED'}; per cell (rows RL-H_t): " + ' | '.join(' '.join(f'{cityT[4 * i + j] - actT[4 * i + j]:+.2f}' for j in T) for i in T))
    for g in ('green+oos', 'green'):
        dA = np.array([[S[('ACT', f, g, s)]['timeloss_agent'] - S[('ACT', f, 'none', s)]['timeloss_agent'] for s in SEL] for f in fleets])
        dF = np.array([[S[('ACT', f, g, s)]['fuel_agent'] / S[('ACT', f, 'none', s)]['fuel_agent'] - 1 for s in SEL] for f in fleets])
        ok4 = dA.mean() <= 0.5 and dF.mean() <= 0.02
        out.append(f"{'GG-4' if g == 'green+oos' else 'GG-5'} under ACT (training light), guard {g}: agent TL change {dA.mean():+.2f} s/veh (per fleet {[round(x, 2) for x in dA.mean(1)]}), "
                   f"agent fuel change {100 * dF.mean():+.2f} % (per fleet {[round(100 * x, 2) for x in dF.mean(1)]})" + (f" -> {'SUPPORTED' if ok4 else 'NOT SUPPORTED'}" if g == 'green+oos' else ''))
    res['GG2T'] = dict(city=cityT.tolist(), act=actT.tolist(), plain=plainT.tolist())
    txt = '\n'.join(out) + '\n'; (G / 'report.txt').write_text(txt); (G / 'report.json').write_text(json.dumps(res, indent=1)); print(txt)


if __name__ == '__main__':
    main()
