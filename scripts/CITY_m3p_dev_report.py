#!/usr/bin/env python3
"""M3′ DEV report (PROTOCOL_CITY_M3P §3-4; written before any DEV row).  Cube [k, dev fleet, traffic 15] vs R (RL-H:k + unavailable rows of the
M3 DEV screen, producer CITY_eval_m3: identity P1).  Tier 1: RPC-receiver M3-1 superiority + all M3-2 constraints AND agent-fuel superiority vs
the best comparator of M3 DEV among W-c (5, 10) and B-ETA (10) (best = lowest fuel point).  Tier 2: receiver vs eta, receiver vs random.
Also M3-4clean (RPC + shadow vs RL-H + σ*), M3-3clean (RPC + fleet vs RPC + shadow), commitments / violations."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
B = Path(__file__).resolve().parents[1] / 'research/city_sim'; S = [100, 101, 102, 103, 104] + list(range(200, 210)); KS, FL = (0, 1), ('s13', 's113')
if __name__ == '__main__':
    Rp, Rm = rows(B / 'm3p_20261004/dev'), rows(B / 'm3_20261004/dev'); dr = R.draws((2, 2, len(S))); out = ['== M3′ RPC DEV screen (light seeds 0, 1 x dev fleets s13, s113 x 15 DEV traffic)']
    def g(Rt, t):
        if t not in Rt or sorted(Rt[t]) != S:
            raise SystemExit(f'INCOMPLETE {t}')
        return Rt[t]
    def cube(F, Bf, key, pct):
        c = np.zeros((2, 2, len(S)))
        for i, k in enumerate(KS):
            for j, fl in enumerate(FL):
                f, b = F(k, fl), Bf(k, fl); c[i, j] = [100 * (f[s][key] / b[s][key] - 1) if pct else f[s][key] - b[s][key] for s in S]
        return R.crossed(c, dr) + (float(np.percentile([c[np.ix_(*ix)].mean() for ix in dr], 5)),)
    fmt = lambda x: f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}] (up {x[2]:+.2f})'
    Rr = lambda k, fl: g(Rm, f'R_k{k}_{fl}'); res = {}
    for trig in ('receiver', 'eta', 'random'):
        F = lambda k, fl, t=trig: g(Rp, f'RPC_{t}_k{k}_{fl}'); Sh = lambda k, fl, t=trig: g(Rp, f'RPC_{t}_k{k}_{fl}_shadow'); Rs = lambda k, fl: g(Rm, f'R_k{k}_sig')
        x = {key: cube(F, Rr, key, key == 'fuel_agent') for key in ('fuel_agent', 'timeloss', 'timeloss_agent', 'timeloss_human')}
        tel = np.mean([F(k, fl)[s]['teleports'] for k in KS for fl in FL for s in S]); tel0 = np.mean([Rr(k, fl)[s]['teleports'] for k in KS for fl in FL for s in S])
        unf = sum(F(k, fl)[s]['unfinished'] for k in KS for fl in FL for s in S); unf0 = sum(Rr(k, fl)[s]['unfinished'] for k in KS for fl in FL for s in S)
        feas = all(x[k][2] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel <= tel0 + 0.1 and unf <= unf0; res[trig] = (x, feas)
        c4 = cube(Sh, Rs, 'timeloss', False); c3 = cube(F, Sh, 'fuel_agent', True)
        sc = [json.loads((B / f'm3p_20261004/dev/RPC_{trig}_k{k}_{fl}_m3p.json').read_text())['per_seed'] for k in KS for fl in FL]
        com = sum(v['commits'] for s_ in sc for v in s_.values()); ve = sum(v['viol_end'] + v['viol_onset'] for s_ in sc for v in s_.values())
        out.append(f"  RPC-{trig:8s} M3-1 fuel % {fmt(x['fuel_agent'])} | city TL {fmt(x['timeloss'])} agent {fmt(x['timeloss_agent'])} human {fmt(x['timeloss_human'])} "
                   f"| tele {tel:.2f} ({tel0:.2f}) -> {'FEASIBLE' if feas else 'infeasible'} | M3-4clean city TL {fmt(c4)} | M3-3clean fleet fuel % {fmt(c3)} | commits {com}, violations {ve}")
    comps = {}
    for arm in ('WC5', 'WC10', 'B10'):
        comps[arm] = cube(lambda k, fl, a=arm: g(Rm, f'{a}_k{k}_{fl}'), Rr, 'fuel_agent', True)[0]
    best = min(comps, key=comps.get); xr, fr = res['receiver']
    vb = cube(lambda k, fl: g(Rp, f'RPC_receiver_k{k}_{fl}'), lambda k, fl: g(Rm, f'{best}_k{k}_{fl}'), 'fuel_agent', True)
    t1 = xr['fuel_agent'][2] < 0 and fr and vb[2] < 0
    out.append(f'  best M3 comparator on DEV fuel: {best} ({comps[best]:+.2f} %); RPC-receiver vs {best}: fuel % {fmt(vb)}')
    out.append(f'  TIER 1 (method helps): {"PASS" if t1 else "FAIL"}')
    for ab in ('eta', 'random'):
        v = cube(lambda k, fl: g(Rp, f'RPC_receiver_k{k}_{fl}'), lambda k, fl, a=ab: g(Rp, f'RPC_{a}_k{k}_{fl}'), 'fuel_agent', True)
        out.append(f'  tier 2: receiver vs {ab}: fuel % {fmt(v)} -> {"superior" if v[2] < 0 else "advantage not shown"}')
    t = '\n'.join(out) + '\n'; (B / 'm3p_20261004/report_m3p_dev.txt').write_text(t); print(t)
