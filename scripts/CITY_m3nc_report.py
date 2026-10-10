#!/usr/bin/env python3
"""M3-NC report (PROTOCOL_CITY_M3_NEG_CONFIRM_20261004; written before any M3-NC run).  Dir m3nc_20261004/eval, fresh 510-529, lights t4..t8,
frozen fleets L11_s213..s513, crossed [light 5, fleet 4, traffic 20], R.crossed 2 000 draws.  Per primary arm (WC5, RPC): M3-1 agent fuel % vs R
(NEGATIVE CONFIRMED iff one-sided lower > 0; NOT SHOWN BETTER iff upper >= 0; positive iff upper < 0), M3-2 TL (reported), M3-4clean light
cost = shadow - R (agent fuel %, city TL), M3-3clean fleet contribution = fleet - shadow (agent fuel %).  Reason named iff light-cost lower > 0
and fleet-contribution upper < 0.  WC5-c descriptive."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m3nc_20261004/eval'; S = list(range(510, 530)); LT = (4, 5, 6, 7, 8); FL = (213, 313, 413, 513)


def cube(Rt, a, b, key, pct):
    """a(l, f), b(l, f) -> tags; array [light, fleet, traffic]."""
    return np.array([[[100 * (Rt[a(l, f)][s][key] / Rt[b(l, f)][s][key] - 1) if pct else Rt[a(l, f)][s][key] - Rt[b(l, f)][s][key] for s in S] for f in FL] for l in LT])


def lo(c, dr):
    return float(np.percentile([c[np.ix_(*ix)].mean() for ix in dr], 5))


def fmt(c, dr):
    p, ci, up = R.crossed(c, dr); return p, ci, up, lo(c, dr), f'{p:+.2f} [{ci[0]:+.2f}, {ci[1]:+.2f}] (lo {lo(c, dr):+.2f}, up {up:+.2f})'


if __name__ == '__main__':
    if '--dir' in sys.argv:                                  # test hook: --dir <eval dir> --seeds <s ...>
        D = Path(sys.argv[sys.argv.index('--dir') + 1]); S = [int(x) for x in sys.argv[sys.argv.index('--seeds') + 1:]]
    Rt = rows(D); dr = R.draws((len(LT), len(FL), len(S)))
    need = [f'R_t{l}' for l in LT] + [f'WC5sig_t{l}' for l in LT] + [f'{a}_t{l}_{f}' for a in ('WC5', 'RPC', 'RPCsh', 'WC5c') for l in LT for f in FL]
    bad = [t for t in need if t not in Rt or sorted(Rt[t]) != S]
    if bad:
        sys.exit(f'INCOMPLETE {bad}')
    out = ['== M3-NC: light-side negative confirmation, fresh 510-529 x lights t4-t8 x frozen R10 fleets s213-s513 (crossed); vs R (no SPaT, fleet = σ*)']
    Rb = lambda l, f: f'R_t{l}'; verdicts = {}
    for name, arm, sh in (('WC5', 'WC5', lambda l, f: f'WC5sig_t{l}'), ('RPC-receiver', 'RPC', lambda l, f: f'RPCsh_t{l}_{f}'), ('WC5-c [descriptive]', 'WC5c', None)):
        A = lambda l, f, a=arm: f'{a}_t{l}_{f}'
        m1 = fmt(cube(Rt, A, Rb, 'fuel_agent', True), dr); tl = {k: fmt(cube(Rt, A, Rb, k, False), dr) for k in ('timeloss', 'timeloss_agent', 'timeloss_human')}
        tel = np.mean([Rt[A(l, f)][s]['teleports'] for l in LT for f in FL for s in S]); tel0 = np.mean([Rt[f'R_t{l}'][s]['teleports'] for l in LT for s in S])
        v = 'NEGATIVE CONFIRMED' if m1[3] > 0 else ('POSITIVE (contradicts DEV; not a claim)' if m1[2] < 0 else 'NOT SHOWN BETTER')
        out.append(f'  {name}: M3-1 agent fuel % {m1[4]} -> {v}')
        out.append(f'      M3-2 city TL {tl["timeloss"][4]} | agent TL {tl["timeloss_agent"][4]} | human TL {tl["timeloss_human"][4]} | teleports {tel:.2f} ({tel0:.2f})')
        if sh is not None:
            lc = fmt(cube(Rt, sh, Rb, 'fuel_agent', True), dr); lct = fmt(cube(Rt, sh, Rb, 'timeloss', False), dr); fc = fmt(cube(Rt, A, sh, 'fuel_agent', True), dr)
            named = lc[3] > 0 and fc[2] < 0
            out.append(f'      M3-4clean light cost: agent fuel % {lc[4]}, city TL {lct[4]} | M3-3clean fleet contribution: agent fuel % {fc[4]} -> reason {"NAMED" if named else "NOT established"}')
            verdicts[arm] = (v, named)
        sc = [json.loads((D / f'{A(l, f)}_{"m3p" if arm == "RPC" else "m3"}.json').read_text()) for l in LT for f in FL]
        ps = [x for c in sc for x in c['per_seed'].values()]
        viol = sum(x.get('violations', 0) + x.get('viol_end', 0) + x.get('viol_onset', 0) for x in ps); com = sum(x.get('commits', 0) for x in ps)
        out.append(f'      commitments {com}, violations {viol}')
    both = all(verdicts[a][0] == 'NEGATIVE CONFIRMED' for a in ('WC5', 'RPC')); named = all(verdicts[a][1] for a in ('WC5', 'RPC'))
    out.append(f'  M3 LIGHT-SIDE NEGATIVE: {"CONFIRMED" if both else "NOT confirmed"}; reason {"NAMED for both" if named else "not named for both"}')
    t = '\n'.join(out) + '\n'; (D.parent / 'report_m3nc.txt').write_text(t); print(t)
