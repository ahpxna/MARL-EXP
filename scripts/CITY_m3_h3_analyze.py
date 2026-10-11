#!/usr/bin/env python3
"""M3-H3 analysis (registered decision rule).  For each situation (k, seed, t*, light) the branches br/<sid>_<opt>: full-episode E4 rows and
per-vehicle tripinfo.  LOCAL set = vehicles that were on the light's incoming lanes in [t*, t*+180] in ANY branch is approximated by vehicles
whose time loss or fuel differs from I0 in any option (exact under determinism: unaffected vehicles are bit-identical) -- reported with the
full-episode outcome as well.  Chaos floor = the spread of differences in situations with no vehicle affected beyond the light (KH-2) is
replaced by the PLACEBO check (must be exactly 0) plus the distribution of 'affected vehicle counts'.  Decision: OPPORTUNITY iff the best
option (agent fuel, with agent and human TL change <= +0.5 s/veh over the affected vehicles) beats I0 in >= 25 % of eligible situations and its
mean gain has a bootstrap lower bound > 0; predictable iff leave-one-seed-out AUC >= 0.65."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m3h3_20261004'; OPTS = ('Z', 'H5', 'H10', 'H15', 'P')


def load(sid, opt, seed):
    z = np.load(D / 'br' / f'{sid}_{opt}_veh_s{seed}.npz', allow_pickle=True); return {str(i): (bool(a), f, t) for i, a, f, t in zip(z['ids'], z['agent'], z['fuel'], z['tl'])}


if __name__ == '__main__':
    sit = json.loads((D / 'situations.json').read_text()); Rt = rows(D / 'br'); res = []; bad = []
    for i, s in enumerate(sit):
        sid = f'S{i:03d}'; base = load(sid, 'I0', s['seed']); pl = load(sid, 'PLACEBO', s['seed'])
        if any(pl[v][1] != base[v][1] or pl[v][2] != base[v][2] for v in base):
            bad.append(sid)
        h0 = json.loads((D / 'br' / f'{sid}_I0_h3.json').read_text())['per_seed'][str(s['seed'])]['prefix_hash']
        r = dict(sid=sid, **s, opt={})
        for o in OPTS:
            br = load(sid, o, s['seed']); hb = json.loads((D / 'br' / f'{sid}_{o}_h3.json').read_text())['per_seed'][str(s['seed'])]
            aff = [v for v in base if br[v][1] != base[v][1] or br[v][2] != base[v][2]]
            ag = [v for v in aff if base[v][0]]; hu = [v for v in aff if not base[v][0]]
            dfa = sum(br[v][1] - base[v][1] for v in ag); fa0 = sum(base[v][1] for v in ag) or 1.0
            r['opt'][o] = dict(n_aff=len(aff), n_ag=len(ag), dfuel_ag_pct_local=100 * dfa / fa0, dfuel_ag_abs=dfa,
                               dtl_ag=float(np.mean([br[v][2] - base[v][2] for v in ag])) if ag else 0.0, dtl_hu=float(np.mean([br[v][2] - base[v][2] for v in hu])) if hu else 0.0,
                               dtl_ag_sum=float(sum(br[v][2] - base[v][2] for v in ag)), dtl_hu_sum=float(sum(br[v][2] - base[v][2] for v in hu)),
                               full=dict(fuel_agent=100 * (Rt[f'{sid}_{o}'][s['seed']]['fuel_agent'] / Rt[f'{sid}_I0'][s['seed']]['fuel_agent'] - 1),
                                         tl=Rt[f'{sid}_{o}'][s['seed']]['timeloss'] - Rt[f'{sid}_I0'][s['seed']]['timeloss']),
                               prefix_ok=hb['prefix_hash'] == h0, applied=(hb.get('done') or {}).get('applied'))
        res.append(r)
    out = [f'== M3-H3 continuation opportunity: {len(res)} situations x {len(OPTS)} options (+ I0, PLACEBO); full-episode and affected-vehicle outcomes',
           f'  KH-1 PLACEBO == I0 (all vehicles bit-identical): {"PASS" if not bad else "FAIL " + str(bad[:5])}',
           f'  KH-3 prefix identical to t*: {"PASS" if all(r["opt"][o]["prefix_ok"] for r in res for o in OPTS) else "FAIL"}']
    for grp in ('eligible', 'random'):
        G = [r for r in res if r['group'] == grp]
        if not G:
            continue
        out.append(f'  -- {grp} situations (n {len(G)})')
        for o in OPTS:
            x = [r['opt'][o] for r in G]
            out.append(f'     {o:4s}: affected veh {np.mean([y["n_aff"] for y in x]):.1f} | agent fuel abs diff (sum over affected agents) mean {np.mean([y["dfuel_ag_abs"] for y in x]):+.1f} mg-units, '
                       f'improves in {np.mean([y["dfuel_ag_abs"] < 0 for y in x]):.2f} | agent TL sum {np.mean([y["dtl_ag_sum"] for y in x]):+.1f} s, human TL sum {np.mean([y["dtl_hu_sum"] for y in x]):+.1f} s | '
                       f'full-episode agent fuel % {np.mean([y["full"]["fuel_agent"] for y in x]):+.4f}, city TL {np.mean([y["full"]["tl"] for y in x]):+.4f}')
        best = []
        for r in G:
            ok = [(r['opt'][o]['dfuel_ag_abs'], o) for o in OPTS if r['opt'][o]['dtl_ag'] <= 0.5 and r['opt'][o]['dtl_hu'] <= 0.5]
            b = min(ok) if ok else (0.0, 'I0'); best.append((min(b[0], 0.0), b[1] if b[0] < 0 else 'I0'))
        gains = np.array([-b[0] for b in best]); share = np.mean([b[1] != 'I0' for b in best])
        rng = np.random.default_rng(0); bs = [rng.choice(gains, len(gains)).mean() for _ in range(2000)]
        out.append(f'     oracle-best (TL-constrained, includes I0): beats I0 in {share:.2f} of situations; mean agent-fuel gain {gains.mean():.1f} (bootstrap 5 % {np.percentile(bs, 5):.1f}); '
                   f'best options {dict(zip(*np.unique([b[1] for b in best], return_counts=True)))}')
        if grp == 'eligible':
            opp = share >= 0.25 and np.percentile(bs, 5) > 0
            out.append(f'  OPPORTUNITY (eligible): {"YES" if opp else "NO"}')
    (D / 'h3_results.json').write_text(json.dumps(res, indent=1, default=float)); t = '\n'.join(out) + '\n'; (D / 'report_m3h3.txt').write_text(t); print(t)
