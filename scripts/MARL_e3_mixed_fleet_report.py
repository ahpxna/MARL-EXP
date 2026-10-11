#!/usr/bin/env python3
"""Report of PROTOCOL_E3_MIXED_FLEET_20261003.md (protocol 20:1x EDT 03/10; report written before any pilot run).
Per layout (D dispersed, C clustered): system gain vs ZTEAM and OLD- / NEW-group local gains (from the per-agent queue sums),
two-level crossed bootstrap (2000, rng 0) over actor seeds x traffic seeds, paired differences, bytes / buffer / runtime, the
GO rule of §6.  Every registered seed and arm is required (INCOMPLETE otherwise).  --smoke: seed 0, traffic 9001-9002."""
import argparse, json
from pathlib import Path
import numpy as np

BASE = Path('research/marl_budget/e3_mixed_fleet_20261003')
ARMS = ['U1/PLAIN', 'U2/PLAIN', 'U2/EMU_OLD', 'U1/FB_OLD', 'K1/ROLLBACK']; REFS = ['ALLOLD', 'ALLNEW']


def main(a):
    E = BASE / ('smoke_pipe' if a.smoke else ''); seeds = [0] if a.smoke else [0, 1, 2, 3, 4]
    panel = (9001, 9002) if a.smoke else tuple(range(5901, 5933)); eps = [f'seed{t}_load{h}' for t in panel for h in (8, 16)]
    TS = sorted({e.split('_')[0] for e in eps}); IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in TS}

    def load(d):
        if not (d / 'manifest.json').exists():
            return None
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
        return json.loads((d / 'rows.json').read_text())
    R = {}; RAW = {}; out = []; missing = []
    for s in seeds:
        ref = load(E / f'REF_s{s}')
        for lay in ('D', 'C'):
            mix = load(E / f'MIX_s{s}_{lay}')
            for arm in ['ZTEAM'] + REFS + ARMS:
                src = ref if arm in ['ZTEAM'] + REFS else mix
                if src is None:
                    missing.append((s, lay, arm)); continue
                rr = {r['episode']: r for r in src if r['arm'] == arm}
                if sorted(rr) != sorted(eps):
                    missing.append((s, lay, arm)); continue
                RAW[(s, lay, arm)] = [rr[e] for e in eps]
                R[(s, lay, arm)] = np.array([rr[e]['q_agents'] for e in eps], float)          # (episodes, agents)
    out.append(f'== mixed-version fleet pilot (4x4, OLD = CK1 at 50 %, NEW = Cage), seeds {seeds}, traffic {panel[0]}-{panel[-1]} x 8/16')
    if missing:
        out.append(f'INCOMPLETE: {missing[:8]}; no verdict'); (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    V = {}
    for lay in ('D', 'C'):
        O = RAW[(seeds[0], lay, 'U1/PLAIN')][0]['old']; N = [i for i in range(16) if i not in O]

        def g(s, arm, grp, ii=None):
            X = R[(s, lay, arm)]; Z = R[(s, lay, 'ZTEAM')]; cols = {'sys': list(range(16)), 'old': O, 'new': N}[grp]
            x = X[:, cols].sum(1); z = Z[:, cols].sum(1)
            return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100

        def boot(f):
            rng = np.random.default_rng(0); bs = []
            for _ in range(2000):
                ss = rng.choice(seeds, len(seeds)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
                bs.append(np.mean([f(s, ii) for s in ss]))
            return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]

        def st(f):
            per = [f(s, None) for s in seeds]
            return dict(mean=float(np.mean(per)), ci=boot(f), pos=int(sum(x > 0 for x in per)))
        fmt = lambda x: f"{x['mean']:+.2f} [{x['ci'][0]:+.2f}, {x['ci'][1]:+.2f}] ({x['pos']}/{len(seeds)} > 0)"
        out.append(f'-- layout {lay} (OLD agents {O})')
        out.append('arm | system | OLD group | NEW group | bytes delivered / episode | emulator buffer | flags / OLD decision | s / episode')
        T = {}
        for arm in ARMS + REFS:
            T[arm] = {grp: st(lambda s, ii, arm=arm, grp=grp: g(s, arm, grp, ii)) for grp in ('sys', 'old', 'new')}
            rr = [r for s in seeds for r in RAW[(s, lay, arm)]]
            fl = np.mean([r.get('flags', 0) for r in rr]) / (26 * len(O)) if arm == 'U1/FB_OLD' else 0.0
            out.append(f"{arm} | {fmt(T[arm]['sys'])} | {fmt(T[arm]['old'])} | {fmt(T[arm]['new'])} | {np.mean([r.get('delivered', 0) for r in rr]) * 25:.0f} | "
                       f"{np.mean([r.get('buffer', 0) for r in rr]):.0f} | {fl:.3f} | {np.mean([r.get('seconds', 0) for r in rr]):.3f}")
        D = lambda x, y, grp: st(lambda s, ii: g(s, x, grp, ii) - g(s, y, grp, ii))
        d1 = D('U2/EMU_OLD', 'U2/PLAIN', 'sys'); d2 = D('U2/EMU_OLD', 'U1/FB_OLD', 'sys'); d2o = D('U2/EMU_OLD', 'U1/FB_OLD', 'old')
        out.append(f"paired: EMU_OLD - U2/PLAIN system {fmt(d1)}; EMU_OLD - FB_OLD system {fmt(d2)}, OLD group {fmt(d2o)}")
        for y in ('U1/PLAIN', 'K1/ROLLBACK', 'ALLNEW', 'ALLOLD'):
            out.append(f"   (no verdict) EMU_OLD - {y}: system {fmt(D('U2/EMU_OLD', y, 'sys'))}, OLD {fmt(D('U2/EMU_OLD', y, 'old'))}, NEW {fmt(D('U2/EMU_OLD', y, 'new'))}")
        bytes_ok = np.mean([r['delivered'] for s in seeds for r in RAW[(s, lay, 'U2/EMU_OLD')]]) <= np.mean([r['delivered'] for s in seeds for r in RAW[(s, lay, 'U1/FB_OLD')]])
        c1 = d1['ci'][0] > 0; c2 = d2['ci'][0] > 0 or (d2o['mean'] > 0 and bytes_ok); c3 = T['U2/EMU_OLD']['new']['mean'] >= T['U1/PLAIN']['new']['mean'] - 0.5
        V[lay] = c1 and c2 and c3
        out.append(f"GO rule ({lay}): (1) EMU_OLD > U2/PLAIN lower > 0: {c1}; (2) EMU_OLD > FB_OLD lower > 0, or more OLD retention at no more bytes: {c2}; "
                   f"(3) NEW group >= U1/PLAIN - 0.5: {c3} -> {'GO' if V[lay] else 'NO-GO'}")
    out.append(f"pilot verdict per layout: {V} (GO opens a fresh multi-seed confirmation; it is not a benchmark win)")
    (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
