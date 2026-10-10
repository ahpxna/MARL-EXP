#!/usr/bin/env python3
"""Report of PROTOCOL_E3_P2_NESTING_20261003.md (protocol 18:3x EDT 03/10; report written before any panel run).
Gain vs Z per receiver x channel/arm (two-level crossed bootstrap, 2000 draws, rng 0), paired differences, N1-N5 verdicts,
missing-entry shares of the emulator on U1, bytes delivered and emulator buffer.  Usage: MARL_e3_p2_nesting_report.py [--smoke]"""
import argparse, json
from pathlib import Path
import numpy as np

BASE = Path('research/marl_budget/e3_p2_nesting_20261003')
ARMS = {'CK1': ['K1/PLAIN', 'U1/PLAIN', 'U2/PLAIN', 'U2/EXACT', 'U1/EXACT'], 'Cage': ['K1/PLAIN', 'U1/PLAIN', 'U2/PLAIN'],
        'MIX': ['K1/PLAIN', 'U1/PLAIN', 'U2/PLAIN']}
TAG = {'CK1': 'relayCK1_st', 'Cage': 'relayCage_st', 'MIX': 'relayMIX_st'}


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def main(a):
    D = BASE / ('smoke_pipe' if a.smoke else '') / '4x4'; panel = (9001, 9002) if a.smoke else tuple(range(5401, 5465))
    seeds = [0] if a.smoke else list(range(10)); eps = [f'seed{t}_load{h}' for t in panel for h in (8, 16)]
    TS = sorted({e.split('_')[0] for e in eps}); IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in TS}

    def rows(d, arm):
        if not (d / 'manifest.json').exists():
            return None
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
        r = {x['episode']: x for x in json.loads((d / 'rows.json').read_text()) if x['arm'] == arm}
        assert sorted(r) == sorted(eps), (d, arm, len(r))
        return [r[e] for e in eps]
    Z = {}; R = {}; RAW = {}
    for s in seeds:
        z = rows(D / f'Z_s{s}', 'Z')
        if z is not None:
            Z[s] = np.array([x['queue_sum'] for x in z], float)
        for rc, arms in ARMS.items():
            for arm in arms:
                rr = rows(D / f'NE_{TAG[rc]}_s{s}', arm)
                if rr is not None:
                    R[(rc, s, arm)] = np.array([x['queue_sum'] for x in rr], float); RAW[(rc, s, arm)] = rr
    S = [s for s in seeds if s in Z and all((rc, s, arm) in R for rc, arms in ARMS.items() for arm in arms)]
    out = [f'== P2 nesting panel {panel[0]}-{panel[-1]} x 8/16 (4x4): complete seeds {S}']
    if not S:
        print('\n'.join(out)); return
    g = lambda rc, s, arm, ii=None: gain(R[(rc, s, arm)], Z[s], ii)

    def boot(f):
        rng = np.random.default_rng(0); bs = []
        for _ in range(2000):
            ss = rng.choice(S, len(S)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
            bs.append(np.mean([f(s, ii) for s in ss]))
        return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]

    def st(f):
        per = [f(s, None) for s in S]
        return dict(mean=float(np.mean(per)), ci=boot(f), pos=int(sum(x > 0 for x in per)), n=len(S))
    fmt = lambda x: f"{x['mean']:+.2f} [{x['ci'][0]:+.2f}, {x['ci'][1]:+.2f}] ({x['pos']}/{x['n']} > 0)"
    T = {(rc, arm): st(lambda s, ii, rc=rc, arm=arm: g(rc, s, arm, ii)) for rc, arms in ARMS.items() for arm in arms}
    out.append('-- gain vs Z, %')
    for (rc, arm), x in T.items():
        out.append(f'{rc} | {arm} | {fmt(x)}')
    dif = lambda rc, x, y: st(lambda s, ii: g(rc, s, x, ii) - g(rc, s, y, ii))
    N3a = dif('CK1', 'U1/EXACT', 'U1/PLAIN'); N3b = dif('CK1', 'U1/EXACT', 'K1/PLAIN'); N4 = dif('CK1', 'U2/PLAIN', 'K1/PLAIN')
    N5 = dif('Cage', 'U2/PLAIN', 'U1/PLAIN'); hz1 = dif('CK1', 'U1/PLAIN', 'K1/PLAIN'); ex2 = dif('CK1', 'U2/EXACT', 'K1/PLAIN')
    miss = {s: sum(r['missing'] for r in RAW[('CK1', s, 'U1/EXACT')]) / sum(r['entries'] for r in RAW[('CK1', s, 'U1/EXACT')]) for s in S}
    locked = all(r['locked_to_K1'] for s in S for r in RAW[('CK1', s, 'U2/EXACT')])
    same = all(np.array_equal(R[('CK1', s, 'U2/EXACT')], R[('CK1', s, 'K1/PLAIN')]) for s in S)
    out.append('-- paired differences (same receiver checkpoint, same episodes)')
    for lab, x in (('CK1 U1/PLAIN - K1/PLAIN (the deployed hazard)', hz1), ('CK1 U2/PLAIN - K1/PLAIN (nested upgrade)', N4),
                   ('CK1 U1/EXACT - U1/PLAIN', N3a), ('CK1 U1/EXACT - K1/PLAIN', N3b), ('CK1 U2/EXACT - K1/PLAIN', ex2),
                   ('Cage U2/PLAIN - U1/PLAIN', N5), ('MIX U2/PLAIN - U1/PLAIN', dif('MIX', 'U2/PLAIN', 'U1/PLAIN'))):
        out.append(f'{lab}: {fmt(x)}')
    mm = [r for s in S for r in RAW[('CK1', s, 'U2/EXACT')]]
    out.append(f"-- N1 detail (Amendment 1): U2/EXACT episodes differing from K1/PLAIN: {sum(r.get('lock_mismatch_steps', 0) > 0 for r in mm)} of {len(mm)} "
               f"(mismatched steps {sum(r.get('lock_mismatch_steps', 0) for r in mm)}; first steps {sorted({r.get('first_mismatch') for r in mm if r.get('first_mismatch') is not None})}; "
               f"queue differs in {sum(not r.get('equal_to_K1', True) for r in mm)})")
    out.append(f"-- emulator on U1: missing-entry share per seed {[round(v, 3) for v in miss.values()]} (older substitutes / missing: "
               f"{sum(r['older_substitute'] for s in S for r in RAW[('CK1', s, 'U1/EXACT')])} / {sum(r['missing'] for s in S for r in RAW[('CK1', s, 'U1/EXACT')])})")
    for rc in ARMS:
        out.append(f'-- {rc} costs: ' + '; '.join(
            f"{arm}: {np.mean([r['delivered'] for s in S for r in RAW[(rc, s, arm)]]) * 25:.0f} B delivered/episode, "
            f"{np.mean([r['seconds'] for s in S for r in RAW[(rc, s, arm)]]):.3f} s, buffer {np.mean([r['buffer'] for s in S for r in RAW[(rc, s, arm)]]):.0f}"
            for arm in ARMS[rc]))
    V = dict(N1=locked and same, N2=all(v >= 0.10 for v in miss.values()), N3=N3a['ci'][0] > 0 and N3b['ci'][1] < 0,
             N4=N4['ci'][1] < 0, N5=N5['ci'][1] < 0)
    words = {'N1': 'U2/EXACT == K1/PLAIN on every episode (locked step by step)', 'N2': 'U1 missing-entry share >= 10 % on every seed',
             'N3': 'U1/EXACT partial: > U1/PLAIN (lower > 0) and < K1/PLAIN (upper < 0)', 'N4': 'nested upgrade still hurts: U2/PLAIN < K1/PLAIN (upper < 0)',
             'N5': 'nesting costs the adaptive-trained receiver: Cage U2 < U1 (upper < 0)'}
    out.append('-- verdicts (PROTOCOL_E3_P2_NESTING_20261003 §3)')
    out += [f"{k} {words[k]} -> {'SUPPORTED' if v else 'NOT SUPPORTED'}" for k, v in V.items()]
    d = BASE / ('smoke_pipe' if a.smoke else ''); (d / 'report.txt').write_text('\n'.join(out) + '\n')
    (d / 'report.json').write_text(json.dumps(dict(seeds=S, table={f'{rc}|{arm}': x for (rc, arm), x in T.items()},
                                                   diffs=dict(hazard_U1=hz1, N3a=N3a, N3b=N3b, N4=N4, N5=N5, exact_U2=ex2), missing=miss,
                                                   verdicts=V), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o)))
    print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
