#!/usr/bin/env python3
"""Report of wave 1 of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (written 23:3x EDT 03/10, before any wave-1 panel run).
E6 (closed loop, dev 901-904): ambiguous-copy share, EXACT_PACKET vs K1 and EXACT, decision rule.  E3 (7301-7332): gain vs Z per
arm, two-level crossed bootstrap (2000, rng 0), E3a / E3c.  E11 (pilot blocks): from-scratch arms vs the pilot's FT-mix / FT-new /
PCT (L-312) on DEV, new channel and old-channel level; Z parity with the pilot's Z rows.  INCOMPLETE on any missing cell."""
import argparse, json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); BASE = M / 'e3_wave_20261003'; PILOT = M / 'e3_adapt_pilot_20261003'


def rows(d, arm):
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
    return {r['episode']: r for r in json.loads((d / 'rows.json').read_text()) if r['arm'] == arm}


def boot(S, IDX, TS, f):
    rng = np.random.default_rng(0); bs = []
    for _ in range(2000):
        ss = rng.choice(S, len(S)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
        bs.append(np.mean([f(s, ii) for s in ss]))
    return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]


def gain(x, z, ii=None):
    return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100


def main(a):
    E = BASE / ('smoke_pipe' if a.smoke else ''); out = []; miss = []
    S10 = [0] if a.smoke else list(range(10)); S2 = [0] if a.smoke else [0, 1]
    dev = [9001, 9002] if a.smoke else [901, 902, 903, 904]; p3 = [9001, 9002] if a.smoke else list(range(7301, 7333))
    # ---- E6
    A6 = ['K1/PLAIN', 'U2/EXACT', 'U2/EXACT_PACKET']; eps6 = [f'seed{t}_load{h}' for t in dev for h in (8, 16)]; D6 = {}
    for s in S10:
        z = rows(E / f'E6C_s{s}', 'Z')
        for arm in A6:
            r = rows(E / f'E6C_s{s}', arm)
            if z is None or r is None or sorted(r) != sorted(eps6):
                miss.append(('E6', s, arm)); continue
            D6[(s, arm)] = [r[e] for e in eps6]; D6[(s, 'Z')] = [z[e] for e in eps6]
    if not any(k[0] == 'E6' for k in miss):
        rr = [x for s in S10 for x in D6[(s, 'U2/EXACT_PACKET')]]
        amb = sum(x['ambiguous'] for x in rr) / sum(x['entries'] for x in rr)
        q = lambda s, arm: np.array([x['queue_sum'] for x in D6[(s, arm)]], float)
        dp = [gain(q(s, 'U2/EXACT_PACKET'), q(s, 'Z')) - gain(q(s, 'K1/PLAIN'), q(s, 'Z')) for s in S10]
        de = [gain(q(s, 'U2/EXACT_PACKET'), q(s, 'Z')) - gain(q(s, 'U2/EXACT'), q(s, 'Z')) for s in S10]
        ok = amb <= 0.001 and abs(np.mean(dp)) <= 0.05
        out.append(f'== E6 (closed loop, dev {dev[0]}-{dev[-1]} x 8/16, seeds {S10}): ambiguous share {amb:.6f}; EXACT_PACKET - K1 mean {np.mean(dp):+.4f} '
                   f'(per seed {np.round(dp, 3).tolist()}); EXACT_PACKET - EXACT mean {np.mean(de):+.4f}; mismatched steps vs K1 '
                   f"{sum(x['lock_mismatch_steps'] or 0 for x in rr)}; missing {sum(x['missing'] for x in rr)} of {sum(x['entries'] for x in rr)}")
        out.append(f"   decision: {'EXACT_PACKET replaces EXACT in E7 with no other change' if ok else 'E7 uses EXACT_PACKET; the gap to EXACT is the cost of 4-bit timestamps'}")
    # ---- E3
    A3 = ['K1/PLAIN', 'U1/PLAIN', 'U1/EMU_OLDER', 'U1/EMU_ABSENT', 'U1/EMU_FRESH']; eps3 = [f'seed{t}_load{h}' for t in p3 for h in (8, 16)]
    TS = sorted({e.split('_')[0] for e in eps3}); IDX = {u: [i for i, e in enumerate(eps3) if e.startswith(u + '_')] for u in TS}; Q = {}; C3 = {}
    for s in S10:
        for arm in ['Z'] + A3:
            r = rows(E / f'E3_s{s}', arm)
            if r is None or sorted(r) != sorted(eps3):
                miss.append(('E3', s, arm)); continue
            Q[(s, arm)] = np.array([r[e]['queue_sum'] for e in eps3], float); C3[(s, arm)] = [r[e] for e in eps3]
    if not any(k[0] == 'E3' for k in miss):
        g = lambda s, arm, ii=None: gain(Q[(s, arm)], Q[(s, 'Z')], ii)
        st = lambda f: (float(np.mean([f(s, None) for s in S10])), boot(S10, IDX, TS, f), int(sum(f(s, None) > 0 for s in S10)))
        fmt = lambda x: f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}] ({x[2]}/{len(S10)} > 0)'
        out.append(f'== E3 (panel {p3[0]}-{p3[-1]} x 8/16, seeds {S10}): gain vs Z')
        T = {arm: st(lambda s, ii, arm=arm: g(s, arm, ii)) for arm in A3}
        for arm in A3:
            extra = ''
            if 'EMU' in arm:
                rr = [x for s in S10 for x in C3[(s, arm)]]; extra = f" | missing {sum(x['missing'] for x in rr) / sum(x['entries'] for x in rr):.3f}, ambiguous {sum(x['ambiguous'] for x in rr)}"
            out.append(f'{arm} | {fmt(T[arm])}{extra}')
        D = lambda x, y: st(lambda s, ii: g(s, x, ii) - g(s, y, ii))
        e3a = D('U1/EMU_FRESH', 'U1/EMU_OLDER'); hz = T['K1/PLAIN'][0] - T['U1/PLAIN'][0]
        out.append(f"E3a EMU_FRESH - EMU_OLDER {fmt(e3a)} -> {'SUPPORTED' if e3a[1][0] > 0 else 'NOT SUPPORTED'}")
        out.append(f"E3b (exploratory) EMU_ABSENT - EMU_OLDER {fmt(D('U1/EMU_ABSENT', 'U1/EMU_OLDER'))}; vs PLAIN: " +
                   ', '.join(f"{x} {fmt(D(x, 'U1/PLAIN'))}" for x in ('U1/EMU_OLDER', 'U1/EMU_ABSENT', 'U1/EMU_FRESH')))
        rec = {x: (T[x][0] - T['U1/PLAIN'][0]) / hz for x in ('U1/EMU_OLDER', 'U1/EMU_ABSENT', 'U1/EMU_FRESH')}
        out.append(f"E3c no emulator arm recovers >= 50 % of the CK1 hazard ({hz:+.2f}): {({k: round(v, 2) for k, v in rec.items()})} -> "
                   f"{'SUPPORTED' if all(v < 0.5 for v in rec.values()) else 'NOT SUPPORTED'}")
    # ---- E11
    buds = [8, 16] if a.smoke else [8, 16, 40, 80]; sel = [9001] if a.smoke else list(range(5701, 5717)); devb = [9002] if a.smoke else list(range(5717, 5749))
    pdir = PILOT / ('smoke_pipe' if a.smoke else ''); G = {}
    def gblk(qd, zd, blk):
        e = [f'seed{t}_load{h}' for t in blk for h in (8, 16)]
        return -(sum(qd[x]['queue_sum'] for x in e) / sum(zd[x]['queue_sum'] for x in e) - 1) * 100
    for s in S2:
        z = rows(E / f'E11Z_s{s}', 'Z'); zp = rows(pdir / f'Z_s{s}', 'Z')
        if z is None or zp is None:
            miss.append(('E11', s, 'Z')); continue
        assert all(abs(z[e]['queue_sum'] - zp[e]['queue_sum']) < 1e-6 for e in z), 'E11 Z differs from the pilot Z'
        for K in (0, 1):
            pp = rows(pdir / f'E_PARENT_s{s}_B0_K{K}', 'PLAIN')
            if pp is None:
                miss.append(('E11', s, 'PARENT')); continue
            G[('PARENT', s, 0, K)] = gblk(pp, z, devb)
            for b in buds:
                for arm in ('SCRATCH_NEW', 'SCRATCH_MIX', 'SCRATCH_MIX_T'):
                    r = rows(E / f'E11E_{arm}_s{s}_B{b}_K{K}', 'PLAIN')
                    if r is None:
                        miss.append(('E11', s, arm, b, K)); continue
                    G[(arm, s, b, K)] = gblk(r, z, devb)
                for arm in ('FTMIX', 'FTNEW', 'PCT'):
                    r = rows(pdir / f'E_{arm}_s{s}_B{b}_K{K}', 'PLAIN')
                    if r is None:
                        miss.append(('E11', s, arm, b, K)); continue
                    G[(arm, s, b, K)] = gblk(r, z, devb)
    if not any(k[0] == 'E11' for k in miss):
        out.append(f'== E11 (DEV {devb[0]}-{devb[-1]}): NEW-channel gain / OLD-channel gain (parent new, old in brackets)')
        for s in S2:
            out.append(f"seed {s} (parent new {G[('PARENT', s, 0, 0)]:+.2f}, old {G[('PARENT', s, 0, 1)]:+.2f})")
            for arm in ('SCRATCH_NEW', 'SCRATCH_MIX', 'SCRATCH_MIX_T', 'FTNEW', 'FTMIX', 'PCT'):
                out.append(f'  {arm} | ' + ' | '.join(f'B={b}: {G[(arm, s, b, 0)]:+.2f} / {G[(arm, s, b, 1)]:+.2f}' for b in buds))
        ok = all(G[('FTMIX', s, b, 0)] - G[('SCRATCH_MIX', s, b, 0)] > 0 for s in S2 for b in buds if b <= 40)
        out.append(f"E11 FT-mix (warm) - SCRATCH_MIX > 0 on NEW at every B <= 40 on every seed: "
                   f"{[(s, b, round(G[('FTMIX', s, b, 0)] - G[('SCRATCH_MIX', s, b, 0)], 2)) for s in S2 for b in buds if b <= 40]} -> {'SUPPORTED' if ok else 'NOT SUPPORTED'}")
    if miss:
        out.insert(0, f'INCOMPLETE parts: {miss[:10]} ({len(miss)} missing); verdicts shown only for complete parts')
    (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
