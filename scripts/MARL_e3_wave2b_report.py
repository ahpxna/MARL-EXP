#!/usr/bin/env python3
"""Report of wave 2b (E2 data factorial + UNI, E10 PAIRED v2) of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (written 23:5x EDT 03/10,
before any wave-2b run).  New-channel (iid) and old-channel (K1) gain vs Z on the adaptation pilot's DEV block (5717-5748), per seed,
at iteration levels L = 1 / 2 / 5 / 10 (the pilot's budgets 8 / 16 / 40 / 80 for FT-mix / PCT / PAIRED / A0, whose rows are reused).
Registered contrasts (E2): O-I - S-I = FTMIX - SI (old-data occupancy), S-I - S-P = SI - A0 (pairing at equal views),
O-P - S-P = OP - A0 (which policy drives the paired trajectories), O-I - O-P = FTMIX - OP, PAIRED - UNI (h vs a weight shift).
E10 GO at L = 5 on both seeds: V2D - FTMIX > +1.0, V2D - PCT > 0, V2D old drop <= 0.5.  INCOMPLETE on any missing cell."""
import argparse, json
from pathlib import Path

M = Path('research/marl_budget'); PIL = M / 'e3_adapt_pilot_20261003'; W2B = M / 'e3_wave_20261003'
BUD = {1: 8, 2: 16, 5: 40, 10: 80}


def rows(d, arm):
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
    return {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['arm'] == arm}


def main(a):
    E = W2B / ('smoke_pipe/w2b' if a.smoke else 'w2b'); P = PIL / ('smoke_pipe' if a.smoke else '')
    seeds = [0] if a.smoke else [0, 1]; LV = [1, 2] if a.smoke else [1, 2, 5, 10]; dev = [9002] if a.smoke else list(range(5717, 5749))
    eps = [f'seed{t}_load{h}' for t in dev for h in (8, 16)]; G = {}; miss = []

    def gn(q, z):
        return -(sum(q[e] for e in eps) / sum(z[e] for e in eps) - 1) * 100
    for s in seeds:
        z = rows(P / f'Z_s{s}', 'Z')
        if z is None:
            miss.append(('Z', s)); continue
        for K in (0, 1):
            pp = rows(P / f'E_PARENT_s{s}_B0_K{K}', 'PLAIN')
            if pp is None:
                miss.append(('PARENT', s, K)); continue
            G[('PARENT', s, 0, K)] = gn(pp, z)
            for L in LV:
                for arm in ('FTMIX', 'PCT', 'PAIRED', 'A0'):
                    q = rows(P / f'E_{arm}_s{s}_B{BUD[L]}_K{K}', 'PLAIN')
                    if q is None:
                        miss.append((arm, s, L, K)); continue
                    G[(arm, s, L, K)] = gn(q, z)
                for arm in ('SI', 'OP', 'UNI', 'V2S', 'V2D'):
                    q = rows(E / f'E_{arm}_s{s}_L{L}_K{K}', 'PLAIN')
                    if q is None:
                        miss.append((arm, s, L, K)); continue
                    G[(arm, s, L, K)] = gn(q, z)
    out = [f'== wave 2b (E2 / E10), DEV {dev[0]}-{dev[-1]} x 8/16, seeds {seeds}: NEW gain / OLD drop from the parent']
    if miss:
        out.append(f'INCOMPLETE: {miss[:8]} ({len(miss)})'); (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    drop = lambda arm, s, L: G[('PARENT', s, 0, 1)] - G[(arm, s, L, 1)]
    for s in seeds:
        out.append(f"seed {s} (parent new {G[('PARENT', s, 0, 0)]:+.2f}, old {G[('PARENT', s, 0, 1)]:+.2f})")
        for arm in ('FTMIX', 'PCT', 'PAIRED', 'A0', 'SI', 'OP', 'UNI', 'V2S', 'V2D'):
            out.append(f'  {arm} | ' + ' | '.join(f"L{L}: {G[(arm, s, L, 0)]:+.2f} / {drop(arm, s, L):+.2f}" for L in LV))
    d = lambda x, y, L: [round(G[(x, s, L, 0)] - G[(y, s, L, 0)], 2) for s in seeds]
    for L in LV:
        out.append(f'-- L{L} (new-channel differences per seed): ' + '; '.join(f'{lab} {x}-{y} {d(x, y, L)}' for lab, x, y in (
            ('old-data occupancy', 'FTMIX', 'SI'), ('pairing at equal views', 'SI', 'A0'), ('driver of paired trajectories', 'OP', 'A0'),
            ('pairing under old occupancy', 'FTMIX', 'OP'), ('h vs weight shift', 'PAIRED', 'UNI'), ('dynamic vs static h', 'V2D', 'V2S'))))
    Lg = 5 if 5 in LV else LV[-1]
    c1 = all(v > 1.0 for v in d('V2D', 'FTMIX', Lg)); c2 = all(v > 0 for v in d('V2D', 'PCT', Lg)); c3 = all(drop('V2D', s, Lg) <= 0.5 for s in seeds)
    out.append(f"E10 GO at L{Lg}: V2D - FTMIX {d('V2D', 'FTMIX', Lg)} (> +1.0: {c1}); V2D - PCT {d('V2D', 'PCT', Lg)} (> 0: {c2}); V2D old drop "
               f"{[round(drop('V2D', s, Lg), 2) for s in seeds]} (<= 0.5: {c3}) -> {'GO (confirmation on 7601-7664)' if c1 and c2 and c3 else 'NO-GO'}")
    (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
