#!/usr/bin/env python3
"""Report for PROTOCOL_E3_RELAY_ROTATION_20260930.md (panel 2601-2664 x 8/16; ledger L-173).

PRIMARY, per seed s and condition c in {iid, cap4, low}: relay_st_s s with the agefirst order vs distill_none_s s, ratio of
summed waiting minus 1, 95 % bootstrap over traffic seeds (both headways together), 4000 draws, seed 0.  SUPPORTED only if
all 6 upper bounds are < 0; INCOMPLETE if any cell is missing.  Secondary rows are printed as measured.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from MARL_e3_music_report import paired

E = Path('research/marl_budget/e3_relayrot_panel_20260930')
COND = {'iid': ('iid', 'prefix'), 'cap4': ('iid', 'cap4'), 'low': ('low', 'prefix')}


def rows(tag, rule):
    p = E / tag / 'rows.json'
    if not (E / tag / 'manifest.json').exists():
        return None
    out = {r['episode']: r for r in json.loads(p.read_text()) if r.get('rule') == rule}
    return out or None


def arm(s, order, c):
    cap, rule = COND[c]
    return rows(f'relay_st_s{s}_{order}_{cap}', rule)


def main(a):
    rep = {}; lines = []; prim = []
    for s in a.seeds:
        st = rows(f'ref_distill_none_s{s}', 'none'); sn = rows(f'ref_set_none_s{s}', 'none'); bb = rows(f'bb_set_full_s{s}', 'prefix')
        mq = rows('ref_maxq', 'none')
        R = rep[f's{s}'] = {}
        lines.append(f'== seed {s}   (0-byte student mean waiting {np.mean([r["queue_sum"] for r in st.values()]):.1f})' if st else f'== seed {s}: student rows missing')
        for c in COND:
            A = arm(s, 'agefirst', c); P = arm(s, 'prefix', c)
            cell = paired(A, st) if (A and st) else None
            prim.append(cell); R[f'PRIMARY {c}: relay+agefirst vs 0-byte student'] = cell
            if A:
                R[f'{c} bytes/episode agefirst'] = round(float(np.mean([r['bytes'] for r in A.values()])), 1)
            if P and st:
                R[f'{c}: relay+prefix order vs 0-byte student'] = paired(P, st)
            if A and P:
                R[f'{c}: agefirst - prefix order'] = paired(A, P)
            if A and sn:
                R[f'{c}: relay+agefirst vs set_none'] = paired(A, sn)
            if A and mq:
                R[f'{c}: relay+agefirst vs maxq'] = paired(A, mq)
        if bb and st:
            R['BYTEBUDGET (27 B/step) vs 0-byte student'] = paired(bb, st)
        if st and sn:
            R['0-byte student vs set_none'] = paired(st, sn)
        for k, v in R.items():
            lines.append(f'   {k:52s} ' + (f'{v[0]:+6.2f} % [{v[1]:+6.2f}, {v[2]:+6.2f}]' if isinstance(v, tuple) else str(v)))
    verdict = 'INCOMPLETE' if any(p is None for p in prim) else ('SUPPORTED' if all(p[2] < 0 for p in prim) else 'NOT SUPPORTED')
    rep['primary_verdict'] = verdict; rep['primary_cells'] = prim
    lines.append(f'PRIMARY (all 6 cells: 2 seeds x iid / cap4 / low, upper 95 % < 0): {verdict}')
    print('\n'.join(lines))
    if a.out:
        Path(a.out).write_text(json.dumps(rep, indent=1)); Path(a.out).with_suffix('.txt').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1])
    p.add_argument('--out', default='research/marl_budget/e3_relayrot_panel_report_20260930.json')
    main(p.parse_args())
