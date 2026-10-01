#!/usr/bin/env python3
"""Report of the LIFETIME-DEADLINE head on the development panel 901-964 x 8/16 (ledger L-178).
Per seed, condition (iid = prefix rule, cap4 = cap4 rule on iid capacities, low = prefix rule on low capacities) and D:
waiting, paired vs the prefix order and vs agefirst (the satrot rows of the same actor), and vs the 0-byte student.
Applies the reading rule written in scripts/RUN_marl_e3_deadline_dev.sh before the result.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent))
from MARL_e3_music_report import paired

E = Path('research/marl_budget/e3_deadline_dev_20260930'); SAT = Path('research/marl_budget/e3_satrot_eval_20260930')
C = Path('research/marl_budget/e3_codesign_eval_20260929')


def rows(p, rule):
    p = Path(p)
    if not (p.parent / 'manifest.json').exists():
        return None
    return {r['episode']: r for r in json.loads(p.read_text()) if r['rule'] == rule} or None


def main(a):
    rep = {}; L = []; cells = {}
    for s in a.seeds:
        st = rows(C / f'distill_none_s{s}/rows.json', 'none')
        for cond, cap, rule in [('iid', 'iid', 'prefix'), ('cap4', 'iid', 'cap4'), ('low', 'low', 'prefix')]:
            P = rows(SAT / f'relay_st_s{s}_prefix_{cap}/rows.json', rule); A = rows(SAT / f'relay_st_s{s}_agefirst_{cap}/rows.json', rule)
            wP = np.mean([r['queue_sum'] for r in P.values()]); wA = np.mean([r['queue_sum'] for r in A.values()])
            line = f's{s} {cond}: prefix {wP:.1f} ({paired(P, st)[0]:+.2f}% vs 0B), agefirst {wA:.1f} ({paired(A, st)[0]:+.2f}% vs 0B)'
            for d in a.D:
                X = rows(E / f'DL_s{s}_D{d}_{cap}/rows.json', rule)
                if X is None:
                    continue
                vp, va, vs = paired(X, P), paired(X, A), paired(X, st)
                man = json.loads((E / f'DL_s{s}_D{d}_{cap}/manifest.json').read_text())
                rep[f's{s}_{cond}_D{d}'] = dict(waiting=round(float(np.mean([r['queue_sum'] for r in X.values()])), 1), vs_prefix=vp, vs_agefirst=va, vs_student=vs,
                                               order_stats=man.get('order_stats'), mirror_checked_steps=man.get('mirror_checked_steps'))
                cells[(s, cond, d)] = (vp[0], va[0])
                line += f' | D{d}: vs P {vp[0]:+.2f} [{vp[1]:+.2f},{vp[2]:+.2f}], vs A {va[0]:+.2f} [{va[1]:+.2f},{va[2]:+.2f}], vs 0B {vs[0]:+.2f}'
            L.append(line)
    L.append('READING RULE (written before): for one D, both seeds: iid vs prefix <= +0.3; cap4 and low vs agefirst <= +0.3; better than min(prefix, agefirst) in >= 3 of 6 cells')
    for d in a.D:
        ok = []; better = 0; complete = True
        for s in a.seeds:
            for cond in ('iid', 'cap4', 'low'):
                if (s, cond, d) not in cells:
                    complete = False; continue
                vp, va = cells[(s, cond, d)]
                ok.append(vp <= 0.3 if cond == 'iid' else va <= 0.3)
                better += int(max(vp, va) < 0)          # better than BOTH orders (fixed 18:5x: was min, i.e. better than either)
        verdict = 'INCOMPLETE' if not complete else ('DOMINATES' if all(ok) and better >= 3 else 'does not dominate')
        L.append(f'  D{d}: conditions met {sum(ok)}/{len(ok)}, better than both in {better} cells -> {verdict}')
        rep[f'verdict_D{d}'] = verdict
    print('\n'.join(L)); Path(a.out).write_text(json.dumps(rep, indent=1)); Path(a.out).with_suffix('.txt').write_text('\n'.join(L) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1])
    p.add_argument('--D', nargs='+', default=['2', '3', '4', '6']); p.add_argument('--out', default='research/marl_budget/e3_deadline_dev_report_20260930.json')
    main(p.parse_args())
