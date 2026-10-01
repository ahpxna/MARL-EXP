#!/usr/bin/env python3
"""Report of the closed-loop theory checks (ledger L-176), development panel 901-964 x 8/16.

V-A  waiting vs beta (Paper-A repair mixture); beta = 0 and beta = 1 are the SATROT rows (prefix and agefirst orders,
     identical to eval v4 with mix0 / mix1, checked 8/8); each point is paired against beta = 0 and against the same-seed
     0-byte student (bootstrap by traffic seed).
V-S  waiting vs const K = 1..7 per actor configuration (relay + agefirst, relay + prefix order, stale-kept set_prefix,
     FO = set_full with a fresh-only receiver), paired against the 0-byte student; a frontier is called NON-MONOTONE when
     some K -> K+1 step raises waiting with the paired 95 % interval above +0 (more decoded packets make it worse).
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from MARL_e3_music_report import paired

E = Path('research/marl_budget/e3_theory_cl_20260930'); SAT = Path('research/marl_budget/e3_satrot_eval_20260930')
C = Path('research/marl_budget/e3_codesign_eval_20260929')


def rows(path, rule):
    p = Path(path)
    if not (p.parent / 'manifest.json').exists():
        return None
    return {r['episode']: r for r in json.loads(p.read_text()) if r['rule'] == rule} or None


def main(a):
    rep = {'V_A': {}, 'V_S': {}}; L = []
    for s in a.seeds:
        st = rows(C / f'distill_none_s{s}/rows.json', 'none')
        for cond, cap, rule in [('iid', 'iid', 'prefix'), ('cap4', 'iid', 'cap4'), ('low', 'low', 'prefix')]:
            pts = {0.0: rows(SAT / f'relay_st_s{s}_prefix_{cap}/rows.json', rule), 1.0: rows(SAT / f'relay_st_s{s}_agefirst_{cap}/rows.json', rule)}
            for b in ('0.05', '0.1', '0.25', '0.5'):
                pts[float(b)] = rows(E / f'VA_s{s}_mix{b}_{cap}/rows.json', rule)
            res = {}
            for b in sorted(pts):
                A = pts[b]
                if A is None:
                    continue
                res[b] = dict(waiting=round(float(np.mean([r['queue_sum'] for r in A.values()])), 1),
                              vs_beta0=paired(A, pts[0.0]) if pts[0.0] and b > 0 else None, vs_student=paired(A, st) if st else None)
            rep['V_A'][f's{s}_{cond}'] = res
            L.append(f'V-A s{s} {cond}: ' + '; '.join(f'b={b:g} {v["waiting"]} (vs b0 {v["vs_beta0"][0]:+.2f}% [{v["vs_beta0"][1]:+.2f},{v["vs_beta0"][2]:+.2f}], vs 0B {v["vs_student"][0]:+.2f}%)'
                                                    if v['vs_beta0'] else f'b={b:g} {v["waiting"]} (vs 0B {v["vs_student"][0]:+.2f}%)' for b, v in res.items()))
        for cfg in ['relay_agefirst', 'relay_prefix', 'setprefix', 'FO']:
            fr = {}
            for k in range(1, 8):
                A = rows(E / f'VS_s{s}_{cfg}_K{k}/rows.json', 'prefix')
                if A is not None:
                    fr[k] = A
            if not fr:
                continue
            steps = []
            for k in range(1, 7):
                if k in fr and k + 1 in fr:
                    steps.append((k, paired(fr[k + 1], fr[k])))
            nonmono = [k for k, (e, lo, hi) in steps if lo > 0]
            rep['V_S'][f's{s}_{cfg}'] = dict(waiting={k: round(float(np.mean([r['queue_sum'] for r in v.values()])), 1) for k, v in fr.items()},
                                             vs_student={k: paired(v, st) for k, v in fr.items()} if st else None,
                                             step_changes={k: v for k, v in steps}, worse_with_more_packets_at_K=nonmono,
                                             monotone=(len(nonmono) == 0))
            L.append(f'V-S s{s} {cfg}: ' + ' '.join(f'K{k}:{rep["V_S"][f"s{s}_{cfg}"]["waiting"][k]}' for k in sorted(fr)) +
                     f' | vs 0B ' + ' '.join(f'{rep["V_S"][f"s{s}_{cfg}"]["vs_student"][k][0]:+.1f}' for k in sorted(fr)) +
                     f' | worse-with-more-packets at K = {nonmono} -> {"MONOTONE" if not nonmono else "NON-MONOTONE"}')
    print('\n'.join(L)); Path(a.out).write_text(json.dumps(rep, indent=1, default=str)); Path(a.out).with_suffix('.txt').write_text('\n'.join(L) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1])
    p.add_argument('--out', default='research/marl_budget/e3_theory_cl_report_20260930.json')
    main(p.parse_args())
