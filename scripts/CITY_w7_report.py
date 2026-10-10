#!/usr/bin/env python3
"""Wave-7 reports (PROTOCOL_CITY_WAVE7_20261005), with the strict wave-6 validation loader (CITY_w6_validation.rows) and the v2 helpers
(crossed bootstrap, limits incl. teleports AND unfinished).  Usage: CITY_w7_report.py dca2 | fpr    (W7_SMOKE=<dir> W7_SEED=<s>: smoke)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
W = Path(os.environ['W7_SMOKE']) if os.environ.get('W7_SMOKE') else ROOT / 'research/city_sim/w7_20261005'; SM = bool(os.environ.get('W7_SMOKE'))


def need(Rt, keys, S):
    miss = [k for k in keys if k not in Rt]; bad = [k for k in keys if k in Rt and sorted(Rt[k]) != sorted(S)]
    if miss or bad:
        print('INCOMPLETE / SEED MISMATCH', miss[:4], bad[:4]); sys.exit(1)


def order(d):
    f, t = d['fuel_agent'], d['timeloss_agent']
    if f['up'] <= 0 and t['up'] <= 0 and (f['up'] < 0 or t['up'] < 0):
        return 'TSI better'
    if f['low'] >= 0 and t['low'] >= 0 and (f['low'] > 0 or t['low'] > 0):
        return 'comparator better'
    return 'no ordering'


def dca2():
    D = W / 'dca2'; Rt = rows(D / 'conf'); S = [int(os.environ.get('W7_SEED', 760))] if SM else list(range(760, 780))
    LT = (4,) if SM else (4, 5, 6, 7, 8); FL = ('s213',) if SM else ('s213', 's313', 's413', 's513')
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}'); need(Rt, [K(a)(l, f) for a in ('R', 'TSI2', 'DCA2') for l in LT for f in FL], S)
    out = ['== W7-2 DCA2 (faithful DC-Ada port: per-controller residual MLP transforms, M 5, sigma 0.05, truncated 1350 s rollouts, budget 176 = 44 x 5400 s; '
           'lights t4-t8 x fleets s213-s513 x traffic 760-779)']
    for a in ('TSI2', 'DCA2'):
        r = V.paired(Rt, K(a), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
        out += [V.line(f'{a} - R', r), f'  {a}: all M3 limits (incl. teleports, unfinished): {ok}; {tl}']
    d = V.paired(Rt, K('TSI2'), K('DCA2'), LT, FL, S); out += [V.line('TSI2 - DCA2', d), f'  W7-2 (b) ordering on agent fuel and agent TL (one-sided 95 %): {order(d)}']
    th = {l: json.loads((D / 'tune' / f'dca2_t{l}.json').read_text()) for l in LT}
    out.append('  DCA2 tuning: ' + '; '.join(f't{l} rollouts {th[l]["rollouts"]}/{th[l]["budget"]} accepted {th[l]["accepted"]} |theta| {th[l]["param_norm"]:.3f}' for l in LT))
    w6 = ROOT / 'research/city_sim/w6_20261005/dca/conf'
    if not SM and w6.exists():
        R6 = rows(w6); same = all(Rt[K('R')(l, f)][s][q] == R6[K('R')(l, f)][s][q] for l in LT for f in FL for s in S for q in ('timeloss', 'fuel_agent', 'timeloss_agent'))
        out.append(f'  KW7-2 R rows == W6-1 R rows (bit-identical endpoints): {same}')
    print('\n'.join(out)); (D / 'report_dca2.txt').write_text('\n'.join(out) + '\n')


def fpr():
    D = W / 'fpr'; Rt = rows(D / 'conf'); S = [int(os.environ.get('W7_SEED', 780))] if SM else list(range(780, 800))
    LT = (9,) if SM else (9, 10, 11, 12, 13); FL = ('s613',) if SM else ('s613', 's713', 's813', 's913')
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}'); need(Rt, [K(a)(l, f) for a in ('R', 'TSI', 'HYB', 'ADP') for l in LT for f in FL], S)
    ch = json.loads((D / 'tune' / 'choice.json').read_text())
    out = ['== W7-1 FPR (fresh-policy replication: NEW lights RL-H t9-t13 x NEW fleets R10 s613-s913 x fresh traffic 780-799; TSI recalibrated from scratch)',
           '  per-light (A, B): ' + ', '.join(f't{l} ({ch[str(l)]["choice"]})' for l in LT)]
    for a in ('TSI', 'HYB', 'ADP'):
        r = V.paired(Rt, K(a), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
        out += [V.line(f'{a} - R', r), f'  {a}: all M3 limits (incl. teleports, unfinished): {ok}; {tl}']
        if a == 'TSI':
            verdict = ok
    for a in ('HYB', 'ADP'):
        out.append(V.line(f'TSI - {a}', V.paired(Rt, K('TSI'), K(a), LT, FL, S)))
    out.append(f'  W7-1 FRESH-POLICY REPLICATION VERDICT (alpha 0.05 one-sided): {"PASS" if verdict else "FAIL"}')
    print('\n'.join(out)); (D / 'report_fpr.txt').write_text('\n'.join(out) + '\n')


if __name__ == '__main__':
    dict(dca2=dca2, fpr=fpr)[sys.argv[1]]()
