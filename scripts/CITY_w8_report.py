#!/usr/bin/env python3
"""Wave-8 reports (PROTOCOL_CITY_WAVE8_20261005), strict loader (CITY_w6_validation.rows) and the v2 helpers.
Usage: CITY_w8_report.py fresh2 | lcd2 | net3      (W8_SMOKE=<dir> W8_SEED=<s>: smoke)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W8_SMOKE')); W = Path(os.environ['W8_SMOKE']) if SM else ROOT / 'research/city_sim/w8_20261005'


def need(Rt, keys, S):
    miss = [k for k in keys if k not in Rt]; bad = [k for k in keys if k in Rt and sorted(Rt[k]) != sorted(S)]
    if miss or bad:
        print('INCOMPLETE / SEED MISMATCH', miss[:4], bad[:4]); sys.exit(1)


def arms(Rt, K, pairs, LT, FL, S, out):
    ok = {}
    for a, b in pairs:
        r = V.paired(Rt, K(a), K(b), LT, FL, S); o, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K(b), LT, FL, S)); ok[a] = (o, r)
        out += [V.line(f'{a} - {b}', r), f'  {a}: all M3 limits vs {b} (incl. teleports, unfinished): {o}; {tl}']
    return ok


def fresh2():
    D = W / 'fresh2'; Rt = rows(D / 'conf'); S = [int(os.environ.get('W8_SEED', 800))] if SM else list(range(800, 820))
    LT = (14,) if SM else (14, 15, 16, 17, 18); FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313')
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}'); need(Rt, [K(a)(l, f) for a in ('R', 'TSI', 'F1B', 'R25', 'TSI25') for l in LT for f in FL], S)
    ch = json.loads((D / 'tune' / 'choice.json').read_text())
    out = ['== W8-2 FRESH2 (second independent fresh-policy set: lights RL-H t14-t18 x R10 s1013-s1313 x fresh traffic 800-819; TSI recalibrated from scratch; F1-B retrained fresh)',
           '  per-light (A, B): ' + ', '.join(f't{l} ({ch[str(l)]["choice"]})' for l in LT)]
    ok = arms(Rt, K, (('TSI', 'R'), ('F1B', 'R'), ('TSI25', 'R25')), LT, FL, S, out)
    d = V.paired(Rt, K('TSI'), K('F1B'), LT, FL, S); out.append(V.line('TSI - F1B', d))
    ni = d['fuel_agent']['up'] < 0.5; sup = d['timeloss']['up'] < 0 and d['timeloss_agent']['up'] < 0
    out += [f'  (1) SECOND FRESH-POLICY REPLICATION VERDICT (TSI vs R, alpha 0.05 one-sided): {"PASS" if ok["TSI"][0] else "FAIL"}',
            f'  (2) NON-INFERIORITY VERDICT vs retraining on agent fuel (upper {d["fuel_agent"]["up"]:+.3f} < +0.5 pp): {"PASS" if ni else "FAIL"}',
            f'  (3) time superiority vs retraining (city and agent TL upper < 0; secondary): {sup}',
            f'  (4) FLEET SHARE 0.25 VERDICT (TSI25 vs R25): {"PASS" if ok["TSI25"][0] else "FAIL"}']
    print('\n'.join(out)); (D / 'report_fresh2.txt').write_text('\n'.join(out) + '\n')


def lcd2():
    D = W / 'lcd2'; out = ['== W8-3 LCD2 (learned committed-duration light, time-normalised reward; exact SPaT)']; g = json.loads((D / 'gate.json').read_text())
    out.append('  DEV gate: ' + json.dumps(g))
    if not g['pass']:
        out.append('  W8-3 VERDICT: DEV GATE FAILED -> no confirmation (registered)'); print('\n'.join(out)); (D / 'report_lcd2.txt').write_text('\n'.join(out) + '\n'); return
    Rt = rows(D / 'conf'); S = [int(os.environ.get('W8_SEED', 800))] if SM else list(range(800, 820))
    LT = (14,) if SM else (14, 15, 16, 17, 18); FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313'); J = (0, 1)
    ka = lambda l, f: f'LCDF_j{l}_{f}'; kr = lambda l, f: f'R_t{l}_{f}'
    need(Rt, [ka(j, f) for j in J for f in FL] + [kr(l, f) for l in LT for f in FL], S)
    r = V.unpaired(Rt, ka, J, kr, LT, FL, S); o, tl = V.limits(r, V.tele(Rt, ka, J, FL, S), V.tele(Rt, kr, LT, FL, S))
    out += [V.line('LCDF - R (lights unpaired)', r), f'  W8-3 VERDICT (learned predictable light + exact SPaT meets every M3 limit vs R): {"PASS" if o else "FAIL"}; {tl}']
    ra = V.unpaired(Rt, lambda l, f: f'LCDA_j{l}', J, lambda l, f: f'RLHA_t{l}', LT, ('x',), S, metrics=('timeloss',)); out.append(V.line('LCD2 alone - RL-H alone (SUMO cars, city TL)', ra))
    print('\n'.join(out)); (D / 'report_lcd2.txt').write_text('\n'.join(out) + '\n')


def net3():
    D = W / 'net3'; S = [int(os.environ.get('W8_SEED', 700))] if SM else list(range(700, 720)); DV = [int(os.environ.get('W8_DEV', 600))] if SM else list(range(600, 606))
    LT = (21,) if SM else (21, 22, 23, 24, 25); FL = ('s213',) if SM else ('s213', 's313', 's413', 's513')
    out = ['== W8-4 NET3 (third network rand3: 20 two-green signals, irregular; NEW lights RL-H t21-t25, NEW fleets N3_s213-s513, dev fleet N3_s13)',
           '  demand: ' + (D / 'period' / 'report.txt').read_text().strip()]
    Rd = rows(D / 'dev'); one = (0,)
    m1 = V.paired(Rd, lambda l, f: f'FLTFT_{f}', lambda l, f: f'SIGFT_{f}', one, FL, DV); out.append(V.line('M1 (DEV): fleet with program SPaT - sigma* under FT', m1))
    m1ok = m1['fuel_agent']['up'] < 0; out.append(f'  M1 condition (fleet saves fuel vs sigma* under FT, DEV upper < 0): {m1ok}')
    la = V.unpaired(Rd, lambda l, f: f'LA_t{l}', LT, lambda l, f: 'FTA', (0,), ('x',), DV, metrics=('timeloss',)); out.append(V.line('learned light - FT (SUMO cars, DEV, city TL)', la))
    m2 = V.paired(Rd, lambda l, f: f'NAIVE_t{l}_{f}', lambda l, f: f'R_t{l}_{f}', LT, FL, DV); out.append(V.line('M2 (DEV): naive program SPaT under the learned light - R', m2))
    Rt = rows(D / 'conf'); K = lambda a: (lambda l, f: f'{a}_t{l}_{f}'); need(Rt, [K(a)(l, f) for a in ('R', 'TSI', 'HYB', 'ADP') for l in LT for f in FL], S)
    ch = json.loads((D / 'tune' / 'choice.json').read_text()); out.append('  per-light (A, B): ' + ', '.join(f't{l} ({ch[str(l)]["choice"]})' for l in LT))
    ok = arms(Rt, K, (('TSI', 'R'), ('HYB', 'R'), ('ADP', 'R')), LT, FL, S, out)
    for a in ('HYB', 'ADP'):
        out.append(V.line(f'TSI - {a}', V.paired(Rt, K('TSI'), K(a), LT, FL, S)))
    out.append(f'  W8-4 THIRD-NETWORK REPLICATION VERDICT (alpha 0.05 one-sided): {"PASS" if ok["TSI"][0] else "FAIL"}' + ('' if m1ok else '  [registered condition: M1 benefit not shown on DEV, so descriptive only]'))
    print('\n'.join(out)); (D / 'report_net3.txt').write_text('\n'.join(out) + '\n')


if __name__ == '__main__':
    dict(fresh2=fresh2, lcd2=lcd2, net3=net3)[sys.argv[1]]()
