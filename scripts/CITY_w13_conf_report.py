#!/usr/bin/env python3
"""W13-2 / W13-3 confirmation report (PROTOCOL_CITY_WAVE13_20261006).  FRESH2 lights t14-t18 x fleets s1013-s1313 x fresh traffic 900-919.
Arms (H4 = HBEFA4 default; P5 = PHEMlight5 at departure, same trajectories): R, TW8 (W8-2 choice), TF (R13-F), TRB (R13-RB), F1B (W8-2
retrained fleets); P5 twins carry the suffix P5 in the arm name.  Crossed bootstrap of CITY_w6_report_v2 (B = 2000).
  D13-1 (alpha 0.025 one-sided): TF meets every M3 limit vs R (H4) and TF - F1B agent fuel (H4) upper < +0.5 pp (upper < 0: TF saves more).
  D13-2 (alpha 0.025 one-sided): TRB meets every M3 limit vs R and TRB - R agent fuel upper < 0 under H4 and under P5.
Self-checks: KM13-1a (P5 == H4 in dynamics), KM13-1b (grid / tripinfo in [0.98, 1.02]).  Usage: CITY_w13_conf_report.py [<dir>] (W13_SMOKE=1)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/w13_20261006'
SM = os.environ.get('W13_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313')
S = [int(os.environ.get('W13_SEED', 860))] if SM else list(range(900, 920))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = rows(D / 'conf')
bad = [f'{k} s{s}' for k, v in Rt.items() for s, r in v.items() if not (r.get('modes_ratio_all') and 0.98 <= r['modes_ratio_all'] <= 1.02)]
if bad:
    print('KM13-1b FAIL', bad[:10]); sys.exit(1)
for a in ('R', 'TW8', 'TF', 'TRB', 'F1B'):
    for l in LT:
        for f in FL:
            h, p = Rt[K(a)(l, f)], Rt[K(a + 'P5')(l, f)]
            for s in S:
                if any(h[s][q] != p[s][q] for q in ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')):
                    print('KM13-1a FAIL', a, l, f, s); sys.exit(1)
chF = json.loads((D / 'tune' / 'choice_F.json').read_text()); chRB = json.loads((D / 'tune' / 'choice_RB.json').read_text())
out = ['== W13-2/3 confirmation (FRESH2 t14-t18 x s1013-s1313 x fresh 900-919; HBEFA4 and PHEMlight5 on the same trajectories)',
       'KM13-1a PASS, KM13-1b PASS',
       'choices R13-F: ' + ', '.join(f't{t} {v["choice"]}' for t, v in chF.items()) + ' | R13-RB: ' + ', '.join(f't{t} {v["choice"]}' for t, v in chRB.items())]


def lim(a, r_, q):
    r = V.paired(Rt, K(a), K(r_), LT, FL, S, q=q); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K(r_), LT, FL, S)); return r, ok, tl


# D13-1
r, ok, tl = lim('TF', 'R', 97.5); d = V.paired(Rt, K('TF'), K('F1B'), LT, FL, S, q=97.5)
ni = ok and d['fuel_agent']['up'] < 0.5; better = ok and d['fuel_agent']['up'] < 0
out += ['-- D13-1 (retraining; alpha 0.025 one-sided)', V.line('TF - R (H4)', r), f'  TF all M3 limits: {ok}; {tl}', V.line('TF - F1B (H4)', d),
        f'  D13-1 VERDICT: fuel non-inferiority to F1B (+0.5 pp) {"ESTABLISHED" if ni else "NOT ESTABLISHED"}'
        + ('; TF saves more fuel than F1B' if better else '')]
# D13-2
rH, okH, tlH = lim('TRB', 'R', 97.5); r5 = V.paired(Rt, K('TRBP5'), K('RP5'), LT, FL, S, q=97.5)
p2 = okH and rH['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
out += ['-- D13-2 (two emission models; alpha 0.025 one-sided)', V.line('TRB - R (H4)', rH), f'  TRB all M3 limits (H4): {okH}; {tlH}',
        V.line('TRB - R (P5)', r5), f'  D13-2 VERDICT: saving under both HBEFA4 and PHEMlight5 {"SHOWN" if p2 else "NOT SHOWN"}']
# descriptive (one-sided 95 %)
out.append('-- descriptive (one-sided 95 %)')
for a, b in (('TW8', 'R'), ('TW8P5', 'RP5'), ('F1B', 'R'), ('F1BP5', 'RP5'), ('TF', 'R'), ('TFP5', 'RP5'), ('TRBP5', 'RP5'), ('TRB', 'F1B'),
             ('TRBP5', 'F1BP5'), ('TF', 'TRB'), ('TF', 'TW8'), ('TW8', 'F1B')):
    out.append(V.line(f'{a} - {b}', V.paired(Rt, K(a), K(b), LT, FL, S)))
(D / 'conf' / 'report_conf.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
