#!/usr/bin/env python3
"""W13-4 (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): iterated closed-loop refit.
  select <dir>   per light, among rounds r in {0, 1, 2} (r0 = the W13 configuration with the W8-2 network; r1, r2 = networks refitted on TRAIN
                 logs collected with round r-1 published), the rounds meeting S on TUNE (agent / city / human TL <= 0 vs R) -> argmin
                 max(fuel_H4, fuel_P5); none qualified -> r0.  Writes <dir>/refit/choice.json, report_select.txt.
  report <dir>   fresh 920-939: R, TC (round 0 = the W13 configuration), TREF (chosen round), F1B; HBEFA4 and PHEMlight5.
                 D13-1' (alpha 0.0125): TREF meets every M3 limit and TREF - F1B fuel (H4) upper < +0.5 pp.
                 D13-2' (alpha 0.0125): TREF meets every M3 limit and TREF - R fuel upper < 0 under H4 and P5.
Config file <dir>/refit/config.json (written by the job): {light: [A, B, q]}.  W13_SMOKE=1: t14, TUNE 660, seed 860."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W13_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); TS = [660] if SM else [660, 661, 662, 663]
FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313'); CS = [860] if SM else list(range(920, 940))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
if cmd == 'select':
    Rt = rows(D / 'refit' / 'tune'); out = ['== W13-4 round selection (TUNE ' + ','.join(map(str, TS)) + ')']; ch = {}
    for t in LT:
        R = {x: Rt[f'R_t{t}{x}'] for x in ('', 'P5')}; tab = {}
        for r in (0, 1, 2):
            X = {x: Rt[f'TR{r}_t{t}{x}'] for x in ('', 'P5')}
            f4, f5 = (float(100 * (np.mean([X[x][s]['fuel_agent'] for s in TS]) / np.mean([R[x][s]['fuel_agent'] for s in TS]) - 1)) for x in ('', 'P5'))
            tl = {k: float(np.mean([X[''][s][k] - R[''][s][k] for s in TS])) for k in ('timeloss', 'timeloss_agent', 'timeloss_human')}
            tab[r] = dict(fuel_H4=f4, fuel_P5=f5, **tl)
        ok = [r for r, v in tab.items() if v['timeloss_agent'] <= 0 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        c = min(ok, key=lambda r: (max(tab[r]['fuel_H4'], tab[r]['fuel_P5']), r)) if ok else 0; ch[t] = dict(round=c, qualified=ok, table=tab)
        out.append(f't{t}: choose r{c} (qualified {ok}) | ' + ' | '.join(f'r{r} H4 {v["fuel_H4"]:+.2f} P5 {v["fuel_P5"]:+.2f} agent {v["timeloss_agent"]:+.2f}' for r, v in tab.items()))
    (D / 'refit' / 'choice.json').write_text(json.dumps(ch, indent=1)); (D / 'refit' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    Rt = rows(D / 'refit' / 'conf'); q = 98.75; out = ['== W13-4 confirmation (fresh 920-939; alpha 0.0125 one-sided; third attempts at T1 and T2)']
    for a in ('R', 'TC', 'TREF', 'F1B'):
        for l in LT:
            for f in FL:
                for s in CS:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[k] != p[k] for k in ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    r = V.paired(Rt, K('TREF'), K('R'), LT, FL, CS, q=q); ok, tl = V.limits(r, V.tele(Rt, K('TREF'), LT, FL, CS), V.tele(Rt, K('R'), LT, FL, CS))
    d = V.paired(Rt, K('TREF'), K('F1B'), LT, FL, CS, q=q); r5 = V.paired(Rt, K('TREFP5'), K('RP5'), LT, FL, CS, q=q)
    out += [V.line('TREF - R (H4)', r), f'  TREF all M3 limits: {ok}; {tl}', V.line('TREF - F1B (H4)', d),
            f"  D13-1' VERDICT: fuel non-inferiority to F1B {'ESTABLISHED' if ok and d['fuel_agent']['up'] < 0.5 else 'NOT ESTABLISHED'}",
            V.line('TREF - R (P5)', r5), f"  D13-2' VERDICT: saving under both models {'SHOWN' if ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0 else 'NOT SHOWN'}",
            '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in (('TC', 'R'), ('TREF', 'TC'), ('F1B', 'R'), ('TC', 'F1B')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, CS)))
    (D / 'refit' / 'conf' / 'report_refit.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
