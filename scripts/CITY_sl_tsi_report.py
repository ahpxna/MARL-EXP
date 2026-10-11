#!/usr/bin/env python3
"""F1-3 / F1-4 (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendment A5) at 400S & 200W.
  select <dir>  TUNE rows <dir>/tune: R[_P5], T_a<A>_b<B>[_q01][_P5] (development fleet GLOSAL:0.3).  R15-U over the grid (agent-TL upper over
                the TUNE days <= 0, city / human mean <= 0, argmin max(H4, P5)) -> <dir>/tune/choice.json.
  report <dir>  CONF rows <dir>/conf: <arm>[P5]_t11_s<f> for OFF, R, HARM, TG, TU; fleets s13 / s113; KM13-1a/1b.
                D-F1a (alpha 0.05): TG - R every M3 limit and agent fuel upper < 0 under HBEFA4 and PHEMlight5.  Descriptive: TU - TG, TU - R,
                M2: HARM - OFF, R - OFF.   SL_SMOKE=1: one TUNE / CONF day, fleet s13."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
from scripts.CITY_sl_build import days  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('SL_SMOKE') == '1'
TS = [d.timetuple().tm_yday for d in days('400sX200w', 'tune')][:1 if SM else 4]
CS = [d.timetuple().tm_yday for d in days('400sX200w', 'conf')][:1 if SM else 20]; FL = ('s13',) if SM else ('s13', 's113'); LT = (11,)
GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5)]
gtag = lambda a, b, q: f'T_a{a:g}_b{b:g}'.replace('.', 'p') + ('_q01' if q == 0.1 else '')  # noqa: E731
if cmd == 'select':
    Rt = rows(D / 'tune'); R = {x: Rt[f'R{x}'] for x in ('', '_P5')}; cand = {}
    for a, b in GRID:
        for q in (0.5, 0.1):
            tg = gtag(a, b, q)
            if tg not in Rt:
                continue
            X = {x: Rt[tg + x] for x in ('', '_P5')}
            f4, f5 = (float(100 * (np.mean([X[x][s]['fuel_agent'] for s in TS]) / np.mean([R[x][s]['fuel_agent'] for s in TS]) - 1)) for x in ('', '_P5'))
            dA = np.array([X[''][s]['timeloss_agent'] - R[''][s]['timeloss_agent'] for s in TS])
            up = float(dA.mean() + (1.645 * dA.std(ddof=1) / np.sqrt(len(TS)) if len(TS) > 1 else 0.0))
            cand[f'{a:g},{b:g},{q:g}'] = dict(fuel_H4=f4, fuel_P5=f5, agent=float(dA.mean()), agent_up=up,
                                              city=float(np.mean([X[''][s]['timeloss'] - R[''][s]['timeloss'] for s in TS])),
                                              human=float(np.mean([X[''][s]['timeloss_human'] - R[''][s]['timeloss_human'] for s in TS])))
    ok = [c for c, v in cand.items() if v['agent_up'] <= 0 and v['city'] <= 0 and v['human'] <= 0]
    key = lambda c: (max(cand[c]['fuel_H4'], cand[c]['fuel_P5']), c)  # noqa: E731
    ch = min(ok, key=key) if ok else min(cand, key=lambda c: (cand[c]['agent_up'], c))
    out = [f'== F1-4 selection R15-U (TUNE {TS}; development fleet GLOSAL:0.3): choice {ch} ({len(ok)} qualified)'] + \
          [f'  {c}: H4 {v["fuel_H4"]:+.2f} P5 {v["fuel_P5"]:+.2f} agent {v["agent"]:+.2f} (up {v["agent_up"]:+.2f}) city {v["city"]:+.2f} human {v["human"]:+.2f}{"  *" if c in ok else ""}' for c, v in cand.items()]
    (D / 'tune' / 'choice.json').write_text(json.dumps(dict(choice=ch, qualified=ok, table=cand), indent=1)); (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    Rt = rows(D / 'conf'); TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
    for a in ('OFF', 'R', 'HARM', 'TG', 'TU'):
        for f in FL:
            for s in CS:
                h, p = Rt[K(a)(11, f)][s], Rt[K(a + 'P5')(11, f)][s]
                if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                    print('KM13-1a/1b FAIL', a, f, s); sys.exit(1)
    r = V.paired(Rt, K('TG'), K('R'), LT, FL, CS); ok, tl = V.limits(r, V.tele(Rt, K('TG'), LT, FL, CS), V.tele(Rt, K('R'), LT, FL, CS))
    r5 = V.paired(Rt, K('TGP5'), K('RP5'), LT, FL, CS); d1 = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    out = [f'== F1-4 TSI on recorded demand, Salt Lake 400S & 200W (RLW t11; fleets {FL}; CONF days {CS[0]}-{CS[-1]}; HBEFA4 / PHEMlight5)',
           'KM13-1a PASS, KM13-1b PASS', '-- D-F1a (alpha 0.05)', V.line('TG - R (H4)', r), f'  TG all M3 limits: {ok}; {tl}', V.line('TG - R (P5)', r5),
           f'  D-F1a VERDICT: {"SHOWN" if d1 else "NOT SHOWN"}', '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in (('TU', 'R'), ('TU', 'TG'), ('R', 'OFF'), ('HARM', 'OFF'), ('TG', 'OFF')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, CS)))
    (D / 'conf' / 'report_tsi.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
