#!/usr/bin/env python3
"""W15-2 (PROTOCOL_CITY_WAVE15_20261007): rule R15-U and the confirmation report.  FRESH2 lights t14-t18, TUNE 660-663, fleet L11_s13.
Candidates per light: the W13 grid (A, B, q in {0.1, 0.5}; rows in w8 fresh2/tune and w13/tune) and the 27 state-quantile configurations
S_t<k>_a<a>_b<b>_c<c> at adapter (1, 0.25) (rows in <dir>/tune), each under HBEFA4 and PHEMlight5.
  R15-U: agent-TL upper = mean + 1.645 sd / sqrt(n) of the per-seed differences vs R <= 0, city / human mean <= 0 -> argmin
         max(fuel_H4, fuel_P5); none -> min agent-TL upper.  (R13-RB on the same candidates is reported for comparison.)
  select <dir>  -> <dir>/tune/choice_U.json, report_select.txt
  report <dir>  fresh 1060-1079: R, TRB (W13 choice), TU, TG (1, 0.25, 0.1), F1B (+P5 twins).
     D15-2a (alpha 0.05): TU meets every M3 limit and saves fuel under both models.
     D15-2b (alpha 0.05): TU - TRB agent TL upper < 0 and TU - TRB fuel upper < +0.5 pp under both models.
W15_SMOKE=1: t14, TUNE 660, conf 860."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W15_SMOKE') == '1'
F2 = ROOT / 'research/city_sim/w8_20261005/fresh2'; W13 = ROOT / 'research/city_sim/w13_20261006'
LT = (14,) if SM else (14, 15, 16, 17, 18); TS = [660] if SM else [660, 661, 662, 663]
FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313'); CS = [860] if SM else list(range(1060, 1080))
GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)]
QS = [(a, b, c) for a in (-2, 0, 2) for b in (0, 1, 3) for c in (0, 1, 3)]
enc = lambda x: (f'm{-x:g}' if x < 0 else f'{x:g}')  # noqa: E731
gtag = lambda t, a, b, q: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p') + ('_q01' if q == 0.1 else '')  # noqa: E731
stag = lambda t, a, b, c: f'S_t{t}_a{enc(a)}_b{enc(b)}_c{enc(c)}'  # noqa: E731
if cmd == 'select':
    Rt = {**({} if SM else {**rows(F2 / 'tune'), **rows(W13 / 'tune')}), **rows(D / 'tune')}
    out = ['== W15-2 selection: R15-U (agent-TL upper over TUNE seeds) vs R13-RB, FRESH2 TUNE ' + ','.join(map(str, TS))]; ch = {}
    for t in LT:
        R = {x: Rt[f'R_t{t}{x}'] for x in ('', '_P5')}; cand = {}
        items = [(f'grid:{a:g},{b:g},{q:g}', gtag(t, a, b, q)) for a, b in GRID for q in (0.5, 0.1)] + [(f'qs:{a}:{b}:{c}', stag(t, a, b, c)) for a, b, c in QS]
        for name, tg in items:
            if SM and tg not in Rt:
                continue
            X = {x: Rt[tg + x] for x in ('', '_P5')}
            for s in TS:
                if any(X[''][s][k] != X['_P5'][s][k] for k in ('timeloss', 'n', 'teleports', 'action_digest')):
                    print('KM13-1a FAIL', tg, s); sys.exit(1)
            f4, f5 = (float(100 * (np.mean([X[x][s]['fuel_agent'] for s in TS]) / np.mean([R[x][s]['fuel_agent'] for s in TS]) - 1)) for x in ('', '_P5'))
            dA = np.array([X[''][s]['timeloss_agent'] - R[''][s]['timeloss_agent'] for s in TS])
            up = float(dA.mean() + (1.645 * dA.std(ddof=1) / np.sqrt(len(TS)) if len(TS) > 1 else 0.0))
            cand[name] = dict(fuel_H4=f4, fuel_P5=f5, agent=float(dA.mean()), agent_up=up,
                              city=float(np.mean([X[''][s]['timeloss'] - R[''][s]['timeloss'] for s in TS])),
                              human=float(np.mean([X[''][s]['timeloss_human'] - R[''][s]['timeloss_human'] for s in TS])))
        okU = [c for c, v in cand.items() if v['agent_up'] <= 0 and v['city'] <= 0 and v['human'] <= 0]
        okRB = [c for c, v in cand.items() if v['agent'] <= 0 and v['city'] <= 0 and v['human'] <= 0]
        key = lambda c: (max(cand[c]['fuel_H4'], cand[c]['fuel_P5']), c)  # noqa: E731
        cU = min(okU, key=key) if okU else min(cand, key=lambda c: (cand[c]['agent_up'], c)); cRB = min(okRB, key=key) if okRB else None
        ch[t] = dict(choice=cU, rule='qualified' if okU else 'fallback: min agent-TL upper', n_qualified=len(okU), rb_choice=cRB, table=cand)
        v = cand[cU]; out.append(f't{t}: R15-U {cU} (H4 {v["fuel_H4"]:+.2f} P5 {v["fuel_P5"]:+.2f} agent {v["agent"]:+.2f} up {v["agent_up"]:+.2f}; '
                                f'{len(okU)} qualified) | R13-RB on the same set: {cRB}')
    (D / 'tune' / 'choice_U.json').write_text(json.dumps(ch, indent=1)); (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    Rt = rows(D / 'conf'); TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
    for a in ('R', 'TRB', 'TU', 'TG', 'F1B'):
        for l in LT:
            for f in FL:
                for s in CS:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[k] != p[k] for k in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    out = [f'== W15-2 confirmation (FRESH2, fresh traffic {CS[0]}-{CS[-1]}; HBEFA4 / PHEMlight5)', 'KM13-1a PASS, KM13-1b PASS']
    r = V.paired(Rt, K('TU'), K('R'), LT, FL, CS); ok, tl = V.limits(r, V.tele(Rt, K('TU'), LT, FL, CS), V.tele(Rt, K('R'), LT, FL, CS))
    r5 = V.paired(Rt, K('TUP5'), K('RP5'), LT, FL, CS); va = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    d4 = V.paired(Rt, K('TU'), K('TRB'), LT, FL, CS); d5 = V.paired(Rt, K('TUP5'), K('TRBP5'), LT, FL, CS)
    vb = d4['timeloss_agent']['up'] < 0 and d4['fuel_agent']['up'] < 0.5 and d5['fuel_agent']['up'] < 0.5
    out += ['-- D15-2a (alpha 0.05)', V.line('TU - R (H4)', r), f'  TU all M3 limits: {ok}; {tl}', V.line('TU - R (P5)', r5),
            f'  D15-2a VERDICT: {"SHOWN" if va else "NOT SHOWN"}', '-- D15-2b (alpha 0.05)', V.line('TU - TRB (H4)', d4), V.line('TU - TRB (P5)', d5),
            f'  D15-2b VERDICT: less agent time than TRB without material fuel loss {"SHOWN" if vb else "NOT SHOWN"}', '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in (('TRB', 'R'), ('TG', 'R'), ('TG', 'TRB'), ('F1B', 'R'), ('TU', 'F1B'), ('TG', 'F1B')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, CS)))
    (D / 'conf' / 'report_u.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
