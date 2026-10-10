#!/usr/bin/env python3
"""W17 reports (PROTOCOL_CITY_WAVE17_20261008; copy of CITY_w16_report.py with the W17 panel: lights t29-t33, fleets s2213-s2513,
fresh 1320-1339 (stage 1) and 1340-1359 (stage 2), smoke via W17_SMOKE).  Original: W16 reports (PROTOCOL_CITY_WAVE16_20261008).  Rows in <dir>/m1 (stage 1, fresh 1300-1319):
  OFF[P5]_t0_h      FT, every car an IDM human (fleet L-ACT:0 membership, guard always)
  PL[P5]_t0_s<f>    FT, the IDM-trained fleet with exact FT SPaT          R[P5]_t0_s<f>   FT, the fleet without SPaT
  GATE[P5]_t<k>_h   learned light RL-H t<k>, every car human               RL[P5]_t<k>_s<f>  learned light, fleet without SPaT (M2)
  m1 <dir>  D16-1 (alpha 0.05): PL - OFF agent fuel upper < 0 under HBEFA4 and PHEMlight5 and every M3 limit;
            W16-2 (alpha 0.05): GATE - OFF city time-loss upper < 0 (pooled over the five lights);  M2 descriptive: RL - GATE.
  KM13-1a/1b on every row pair.  Writes <dir>/m1/report_m1.txt and <dir>/m1/stage1.json.   W16_SMOKE=1: t24, s1813, seed 860."""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W17_SMOKE') == '1'
LT = (29,) if SM else (29, 30, 31, 32, 33); FL = ('s2213',) if SM else ('s2213', 's2313', 's2413', 's2513')
S = [860] if SM else list(range(1320, 1340))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
if cmd == 'm1':
    Rt = rows(D / 'm1')
    for x in ('', 'P5'):                                               # aliases (no duplicate runs): fleet-independent rows per fleet / light
        for f in FL:
            Rt[f'OFF{x}_t0_{f}'] = Rt[f'OFF{x}_t0_h']
        for k in LT:
            Rt[f'OFFG{x}_t{k}_h'] = Rt[f'OFF{x}_t0_h']
            for f in FL:
                Rt[f'GATEF{x}_t{k}_{f}'] = Rt[f'GATE{x}_t{k}_h']
    pairs = [('OFF', (0,), ('h',)), ('PL', (0,), FL), ('R', (0,), FL), ('GATE', LT, ('h',)), ('RL', LT, FL)]
    for a, ls_, fs in pairs:
        for l in ls_:
            for f in fs:
                for s in S:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    out = [f'== W17 stage 1, field-matched world (jointly calibrated IDM; lights t{LT[0]}-t{LT[-1]}, fleets {FL}, fresh {S[0]}-{S[-1]})', 'KM13-1a PASS, KM13-1b PASS']
    r = V.paired(Rt, K('PL'), K('OFF'), (0,), FL, S); ok, tl = V.limits(r, V.tele(Rt, K('PL'), (0,), FL, S), V.tele(Rt, K('OFF'), (0,), FL, S))
    r5 = V.paired(Rt, K('PLP5'), K('OFFP5'), (0,), FL, S); d1 = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    out += ['-- D17-1 M1 in the field-matched world (alpha 0.05)', V.line('PL - OFF (H4)', r), f'  all M3 limits: {ok}; {tl}', V.line('PL - OFF (P5)', r5),
            f'  D17-1 VERDICT: {"SHOWN" if d1 else "NOT SHOWN"}']
    g = V.paired(Rt, K('GATE'), K('OFFG'), LT, ('h',), S); w2 = g['timeloss']['up'] < 0
    out += ['-- W17-2 light gate (alpha 0.05; city time loss)', V.line('RL-H(W17) - FT, all humans', g), f'  W17-2 VERDICT: {"PASS" if w2 else "FAIL"}']
    out += ['-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        out.append(V.line(f'R{x} - OFF{x} (FT, fleet without SPaT)', V.paired(Rt, K('R' + x), K('OFF' + x), (0,), FL, S)))
        out.append(V.line(f'RL{x} - GATE{x} (M2: learned light, fleet without SPaT vs humans)', V.paired(Rt, K('RL' + x), K('GATEF' + x), LT, FL, S)))
    (D / 'm1' / 'report_m1.txt').write_text('\n'.join(out) + '\n'); (D / 'm1' / 'stage1.json').write_text(json.dumps(dict(D17_1=d1, W17_2=w2)))
    print('\n'.join(out))
elif cmd == 'select':                                                   # R15-U per light (W16-4), as CITY_w15_u select, lights t24-t28
    import numpy as np
    TS = [660] if SM else [660, 661, 662, 663]
    GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)]
    QS = [(a, b, c) for a in (-2, 0, 2) for b in (0, 1, 3) for c in (0, 1, 3)]
    enc = lambda x: (f'm{-x:g}' if x < 0 else f'{x:g}')  # noqa: E731
    gtag = lambda t, a, b, q: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p') + ('_q01' if q == 0.1 else '')  # noqa: E731
    stag = lambda t, a, b, c: f'S_t{t}_a{enc(a)}_b{enc(b)}_c{enc(c)}'  # noqa: E731
    Rt = rows(D / 'tune'); out = ['== W17-4 selection R15-U (field-matched world; TUNE ' + ','.join(map(str, TS)) + ')']; ch = {}
    for t in LT:
        R = {x: Rt[f'R_t{t}{x}'] for x in ('', '_P5')}; cand = {}
        items = [(f'grid:{a:g},{b:g},{q:g}', gtag(t, a, b, q)) for a, b in GRID for q in (0.5, 0.1)] + [(f'qs:{a}:{b}:{c}', stag(t, a, b, c)) for a, b, c in QS]
        for name, tg in items:
            if tg not in Rt or tg + '_P5' not in Rt:
                if SM:
                    continue
                print('missing', tg); sys.exit(1)
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
        key = lambda c: (max(cand[c]['fuel_H4'], cand[c]['fuel_P5']), c)  # noqa: E731
        cU = min(okU, key=key) if okU else min(cand, key=lambda c: (cand[c]['agent_up'], c))
        ch[t] = dict(choice=cU, rule='qualified' if okU else 'fallback: min agent-TL upper', n_qualified=len(okU), table=cand)
        v = cand[cU]; out.append(f't{t}: R15-U {cU} (H4 {v["fuel_H4"]:+.2f} P5 {v["fuel_P5"]:+.2f} agent {v["agent"]:+.2f} up {v["agent_up"]:+.2f}; {len(okU)} qualified)'
                                 + ' | default grid:1,0.25,0.1 ' + (f'H4 {cand["grid:1,0.25,0.1"]["fuel_H4"]:+.2f} P5 {cand["grid:1,0.25,0.1"]["fuel_P5"]:+.2f} agent {cand["grid:1,0.25,0.1"]["agent"]:+.2f}' if 'grid:1,0.25,0.1' in cand else ''))
    (D / 'tune' / 'choice_U.json').write_text(json.dumps(ch, indent=1)); (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
elif cmd == 'report':                                                   # W16-4 confirmation on fresh 1280-1299
    CS = [860] if SM else list(range(1340, 1360)); Rt = rows(D / 'conf')
    for a in ('R', 'TG', 'TU', 'F1B'):
        for l in LT:
            for f in FL:
                for s in CS:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    out = [f'== W17-4 TSI in the field-matched world (lights t{LT[0]}-t{LT[-1]}, fleets {FL}, fresh {CS[0]}-{CS[-1]}; HBEFA4 / PHEMlight5)', 'KM13-1a PASS, KM13-1b PASS']
    r = V.paired(Rt, K('TG'), K('R'), LT, FL, CS); ok, tl = V.limits(r, V.tele(Rt, K('TG'), LT, FL, CS), V.tele(Rt, K('R'), LT, FL, CS))
    r5 = V.paired(Rt, K('TGP5'), K('RP5'), LT, FL, CS); d2 = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    f5 = V.paired(Rt, K('TGP5'), K('F1BP5'), LT, FL, CS); d3 = ok and f5['fuel_agent']['up'] < 0.5
    out += ['-- D17-2 (alpha 0.05)', V.line('TG - R (H4)', r), f'  TG all M3 limits: {ok}; {tl}', V.line('TG - R (P5)', r5), f'  D17-2 VERDICT: {"SHOWN" if d2 else "NOT SHOWN"}',
            '-- D17-3 (alpha 0.05; PHEMlight5)', V.line('TG - F1B (P5)', f5), f'  D17-3 VERDICT: fuel non-inferiority to F1B retrained in this world {"ESTABLISHED" if d3 else "NOT ESTABLISHED"}',
            '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in (('TU', 'R'), ('TU', 'TG'), ('F1B', 'R'), ('TG', 'F1B')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, CS)))
    (D / 'conf' / 'report_w17.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
