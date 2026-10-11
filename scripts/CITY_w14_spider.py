#!/usr/bin/env python3
"""W14-3 (PROTOCOL_CITY_WAVE14_20261007, Amendment A1): the W13 method on the original one-lane spider (lights RLK 11 / 111, rule fleet
GLOSAL:0.3, attempt-1 N2K networks and tables).  Grid: the union of the two registered spider adapter grids x q in {0.1, 0.5} x {HBEFA4,
PHEMlight5} on TUNE 1100-1103 (q 0.5 HBEFA4 rows reused from sptsi_20261005/tune and tune2).  Rule R13-RB as in W13.
  select <dir>   writes <dir>/tune/choice_RB.json, report_select.txt (KM13-1a: P5 dynamics == H4)
  report <dir>   fresh spider traffic 1190-1209: R, TOLD (attempt-1 choice, q 0.5), TRB, each with a PHEMlight5 twin.
     D14-3 (fifth attempt of the one-lane spider chain, alpha 0.003125 one-sided): TRB meets every M3 limit vs R (HBEFA4) and TRB - R
     fuel upper < 0 under HBEFA4 and PHEMlight5.  Descriptive at one-sided 95 %.   W14_SMOKE=1: light 11, TUNE 1100, seed 1100."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W14_SMOKE') == '1'; ST = ROOT / 'research/city_sim/sptsi_20261005'
LK = (11,) if SM else (11, 111); TS = [1100] if SM else [1100, 1101, 1102, 1103]; CS = [1100] if SM else list(range(1190, 1210))
GRID = [(0, 0), (1, 0), (2, 0), (1, 0.25), (1.5, 0.25), (1, 0.5), (2, 0.5), (1, 0.75), (2, 0.75), (1, 1.0), (2, 1.0)]
tag = lambda k, a, b: f'T_{k}_a{a:g}_b{b:g}'.replace('.', 'p')  # noqa: E731
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished')
if cmd == 'select':
    Rt = {**({} if SM else {**rows(ST / 'tune'), **rows(ST / 'tune2')}), **rows(D / 'tune')}
    name = lambda k, a, b, q, em: (f'R_{k}' if a is None else tag(k, a, b) + ('_q01' if q == 0.1 else '')) + ('_P5' if em == 'P5' else '')  # noqa: E731
    for k in LK:
        for a, b, q in [(None, None, 0.5)] + [(a, b, q) for a, b in GRID for q in (0.5, 0.1)]:
            for s in TS:
                x, y = Rt[name(k, a, b, q, 'H4')][s], Rt[name(k, a, b, q, 'P5')][s]
                if any(x.get(t) != y.get(t) for t in TW):
                    print('KM13-1a FAIL', name(k, a, b, q, 'P5'), s); sys.exit(1)
    out = ['== W14-3 one-lane spider selection (TUNE ' + ','.join(map(str, TS)) + ')', 'KM13-1a PASS']; ch = {}
    for k in LK:
        R = {em: Rt[name(k, None, None, 0.5, em)] for em in ('H4', 'P5')}; tab = {}
        for a, b in GRID:
            for q in (0.5, 0.1):
                X = {em: Rt[name(k, a, b, q, em)] for em in ('H4', 'P5')}
                fu = {em: float(100 * (np.mean([X[em][s]['fuel_agent'] for s in TS]) / np.mean([R[em][s]['fuel_agent'] for s in TS]) - 1)) for em in ('H4', 'P5')}
                tab[f'{a:g},{b:g},{q:g}'] = dict(fuel_H4=fu['H4'], fuel_P5=fu['P5'], **{t: float(np.mean([X['H4'][s][t] - R['H4'][s][t] for s in TS]))
                                                                                         for t in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= 0 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        tie = lambda c: (float(c.split(',')[0]) + float(c.split(',')[1]), 0 if c.endswith(',0.5') else 1)  # noqa: E731
        c = (min(ok, key=lambda c: (max(tab[c]['fuel_H4'], tab[c]['fuel_P5']),) + tie(c)) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'],) + tie(c)))
        ch[k] = dict(choice=c, qualified=ok, rule='qualified' if ok else 'fallback: min agent TL', table=tab)
        out.append(f'RLK{k}: {len(ok)} qualified -> {c} ({ch[k]["rule"]}): ' + ' '.join(f'{t}:{v:+.2f}' for t, v in tab[c].items()))
        for cc, v in sorted(tab.items(), key=lambda kv: kv[1]['timeloss_agent']):
            out.append(f'    {cc:>11}: H4 {v["fuel_H4"]:+.2f} P5 {v["fuel_P5"]:+.2f} agent {v["timeloss_agent"]:+.2f} city {v["timeloss"]:+.2f} human {v["timeloss_human"]:+.2f}' + ('  *' if cc in ok else ''))
    (D / 'tune' / 'choice_RB.json').write_text(json.dumps(ch, indent=1)); (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
    FL = ('rule',); Rt = rows(D / 'conf'); q = 100 - 0.3125
    for a in ('R', 'TOLD', 'TRB'):
        for k in LK:
            for s in CS:
                h, p = Rt[f'{a}_{k}'][s], Rt[f'{a}P5_{k}'][s]
                if any(h[t] != p[t] for t in TW) or not (0.98 <= h.get('modes_ratio_all', 0) <= 1.02):
                    print('KM13-1a/1b FAIL', a, k, s); sys.exit(1)
    out = ['== W14-3 one-lane spider, W13 method (fresh 1190-1209; RLK 11 / 111 x rule fleet x 20; HBEFA4 / PHEMlight5)', 'KM13-1a PASS, KM13-1b PASS']
    r = V.paired(Rt, K('TRB'), K('R'), LK, FL, CS, q=q); ok, tl = V.limits(r, V.tele(Rt, K('TRB'), LK, FL, CS), V.tele(Rt, K('R'), LK, FL, CS))
    r5 = V.paired(Rt, K('TRBP5'), K('RP5'), LK, FL, CS, q=q); v = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    out += ['-- D14-3 (alpha 0.003125 one-sided; fifth attempt)', V.line('TRB - R (H4)', r), f'  TRB all M3 limits: {ok}; {tl}', V.line('TRB - R (P5)', r5),
            f'  D14-3 VERDICT: {"PASS" if v else "FAIL"}', '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in (('TOLD', 'R'), ('TRB', 'R'), ('TRB', 'TOLD')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LK, FL, CS)))
    (D / 'conf' / 'report_spider.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
