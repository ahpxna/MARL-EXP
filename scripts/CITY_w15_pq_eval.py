#!/usr/bin/env python3
"""W15-4 (PROTOCOL_CITY_WAVE15_20261007, Amendment A1): projected-queue adapter, selection and report for one network.
  select <mode> <dir>   candidates (tau in {3, 5, 10, 15}) x (q in {0.1, 0.5}) tagged P_<k>_tau<tau>_q01 / _q05 (+ _P5); rule R13-RB
                        (agent / city / human TL points <= 0 on TUNE, then min of max(fuel_H4, fuel_P5); none -> min agent TL; ties smaller tau,
                        then q 0.5).  KM13-1a on every candidate.  -> <dir>/tune/choice_P.json
  report <mode> <dir>   fresh traffic; arms R, REF (grid4: TRB = W13 choice; spider: TRB = W14-3 choice; rand3: TOLD = W10-6 choice) and TP,
                        each with a PHEMlight5 twin; decision: TP meets every M3 limit and TP - R fuel upper < 0 under both models at the mode's
                        alpha (grid4 / rand3 0.05; spider 0.0015625, sixth attempt).
modes: grid4 (FRESH2 t14-t18 x s1013-s1313, TUNE 660-663, conf 1180-1199), spider (RLK 11 / 111 x rule fleet, TUNE 1100-1103, conf
1210-1229), rand3 (RL-H t21-t25 x N3 s213-s513, TUNE 660-663, conf 740-759).   W15_SMOKE=1: first light / fleet, one seed."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, mode, D = sys.argv[1], sys.argv[2], Path(sys.argv[3]); SM = os.environ.get('W15_SMOKE') == '1'
CFG = dict(grid4=dict(L=(14, 15, 16, 17, 18), F=('s1013', 's1113', 's1213', 's1313'), T=[660, 661, 662, 663], C=list(range(1180, 1200)), alpha=0.05, ref='TRB',
                      rtag=lambda k: f'R_t{k}', key=lambda a: (lambda l, f: f'{a}_t{l}_{f}')),
           spider=dict(L=(11, 111), F=('rule',), T=[1100, 1101, 1102, 1103], C=list(range(1210, 1230)), alpha=0.0015625, ref='TRB',
                       rtag=lambda k: f'R_{k}', key=lambda a: (lambda l, f: f'{a}_{l}')),
           rand3=dict(L=(21, 22, 23, 24, 25), F=('s213', 's313', 's413', 's513'), T=[660, 661, 662, 663], C=list(range(740, 760)), alpha=0.05, ref='TOLD',
                      rtag=lambda k: f'R_t{k}', key=lambda a: (lambda l, f: f'{a}_t{l}_{f}')))[mode]
L = CFG['L'][:1] if SM else CFG['L']; FL = CFG['F'][:1] if SM else CFG['F']; TS = [int(os.environ.get('W15_TSEED', CFG['T'][0]))] if SM else CFG['T']
CS = [int(os.environ.get('W15_SEED', 860))] if SM else CFG['C']; TAUS = (3, 5, 10, 15); QS = (0.1, 0.5)
ptag = lambda k, tau, q: (f'P_t{k}' if mode != 'spider' else f'P_{k}') + f'_tau{tau}_q{"01" if q == 0.1 else "05"}'  # noqa: E731
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished')
if cmd == 'select':
    Rt = rows(D / 'tune'); out = [f'== W15-4 projected-queue selection, {mode} (TUNE {TS})']; ch = {}
    for k in L:
        R = {x: Rt[CFG['rtag'](k) + x] for x in ('', '_P5')}; tab = {}
        for tau in TAUS:
            for q in QS:
                X = {x: Rt[ptag(k, tau, q) + x] for x in ('', '_P5')}
                for s in TS:
                    if any(X[''][s][t] != X['_P5'][s][t] for t in TW):
                        print('KM13-1a FAIL', ptag(k, tau, q), s); sys.exit(1)
                f4, f5 = (float(100 * (np.mean([X[x][s]['fuel_agent'] for s in TS]) / np.mean([R[x][s]['fuel_agent'] for s in TS]) - 1)) for x in ('', '_P5'))
                tab[f'{tau},{q:g}'] = dict(fuel_H4=f4, fuel_P5=f5, **{t: float(np.mean([X[''][s][t] - R[''][s][t] for s in TS])) for t in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= 0 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        tie = lambda c: (float(c.split(',')[0]), 0 if c.endswith(',0.5') else 1)  # noqa: E731
        c = min(ok, key=lambda c: (max(tab[c]['fuel_H4'], tab[c]['fuel_P5']),) + tie(c)) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'],) + tie(c))
        ch[k] = dict(choice=c, qualified=ok, rule='qualified' if ok else 'fallback: min agent TL', table=tab)
        out.append(f'{k}: choose tau,q = {c} ({ch[k]["rule"]}, {len(ok)} qualified): ' + ' '.join(f'{t}:{v:+.2f}' for t, v in tab[c].items()))
        for cc, v in sorted(tab.items()):
            out.append(f'    {cc:>7}: H4 {v["fuel_H4"]:+.2f} P5 {v["fuel_P5"]:+.2f} agent {v["timeloss_agent"]:+.2f} city {v["timeloss"]:+.2f} human {v["timeloss_human"]:+.2f}' + ('  *' if cc in ok else ''))
    (D / 'tune' / 'choice_P.json').write_text(json.dumps(ch, indent=1)); (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = CFG['key']; Rt = rows(D / 'conf'); ref = CFG['ref']; qq = 100 * (1 - CFG['alpha'])
    for a in ('R', ref, 'TP'):
        for l in L:
            for f in FL:
                for s in CS:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[t] != p[t] for t in TW) or not (0.98 <= h.get('modes_ratio_all', 0) <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    out = [f'== W15-4 projected-queue adapter, {mode} (fresh {CS[0]}-{CS[-1]}; alpha {CFG["alpha"]} one-sided)', 'KM13-1a PASS, KM13-1b PASS']
    r = V.paired(Rt, K('TP'), K('R'), L, FL, CS, q=qq); ok, tl = V.limits(r, V.tele(Rt, K('TP'), L, FL, CS), V.tele(Rt, K('R'), L, FL, CS))
    r5 = V.paired(Rt, K('TPP5'), K('RP5'), L, FL, CS, q=qq); v = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    out += [V.line('TP - R (H4)', r), f'  TP all M3 limits: {ok}; {tl}', V.line('TP - R (P5)', r5), f'  D15-4 ({mode}) VERDICT: {"PASS" if v else "FAIL"}',
            '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in ((ref, 'R'), ('TP', ref), ('TP', 'R')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), L, FL, CS)))
    (D / 'conf' / 'report_pq.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
