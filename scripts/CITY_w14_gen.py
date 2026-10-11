#!/usr/bin/env python3
"""W14-1 (PROTOCOL_CITY_WAVE14_20261007): does the W13 method (per-light (A, B, q) with the robust rule R13-RB) generalize to the earlier
grid4 panels?  One script, two commands, a panel JSON (written by the job):
  {"name", "dir", "lights": [...], "fleets": [...], "tune_old": <dir with q = 0.5 HBEFA4 tuning rows R_t<k>, T_t<k>_a<A>_b<B>>,
   "choice_old": <the panel's registered adapter choice json>, "tune_seeds": [...], "conf_seeds": [...], "f1b": bool}
  select <panel.json>   the CITY_w13_select rules on <dir>/tune (+ tune_old): R13-F and R13-RB; KM13-1a; writes choice_F/RB.json.
  report <panel.json>   <dir>/conf: arms R, TOLD (panel's choice, q 0.5), TRB, TF (and F1B if f1b), each with a P5 twin.
    D14-1 (alpha 0.05 one-sided): TRB meets every M3 limit vs R and TRB - R fuel upper < 0 under HBEFA4 and under PHEMlight5.
    D14-2 (alpha 0.05, only if f1b): TRB - F1B fuel (HBEFA4) upper < +0.5 pp.
  KM13-1a / KM13-1b on every row.  W14_SMOKE=1 trims to the first light / fleet / seed."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, P = sys.argv[1], json.loads(Path(sys.argv[2]).read_text()); SM = os.environ.get('W14_SMOKE') == '1'
D = Path(P['dir']); LT = P['lights'][:1] if SM else P['lights']; FL = P['fleets'][:1] if SM else P['fleets']
TS = P['tune_seeds'][:1] if SM else P['tune_seeds']; CS = P['conf_seeds'][:1] if SM else P['conf_seeds']
GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)]
tag = lambda t, a, b: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p')  # noqa: E731
TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
if cmd == 'select':
    Rt = {**({} if SM else rows(ROOT / P['tune_old'])), **rows(D / 'tune')}
    name = lambda t, a, b, q, em: (f'R_t{t}' if a is None else tag(t, a, b) + ('_q01' if q == 0.1 else '')) + ('_P5' if em == 'P5' else '')  # noqa: E731
    for t in LT:
        for a, b, q in [(None, None, 0.5)] + [(a, b, q) for a, b in GRID for q in (0.5, 0.1)]:
            for s in TS:
                x, y = Rt[name(t, a, b, q, 'H4')][s], Rt[name(t, a, b, q, 'P5')][s]
                if any(x.get(k) != y.get(k) for k in TW):
                    print('KM13-1a FAIL', name(t, a, b, q, 'P5'), s); sys.exit(1)
    out = [f'== W14-1 selection, panel {P["name"]} (TUNE {TS})', 'KM13-1a PASS']; chF, chRB, tables = {}, {}, {}
    for t in LT:
        R = {em: Rt[name(t, None, None, 0.5, em)] for em in ('H4', 'P5')}; tab = {}
        for a, b in GRID:
            for q in (0.5, 0.1):
                X = {em: Rt[name(t, a, b, q, em)] for em in ('H4', 'P5')}
                fu = {em: float(100 * (np.mean([X[em][s]['fuel_agent'] for s in TS]) / np.mean([R[em][s]['fuel_agent'] for s in TS]) - 1)) for em in ('H4', 'P5')}
                tab[f'{a:g},{b:g},{q:g}'] = dict(fuel_H4=fu['H4'], fuel_P5=fu['P5'], **{k: float(np.mean([X['H4'][s][k] - R['H4'][s][k] for s in TS]))
                                                                                         for k in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= 0 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        tie = lambda c: (float(c.split(',')[0]) + float(c.split(',')[1]), 0 if c.endswith(',0.5') else 1)  # noqa: E731
        pick = lambda f: (min(ok, key=lambda c: (f(tab[c]),) + tie(c)) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'],) + tie(c)))  # noqa: E731
        cF, cRB = pick(lambda v: v['fuel_H4']), pick(lambda v: max(v['fuel_H4'], v['fuel_P5'])); rule = 'qualified' if ok else 'fallback'
        chF[t] = dict(choice=cF, rule=rule); chRB[t] = dict(choice=cRB, rule=rule); tables[t] = tab
        out.append(f't{t}: {len(ok)} qualified | R13-F {cF} (H4 {tab[cF]["fuel_H4"]:+.2f} P5 {tab[cF]["fuel_P5"]:+.2f}) | R13-RB {cRB} '
                   f'(H4 {tab[cRB]["fuel_H4"]:+.2f} P5 {tab[cRB]["fuel_P5"]:+.2f} agent {tab[cRB]["timeloss_agent"]:+.2f}) | {rule}')
    for p, d in (('choice_F.json', chF), ('choice_RB.json', chRB), ('tables.json', tables)):
        (D / 'tune' / p).write_text(json.dumps(d, indent=1))
    (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    Rt = rows(D / 'conf'); arms = ['R', 'TOLD', 'TRB', 'TF'] + (['F1B'] if P.get('f1b') else [])
    for a in arms:
        for l in LT:
            for f in FL:
                for s in CS:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[k] != p[k] for k in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    out = [f'== W14-1 confirmation, panel {P["name"]} (lights {LT}, fleets {FL}, fresh traffic {CS[0]}-{CS[-1]}; HBEFA4 / PHEMlight5)', 'KM13-1a PASS, KM13-1b PASS']
    r = V.paired(Rt, K('TRB'), K('R'), LT, FL, CS); ok, tl = V.limits(r, V.tele(Rt, K('TRB'), LT, FL, CS), V.tele(Rt, K('R'), LT, FL, CS))
    r5 = V.paired(Rt, K('TRBP5'), K('RP5'), LT, FL, CS); v1 = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    out += ['-- D14-1 (alpha 0.05 one-sided)', V.line('TRB - R (H4)', r), f'  TRB all M3 limits: {ok}; {tl}', V.line('TRB - R (P5)', r5),
            f'  D14-1 VERDICT: the W13 method saves fuel under both emission models on this panel {"SHOWN" if v1 else "NOT SHOWN"}']
    if P.get('f1b'):
        d = V.paired(Rt, K('TRB'), K('F1B'), LT, FL, CS)
        out += ['-- D14-2 (alpha 0.05 one-sided)', V.line('TRB - F1B (H4)', d),
                f'  D14-2 VERDICT: fuel non-inferiority to F1B {"ESTABLISHED" if ok and d["fuel_agent"]["up"] < 0.5 else "NOT ESTABLISHED"}']
    out.append('-- descriptive (one-sided 95 %)')
    for x in ('', 'P5'):
        for a, b in [('TOLD', 'R'), ('TRB', 'TOLD'), ('TF', 'R'), ('TF', 'TRB')] + ([('F1B', 'R'), ('TRB', 'F1B')] if P.get('f1b') else []):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, CS)))
    (D / 'conf' / 'report_gen.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
