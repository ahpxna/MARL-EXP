#!/usr/bin/env python3
"""W15-6 (PROTOCOL_CITY_WAVE15_20261007, Amendment A2): policy-aware forecaster, selection and report (FRESH2 t14-t18).
  select <dir>  candidates per light: prf, prfq (CITY_w15_prf at adapter (1, 0.25), wrapped provider at q 0.1; rows <dir>/tune/F_t<k>_<v>[_P5])
                and tg (the default, rows w13 tune T_t<k>_a1_b0p25_q01[_P5]); rule R13-RB vs R (fresh2 / w13 tune rows) -> choice_PRF.json
  report <dir>  fresh traffic 1260-1279: R, TG, TPRF (chosen variant) x HBEFA4 / PHEMlight5 (s1013-s1313).
     D15-6 (alpha 0.05): TPRF meets every M3 limit and TPRF - R fuel upper < 0 under both models.  Descriptive: TPRF - TG; the projected
     switch-time error (sidecars: PRF vs the wrapped network, queried green seconds).   W15_SMOKE=1: t14, TUNE 660, conf 860."""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W15_SMOKE') == '1'
F2 = ROOT / 'research/city_sim/w8_20261005/fresh2'; W13 = ROOT / 'research/city_sim/w13_20261006'
LT = (14,) if SM else (14, 15, 16, 17, 18); TS = [660] if SM else [660, 661, 662, 663]
FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313'); CS = [860] if SM else list(range(1260, 1280))
if cmd == 'select':
    Rt = {**({} if SM else {**rows(F2 / 'tune'), **rows(W13 / 'tune')}), **rows(D / 'tune')}; out = ['== W15-6 selection (TUNE ' + ','.join(map(str, TS)) + ')']; ch = {}
    for k in LT:
        R = {x: Rt[f'R_t{k}{x}'] for x in ('', '_P5')}; tab = {}
        for v, tg in (('prf', f'F_t{k}_prf'), ('prfq', f'F_t{k}_prfq'), ('tg', f'T_t{k}_a1_b0p25_q01')):
            if tg not in Rt:
                continue
            X = {x: Rt[tg + x] for x in ('', '_P5')}
            for s in TS:
                if any(X[''][s][t] != X['_P5'][s][t] for t in ('timeloss', 'n', 'teleports')):
                    print('KM13-1a FAIL', tg, s); sys.exit(1)
            f4, f5 = (float(100 * (np.mean([X[x][s]['fuel_agent'] for s in TS]) / np.mean([R[x][s]['fuel_agent'] for s in TS]) - 1)) for x in ('', '_P5'))
            tab[v] = dict(fuel_H4=f4, fuel_P5=f5, **{t: float(np.mean([X[''][s][t] - R[''][s][t] for s in TS])) for t in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, w in tab.items() if w['timeloss_agent'] <= 0 and w['timeloss'] <= 0 and w['timeloss_human'] <= 0]
        c = min(ok, key=lambda c: (max(tab[c]['fuel_H4'], tab[c]['fuel_P5']), c)) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], c))
        ch[k] = dict(choice=c, qualified=ok, table=tab)
        out.append(f't{k}: choose {c} ({len(ok)} qualified) | ' + ' | '.join(f'{v} H4 {w["fuel_H4"]:+.2f} P5 {w["fuel_P5"]:+.2f} agent {w["timeloss_agent"]:+.2f}' for v, w in tab.items()))
    (D / 'tune' / 'choice_PRF.json').write_text(json.dumps(ch, indent=1)); (D / 'tune' / 'report_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    Rt = rows(D / 'conf'); TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
    for a in ('R', 'TG', 'TPRF'):
        for l in LT:
            for f in FL:
                for s in CS:
                    h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                    if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                        print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
    out = [f'== W15-6 policy-aware forecaster (FRESH2, fresh {CS[0]}-{CS[-1]}; HBEFA4 / PHEMlight5)', 'KM13-1a PASS, KM13-1b PASS',
           'choices: ' + ', '.join(f't{k} {v["choice"]}' for k, v in json.loads((D / 'tune' / 'choice_PRF.json').read_text()).items())]
    r = V.paired(Rt, K('TPRF'), K('R'), LT, FL, CS); ok, tl = V.limits(r, V.tele(Rt, K('TPRF'), LT, FL, CS), V.tele(Rt, K('R'), LT, FL, CS))
    r5 = V.paired(Rt, K('TPRFP5'), K('RP5'), LT, FL, CS); v = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
    out += ['-- D15-6 (alpha 0.05)', V.line('TPRF - R (H4)', r), f'  TPRF all M3 limits: {ok}; {tl}', V.line('TPRF - R (P5)', r5),
            f'  D15-6 VERDICT: {"SHOWN" if v else "NOT SHOWN"}', '-- descriptive (one-sided 95 %)']
    for x in ('', 'P5'):
        for a, b in (('TG', 'R'), ('TPRF', 'TG')):
            out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, CS)))
    agg = dict(sw_err_n=0, sw_err_abs=0.0, sw_err_sum=0.0, mlp_err_n=0, mlp_err_abs=0.0, mlp_err_sum=0.0)
    for p in (D / 'conf').glob('TPRF_t*_n4.json'):
        s = json.loads(p.read_text())
        for k in agg:
            agg[k] += s.get(k, 0)
    if agg['sw_err_n']:
        out.append(f'  switch-time error on queried green seconds (TPRF rows, HBEFA4): projection MAE {agg["sw_err_abs"] / agg["sw_err_n"]:.2f} s, bias '
                   f'{agg["sw_err_sum"] / agg["sw_err_n"]:+.2f} (n {agg["sw_err_n"]}); wrapped network MAE {agg["mlp_err_abs"] / max(1, agg["mlp_err_n"]):.2f} s, '
                   f'bias {agg["mlp_err_sum"] / max(1, agg["mlp_err_n"]):+.2f} (n {agg["mlp_err_n"]})')
    (D / 'conf' / 'report_prf.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
