#!/usr/bin/env python3
"""Wave-9 reports (PROTOCOL_CITY_WAVE9_20261005), strict loader (CITY_w6_validation.rows) and the v2 helpers (crossed bootstrap, CITY_wave2_report_v2
draws; M3 limits incl. teleports AND unfinished).  Usage: CITY_w9_report.py robust | global | mp      (W9_SMOKE=<dir>: smoke, one cell, seed 780 / 820)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W9_SMOKE')); W = Path(os.environ['W9_SMOKE']) if SM else ROOT / 'research/city_sim/w9_20261005'
CS = ROOT / 'research/city_sim'; W7 = CS / 'w7_20261005/fpr'; F2 = CS / 'w8_20261005/fresh2'
TLQ = ('timeloss', 'timeloss_agent', 'timeloss_human')


def load(*dirs, S=None):
    Rt = {}
    for d in dirs:
        for k, v in rows(d).items():
            assert k not in Rt, f'duplicate key {k}'
            Rt[k] = {s: r for s, r in v.items() if S is None or s in S} if SM else v
    return Rt


def arm(Rt, K, a, b, LT, FL, S, out):
    r = V.paired(Rt, K(a), K(b), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K(b), LT, FL, S))
    out += [V.line(f'{a} - {b}', r), f'  {a}: all M3 limits vs {b} (incl. teleports, unfinished): {ok}; {tl}']
    return ok, r


def same(Rt, ka, kb, LT, FL, S, qs=TLQ + ('n',)):
    bad = [(l, f, s, q) for l in LT for f in FL for s in S for q in qs if abs(Rt[ka(l, f)][s][q] - Rt[kb(l, f)][s][q]) > 1e-9]
    return not bad, bad[:3]


def robust():
    S = [780] if SM else list(range(780, 800)); LT = (9,) if SM else (9, 10, 11, 12, 13); FL = ('s613',) if SM else ('s613', 's713', 's813', 's913')
    D = W / 'robust'; Rt = load(W7 / 'conf', D / 'conf', S=S); K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    out = ['== W9-1..W9-4 robustness of the frozen TSI design (W7-1 fresh-policy panel: lights t9-t13 x fleets s613-s913 x traffic 780-799; '
           'W7-1 providers and per-light adapters unchanged; descriptive, one-sided 95 % per arm)']
    out.append('-- W9-1 COMM (fleet side: SPaT latency / loss) and W9-2 SENSE (light side: adapter detection / speed noise); vs the W7-1 R rows')
    for a in ('TSI', 'TSI_LAT1', 'TSI_LOSS20', 'TSI_LOSS50', 'TSI_DET80', 'TSI_SPN1'):
        arm(Rt, K, a, 'R', LT, FL, S, out)
        if a != 'TSI':
            out.append(V.line(f'{a} - TSI (cost of the perturbation)', V.paired(Rt, K(a), K('TSI'), LT, FL, S)))
    out.append('-- W9-3 EMIS (PHEMlight5/PC_EU4_G; default HBEFA4/PC_petrol_Euro-4)')
    k1, b1 = same(Rt, K('R_EM2'), K('R'), LT, FL, S); k2, b2 = same(Rt, K('TSI_EM2'), K('TSI'), LT, FL, S)
    out.append(f'  KW9-3 self-check (time losses and vehicle counts identical to the W7-1 rows): R {k1} {b1} | TSI {k2} {b2}')
    if k1 and k2:
        arm(Rt, K, 'TSI_EM2', 'R_EM2', LT, FL, S, out)
    else:
        out.append('  W9-3 VOID (self-check failed)')
    out.append('-- W9-4 IDM (every vehicle --carfollow.model IDM; all policies trained / fitted under Krauss)')
    arm(Rt, K, 'TSI_IDM', 'R_IDM', LT, FL, S, out); out.append(V.line('R_IDM - R (the model change itself)', V.paired(Rt, K('R_IDM'), K('R'), LT, FL, S)))
    (D / 'report_robust.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


def glob_():
    D = W / 'robust'; out = ['== W9-5 GLOBAL adapter (A, B) = (1, 0.5), fixed from the TSI-2 lights t4-t8 (smallest A qualified on all five)']
    S = [780] if SM else list(range(780, 800)); LT = (9,) if SM else (9, 10, 11, 12, 13); FL = ('s613',) if SM else ('s613', 's713', 's813', 's913')
    Rt = load(W7 / 'conf', D / 'glob', S=S); ch = json.loads((W7 / 'tune' / 'choice.json').read_text())
    for l in LT:
        if ch[str(l)]['choice'] == '1,0.5':
            for f in FL:
                assert f'TSIG_t{l}_{f}' not in Rt; Rt[f'TSIG_t{l}_{f}'] = Rt[f'TSI_t{l}_{f}']        # identical configuration: W7-1 TSI rows reused
    K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    if not SM:
        c = rows(D / 'check')['KW95_t10_s613'][780]; w = Rt['TSI_t10_s613'][780]
        ok = all(abs(c[q] - w[q]) < 1e-9 for q in TLQ + ('fuel_agent', 'n')); out.append(f'  KW9-5 identity (TSI_G t10 s613 seed 780 == W7-1 TSI row): {ok}')
    out.append('-- (b) secondary, W7-1 panel (t9 / t11 / t12 run with (1, 0.5); t10 / t13 reuse their W7-1 rows; W7-1 grids were seen before registration)')
    okb, _ = arm(Rt, K, 'TSIG', 'R', LT, FL, S, out); out.append(V.line('TSIG - TSI (global minus per-light)', V.paired(Rt, K('TSIG'), K('TSI'), LT, FL, S)))
    if not SM:
        if (F2 / 'report_fresh2.txt').exists() and all((D / 'glob' / f'TSIG_t{l}_s{f}.json').exists() for l in (14, 15, 16, 17, 18) for f in (1013, 1113, 1213, 1313)):
            S2 = list(range(800, 820)); L2 = (14, 15, 16, 17, 18); F2L = ('s1013', 's1113', 's1213', 's1313'); R2 = load(F2 / 'conf', D / 'glob')
            out.append('-- (a) REGISTERED: W8-2 FRESH2 panel (lights t14-t18 x fleets s1013-s1313 x traffic 800-819), FRESH2 providers, adapter (1, 0.5)')
            oka, _ = arm(R2, K, 'TSIG', 'R', L2, F2L, S2, out); out.append(V.line('TSIG - TSI (global minus FRESH2 per-light)', V.paired(R2, K('TSIG'), K('TSI'), L2, F2L, S2)))
            out.append(f'  W9-5 (a) CALIBRATION-FREE ADAPTER VERDICT (alpha 0.05 one-sided): {"PASS" if oka else "FAIL"}')
        else:
            out.append('  W9-5 (a) NOT RUN: FRESH2 incomplete')
    (D / 'report_global.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


def mp():
    D = W / 'mp'; S = [int(os.environ.get('W9_SEED', 820))] if SM else list(range(820, 840)); FL = ('s613',) if SM else ('s613', 's713', 's813', 's913')
    Rt = load(D / 'conf', S=S)                                         # one light per arm: the tag carries the light
    L1 = ('MP',); L0 = ('FT',); KL = lambda a, lt: (lambda l, f: f'{a}_{lt}_{f}')  # noqa: E731
    out = ['== W9-6 MP: MaxPressure (Varaiya 2013) as the upgraded signal; W7-1 fleets s613-s913; fresh grid4 traffic 820-839; one light: bootstrap over fleet x traffic']
    pre = V.paired(Rt, KL('PL', 'FT'), KL('R', 'FT'), L0, FL, S); out += [V.line('(a) PL_FT - R_FT (fleet benefit under FT, precondition)', pre),
                                                                           f'  (a) precondition (agent fuel upper < 0): {pre["fuel_agent"]["up"] < 0}']
    nv = V.paired(Rt, KL('NAIVE', 'MP'), KL('R', 'MP'), L1, FL, S); harm = nv['fuel_agent']['low'] > 0 or nv['timeloss_agent']['low'] > 0
    out += [V.line('(b) NAIVE_MP - R_MP (program SPaT under MP)', nv), f'  (b) harm (agent fuel or agent TL lower > 0): {harm}']
    dd = V.did(Rt, KL('NAIVE', 'MP'), KL('R', 'MP'), L1, KL('PL', 'FT'), KL('R', 'FT'), L0, FL, S); out.append(V.line('(b) DiD naive: (NAIVE_MP - R_MP) - (PL_FT - R_FT)', dd))
    for a in ('C2', 'HYB'):
        r = V.paired(Rt, KL(a, 'MP'), KL('R', 'MP'), L1, FL, S); ok, tl = V.limits(r, V.tele(Rt, KL(a, 'MP'), L1, FL, S), V.tele(Rt, KL('R', 'MP'), L1, FL, S))
        out += [V.line(f'{a}_MP - R_MP', r), f'  {a}_MP: all M3 limits vs R_MP (incl. teleports, unfinished): {ok}; {tl}']
        if a == 'HYB':
            verdict = ok
        out.append(V.line(f'(e) recovery DiD: ({a}_MP - R_MP) - (PL_FT - R_FT)', V.did(Rt, KL(a, 'MP'), KL('R', 'MP'), L1, KL('PL', 'FT'), KL('R', 'FT'), L0, FL, S)))
    g = lambda a, q: sum(Rt[f'{a}_MP_{f}'][s][q] for f in FL for s in S) / (len(FL) * len(S))  # noqa: E731
    out.append('  (d) mechanism probe, mean green (s) / mean halting: ' + '; '.join(f'{a} {g(a, "green_mean"):.1f} / {g(a, "mean_halting"):.2f}' for a in ('R', 'NAIVE', 'C2', 'HYB'))
               + '   (grid4 RL-H reference, TSI-2 panel: R 15.0 / 2.91, HYB 17.1 / 1.63)')
    out.append(f'  W9-6 (c) MECHANISM PREDICTION (HYB_MP meets every M3 limit vs R_MP; predicted YES): {"CONFIRMED" if verdict else "NOT CONFIRMED"}')
    (D / 'report_mp.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    dict(robust=robust, mp=mp, **{'global': glob_})[sys.argv[1]]()
