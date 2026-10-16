#!/usr/bin/env python3
"""W21-C report (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-C): where the Midtown time cost of the forecast comes from.
Rows and logs in <dir> (scripts/RUN_w21c_midtown_diag.sh).  The matcher is CITY_w10_diag.match (unchanged) with the static-program link
states of midtown_full.net.xml (the AI lights switch inside it).
  KW21-C0  under FT the fleet's program SPaT equals realized + c, one offset per field, on every valid uncensored query (FTX, day 0)
  KW21-C1  SHADOWg rows equal W21-B's MTW_R rows (the shadow is the R dynamics plus logging; skipped in smoke)
  C1       served-answer MAE / bias / >5 s share, SERVE vs SHADOW, grid vs refit forecaster; agent time SERVE - SHADOW (= SV - R)
  C2       held human-seconds per commanded agent-second (W10-3 counters)
  C3       SIG (sigma* replay) and ORC (exact future timing) on each light's SHADOWg schedule: ORC - SIG; KH-1 for every light
Descriptive (95 % bootstrap over lights x days).  Usage: CITY_w21c_report.py <dir> "<AH lights>" "<B2D lights>" "<refit lights>" """
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w10_diag as WD  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]); LA, LB, LR = ([int(x) for x in a.split()] for a in sys.argv[2:5]); SM = os.environ.get('W21_SMOKE') == '1'
W21B = ROOT / 'research/city_sim/w21_20261015/midtown'; FIELDS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'waiting', 'teleports', 'unfinished', 'action_digest')
Rt = rows(D); ST = WD.states(ROOT / 'research/city_sim/net/midtown_full.net.xml'); DAYS = sorted(Rt[f'SHADOWg_t{LA[0]}'].keys())
out = [f'== W21-C: Midtown diagnosis (MT-E setting, fleet s1413, days {DAYS}; AH {LA}, B2D {LB}, refit {LR})']
res = {}
# KW21-C0
k, p, r = WD.match(D / 'served' / 'FTX_served_s0.npz', D / 'rec' / 'FTX' / 'phases_s0.npz', ST); cc = {}
for kind in (0, 1):
    m = k == kind
    if m.any():
        best = max(WD.CS, key=lambda c: np.mean(np.abs(p[m] - (r[m] + c)) < 1e-6)); cc[kind] = (best, float(np.mean(np.abs(p[m] - (r[m] + best)) < 1e-6)), int(m.sum()))
    else:
        cc[kind] = (0, float('nan'), 0)
c0 = all(v[1] == 1.0 for v in cc.values() if v[2] > 0) and all(v[2] > 0 for v in cc.values())
out.append(f'KW21-C0 exactness under FT (program SPaT): ttg c {cc[0][0]:+d} exact {cc[0][1]:.4f} (n {cc[0][2]}), ttr c {cc[1][0]:+d} exact {cc[1][1]:.4f} '
           f'(n {cc[1][2]}) -> {"PASS" if c0 else "FAIL: forecast accounting VOID"}')
res['KW21_C0'] = dict(pass_=c0, c=cc)
# KW21-C1
if not SM:
    bad = []
    for kk in LA + LB:
        a, b = Rt[f'SHADOWg_t{kk}'], {x['seed']: x for x in json.loads((W21B / f'MTW_R_t{kk}_s1413.json').read_text())['rows']}
        bad += [(kk, s, f) for s in b for f in FIELDS if a[s][f] != b[s][f]]
    out.append(f'KW21-C1 SHADOWg = W21-B R rows ({len(LA + LB)} lights x {len(DAYS)} days): ' + ('PASS' if not bad else f'FAIL {bad[:6]}'))
    res['KW21_C1'] = not bad


def acct(tag, ks):
    E, K = [], []; held = cmd = 0; tla = []
    for kk in ks:
        t = f'{tag}_t{kk}'
        for s in DAYS:
            kind, pr, re = WD.match(D / 'served' / f'{t}_served_s{s}.npz', D / 'rec' / t / f'phases_s{s}.npz', ST)
            c = np.where(kind == 0, cc[0][0], cc[1][0]); E.append(pr - (re + c)); K.append(kind)
            row = Rt[t][s]; held += row.get('held_human_s', 0); cmd += row.get('commanded_agent_s', 0); tla.append(row['timeloss_agent'])
    e, kd = np.concatenate(E), np.concatenate(K)
    return dict(n=int(len(e)), mae=float(np.mean(np.abs(e))), bias=float(np.mean(e)), gt5=float(np.mean(np.abs(e) > 5)), mae_ttg=float(np.mean(np.abs(e[kd == 0]))),
                mae_ttr=float(np.mean(np.abs(e[kd == 1]))), held_per_cmd=held / max(1, cmd), tl_agent=float(np.mean(tla)))


def boot(M, rng):
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]))].mean() for _ in range(2000)]
    return float(M.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def diff(a, b, ks, m, pct=False):
    M = np.array([[100 * (Rt[f'{a}_t{kk}'][s][m] / Rt[f'{b}_t{kk}'][s][m] - 1) if pct else Rt[f'{a}_t{kk}'][s][m] - Rt[f'{b}_t{kk}'][s][m] for s in DAYS] for kk in ks])
    return boot(M, np.random.default_rng(0))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
out.append('-- C1 / C2: served-answer accounting (error = answer - realized; MAE s) and following exposure (held human-s per commanded agent-s)')
for lab, tag, ks in (('AH, grid forecaster', 'g', LA), ('B2D, grid forecaster', 'g', LB), ('B2D t60-63, grid forecaster', 'g', LR), ('B2D t60-63, refit forecaster', 'r', LR)):
    sv, sh = acct(f'SERVE{tag}', ks), acct(f'SHADOW{tag}', ks)
    dt = diff(f'SERVE{tag}', f'SHADOW{tag}', ks, 'timeloss_agent'); df = diff(f'SERVE{tag}', f'SHADOW{tag}', ks, 'fuel_agent', True)
    res[lab] = dict(serve=sv, shadow=sh, agent_tl_serve_minus_shadow=dt, fuel_serve_minus_shadow=df)
    out += [f'  {lab}: shadow MAE {sh["mae"]:.2f} (ttg {sh["mae_ttg"]:.2f}, ttr {sh["mae_ttr"]:.2f}), bias {sh["bias"]:+.2f}, >5 s {sh["gt5"]:.3f}, n {sh["n"]} | '
            f'served MAE {sv["mae"]:.2f} (ttg {sv["mae_ttg"]:.2f}, ttr {sv["mae_ttr"]:.2f}), bias {sv["bias"]:+.2f}, >5 s {sv["gt5"]:.3f}, n {sv["n"]} | '
            f'publication shift {sv["mae"] - sh["mae"]:+.2f} s',
            f'      held per commanded agent-s: served {sv["held_per_cmd"]:.3f}, shadow {sh["held_per_cmd"]:.3f} | agent TL serve - shadow {fmt(dt)} s/veh; agent fuel {fmt(df)} %']
out.append('  W10 references (grid / spider / rand3): shadow MAE 3.77 / 7.33 / 15.34 s; publication shift +0.14 / +7.80 / -2.60 s; held 0.057 / 0.286 / 0.050')
# C3
kh = (D / 'kh1.txt').read_text().strip() if (D / 'kh1.txt').exists() else 'kh1.txt missing'
out += ['-- C3: oracle on the fixed schedule (R\'s own, replayed)', '  ' + kh]
if all(f'ORC_t{kk}' in Rt and f'SIG_t{kk}' in Rt for kk in LA + LB):
    same = sum(all(Rt[f'SIG_t{kk}'][s][f] == Rt[f'SHADOWg_t{kk}'][s][f] for f in ('timeloss', 'timeloss_agent', 'fuel_agent')) for kk in LA + LB for s in DAYS)
    out.append(f'  KH-1 for every light-day: SIG reproduces SHADOWg on {same} of {len(LA + LB) * len(DAYS)}')
    for lab, ks in (('AH', LA), ('B2D', LB)):
        r3 = {m: diff('ORC', 'SIG', ks, m, m == 'fuel_agent') for m in ('timeloss_agent', 'fuel_agent', 'timeloss_human')}
        res[f'C3 {lab}'] = r3
        out.append(f'  {lab}: ORC - SIG agent TL {fmt(r3["timeloss_agent"])} s/veh, agent fuel {fmt(r3["fuel_agent"])} %, human TL {fmt(r3["timeloss_human"])}')
else:
    out.append('  C3 not run or incomplete')
sfx = '_smoke' if SM else ''
(D / f'report_w21c{sfx}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21c{sfx}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
