#!/usr/bin/env python3
"""W21-G / W21-H report (PROTOCOL_CITY_WAVE21_20261015).  <dir> holds the W21-G replay rows (SIGR / ORCR on R's schedule, SIGS / ORCS on the
forecast run's schedule) and the W21-H capped rows (LGc / Rc / SVc); <W21-C dir> holds SHADOWg (= R) and SERVEg (= SV) for the same fleet
(s1413) and days.  Descriptive, 95 % bootstrap over lights x days (2 000 draws, seed 0).
  KH-1    SIGR reproduces SHADOWg on every light-day (time losses, fuel, counts, action digest)
  R5      ORCR - SIGR: exact timing on R's own schedule
  decomp  SV - R = (SIGS - SIGR) schedule effect + (SV - SIGS) information effect; ORCS - SIGS alongside
  H       SVc - Rc (capped at 20 s, cap-aware provider) against SV - R (uncapped); Rc - R and LGc - ACT (W21-B's MTW_ACT) = what the cap costs
Usage: CITY_w21gh_report.py <dir> <W21-C dir> "<lights>" "<days>" """
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_w6_validation import rows  # noqa: E402
D, C = Path(sys.argv[1]), Path(sys.argv[2]); LT = [int(x) for x in sys.argv[3].split()]; DAYS = [int(x) for x in sys.argv[4].split()]
SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
R = rows(D); R.update({k: v for k, v in rows(C).items() if k.startswith(('SHADOWg_', 'SERVEg_t'))})
ACT = {r['seed']: r for r in json.loads((ROOT / 'research/city_sim/w21_20261015/midtown/MTW_ACT.json').read_text())['rows']}
FAM = {'AH': [k for k in LT if k < 50], 'B2D': [k for k in LT if k >= 59]}; F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports', 'unfinished', 'action_digest')
rng = np.random.default_rng(0); out = [f'== W21-G / W21-H: Midtown, fleet s1413, days {DAYS}, lights {LT}']; res = {}


def has(tag, ks):
    return all(f'{tag}_t{k}' in R and all(d in R[f'{tag}_t{k}'] for d in DAYS) for k in ks)


def diff(a, b, ks, m, pct=False):
    M = np.array([[100 * (R[f'{a}_t{k}'][d][m] / R[f'{b}_t{k}'][d][m] - 1) if pct else R[f'{a}_t{k}'][d][m] - R[f'{b}_t{k}'][d][m] for d in DAYS] for k in ks])
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]))].mean() for _ in range(2000)]
    return float(M.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731


def block(a, b, ks):
    r = {m: diff(a, b, ks, m, m == 'fuel_agent') for m in ('timeloss_agent', 'fuel_agent', 'timeloss_human')}
    return r, f'agent TL {fmt(r["timeloss_agent"])} s/veh, agent fuel {fmt(r["fuel_agent"])} %, human TL {fmt(r["timeloss_human"])}'


# KH-1
if has('SIGR', LT):
    same = sum(all(R[f'SIGR_t{k}'][d][f] == R[f'SHADOWg_t{k}'][d][f] for f in F) for k in LT for d in DAYS)
    out.append(f'KH-1: SIGR reproduces SHADOWg (R) on {same} of {len(LT) * len(DAYS)} light-days'); res['KH1'] = [same, len(LT) * len(DAYS)]
else:
    out.append('KH-1: ' + ((D / 'kh1.txt').read_text().strip() if (D / 'kh1.txt').exists() else 'not run'))
for f, ks in FAM.items():
    if not ks:
        continue
    out.append(f'-- {f} (lights {ks})'); e = {}
    r, s = block('SERVEg', 'SHADOWg', ks); e['SV_R'] = r; out.append(f'  SV - R (closed loop, W21-C): {s}')
    if has('ORCR', ks) and has('SIGR', ks):
        r, s = block('ORCR', 'SIGR', ks); e['R5'] = r; out.append(f'  R5  ORC - SIG on R\'s schedule (exact timing): {s}')
    if has('SIGS', ks) and has('ORCS', ks):
        r1, s1 = block('SIGS', 'SHADOWg', ks); r2, s2 = block('SERVEg', 'SIGS', ks); r3, s3 = block('ORCS', 'SIGS', ks)
        e.update(schedule=r1, information=r2, ORCS_SIGS=r3)
        out += [f'  schedule effect (SIG on SV\'s schedule - R): {s1}', f'  information effect (SV - SIG on its own schedule): {s2}',
                f'  ORC - SIG on SV\'s schedule (exact timing): {s3}']
    if has('SVc', ks) and has('Rc', ks):
        r, s = block('SVc', 'Rc', ks); e['H'] = r; out.append(f'  H   SVc - Rc (greens capped at 20 s, cap-aware provider): {s}')
        r, s = block('Rc', 'SHADOWg', ks); e['cap_cost_R'] = r; out.append(f'      Rc - R (what the cap costs, fleet without SPaT): {s}')
        g = {a: float(np.mean([R[f'{a}_t{k}'][d]['green_mean'] for k in ks for d in DAYS])) for a in ('SHADOWg', 'SERVEg', 'Rc', 'SVc')}
        e['greens'] = g; out.append('      mean green: ' + ', '.join(f'{a} {v:.1f} s' for a, v in g.items()))
        if has('LGc', ks):
            M = np.array([[R[f'LGc_t{k}'][d]['timeloss'] - ACT[d]['timeloss'] for d in DAYS] for k in ks]); out.append(f'      LGc - ACT city TL (all human): {M.mean():+.2f} s/veh')
        tv, hv = e['SV_R']['timeloss_agent'][0], e['H']['timeloss_agent'][0]
        out.append(f'      reading: capped cost {hv:+.2f} vs uncapped {tv:+.2f} s/veh -> '
                   + ('LONG GREENS drive the cost (capped < half of uncapped)' if hv < 0.5 * tv else 'not explained by green length (capped >= half of uncapped)'))
    if 'R5' in e:
        lo, hi = e['R5']['timeloss_agent'][1], e['R5']['timeloss_agent'][2]
        out.append('      R5 reading: ' + ('exact timing still costs (or does not save) the fleet time on this map -> the cost lies in the glide on this network, not in the forecast information'
                                        if lo > 0 or (lo <= 0 <= hi and e['R5']['timeloss_agent'][0] >= 0) else
                                        ('exact timing saves the fleet time -> the cost lies in the forecast information' if hi < 0 else 'inconclusive')))
    res[f] = e
(D / f'report_w21gh{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21gh{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
