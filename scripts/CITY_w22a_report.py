#!/usr/bin/env python3
"""W22-A report (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-A): deciding exposure by size from the owner's switchback, and its cost.
<dir>: SWBp<pp>_t<k>_s<f> rows (probe on).  Ground truth R / SV rows of the same light, fleet and day (W19 for AH, W20 otherwise).
  unit = (policy k, fleet); tau_d = mean over signals of treated - control mean green (greens >= burn-in into a window) on day d
  after n = 2..N days: Student-t 95 % interval of mean tau_d -> exposed if lower > DELTA, not exposed if upper < DELTA, else continue;
  also a normal-mixture confidence sequence with plug-in sd (descriptive, approximate):  half-width sd * sqrt((n+1) log((n+1)/alpha^2)) / n
  truth label: SV - R mean green over the unit's days > DELTA.  Cost: fleet fuel and agent time loss of SWB against SV, same light/fleet/day,
  and the share of SPaT's fuel benefit kept, (fuel_SWB - fuel_R) / (fuel_SV - fuel_R).
Usage: CITY_w22a_report.py <dir> "<FAM:k0-k1:src ...>" "<fleets>" "<days>" "<p levels, e.g. 50 80 95>" """
import json, math, os, sys
from pathlib import Path
import numpy as np
D = Path(sys.argv[1]); FAMS = [x.split(':') for x in sys.argv[2].split()]; FS = [int(x) for x in sys.argv[3].split()]; DAYS = [int(x) for x in sys.argv[4].split()]
PL = [int(x) for x in sys.argv[5].split()]; SM = os.environ.get('W22_SMOKE') == '1'; SFX = '_smoke' if SM else ''
SRC = {'w19': Path('research/city_sim/w19_20261008/conf'), 'w20': Path('research/city_sim/w20_20261009/conf')}
DELTA, ALPHA = 0.5, 0.05
T975 = [None, 12.706, 4.303, 3.182, 2.776, 2.571, 2.447, 2.365, 2.306, 2.262, 2.228, 2.201, 2.179, 2.160, 2.145, 2.131, 2.120, 2.110, 2.101, 2.093]


def L(p):
    d = json.loads(Path(p).read_text())
    if d.get('status') != 'COMPLETE':
        sys.exit(f'INCOMPLETE {p}')
    return {r['seed']: r for r in d['rows']}


def run_tau(win):
    acc = {}
    for tid, w, _na, _da, nl, dl, _t, _c, a in win:
        s = acc.setdefault(tid, [0, 0.0, 0, 0.0]); s[2 * a] += nl; s[2 * a + 1] += dl
    t = [s[3] / s[2] - s[1] / s[0] for s in acc.values() if s[0] > 0 and s[2] > 0]
    return float(np.mean(t)) if t else float('nan')


def decide(x, kind):
    for n in range(2, len(x) + 1):
        m, sd = float(np.mean(x[:n])), float(np.std(x[:n], ddof=1))
        h = T975[n - 1] * sd / math.sqrt(n) if kind == 't' else sd * math.sqrt((n + 1) * math.log((n + 1) / ALPHA ** 2)) / n
        if m - h > DELTA:
            return 'exposed', n
        if m + h < DELTA:
            return 'not exposed', n
    return 'undecided', None


out = [f'== W22-A: exposure decided by size (delta {DELTA} s) from the owner switchback; p levels {PL}; fleets {FS}; days {DAYS}']; res = {}
for fam, kr, src in FAMS:
    k0, k1 = (int(x) for x in kr.split('-')); ks = list(range(k0, k1 + 1)); G = SRC[src] if src in SRC else Path(src)
    R = {(k, s): L(G / f'R_t{k}_s{s}.json') for k in ks for s in FS}; V = {(k, s): L(G / f'SV_t{k}_s{s}.json') for k in ks for s in FS}
    out.append(f'-- {fam} (t{k0}-t{k1})'); res[fam] = {}
    for p in PL:
        units = []; cost_f = []; cost_t = []; kept = []
        for k in ks:
            for s in FS:
                S = L(D / f'SWBp{p}_t{k}_s{s}.json'); tau = [run_tau(S[d]['w22_win']['rows']) for d in DAYS]
                truth = float(np.mean([V[k, s][d]['green_mean'] - R[k, s][d]['green_mean'] for d in DAYS])); lab_t = 'exposed' if truth > DELTA else 'not exposed'
                dt, nt = decide(tau, 't'); dc, nc = decide(tau, 'cs')
                units.append(dict(k=k, s=s, tau=float(np.mean(tau)), truth=truth, truth_label=lab_t, t=[dt, nt], cs=[dc, nc]))
                for d in DAYS:
                    sv, r, x = V[k, s][d], R[k, s][d], S[d]
                    cost_f.append(100 * (x['fuel_agent'] / sv['fuel_agent'] - 1)); cost_t.append(x['timeloss_agent'] - sv['timeloss_agent'])
                    den = sv['fuel_agent'] - r['fuel_agent']; kept.append((x['fuel_agent'] - r['fuel_agent']) / den if abs(den) > 1e-9 else float('nan'))
        e = {}
        for kind in ('t', 'cs'):
            lab = [u[kind][0] for u in units]; ns = [u[kind][1] for u in units if u[kind][1]]
            wrong = sum(u[kind][0] not in ('undecided', u['truth_label']) for u in units)
            e[kind] = dict(exposed=lab.count('exposed'), not_exposed=lab.count('not exposed'), undecided=lab.count('undecided'), wrong=wrong,
                           median_days=float(np.median(ns)) if ns else None, max_days=max(ns) if ns else None)
        e.update(units=units, tau=float(np.mean([u['tau'] for u in units])), truth=float(np.mean([u['truth'] for u in units])),
                 fuel_cost_pct=float(np.mean(cost_f)), tl_cost=float(np.mean(cost_t)), benefit_kept=float(np.nanmean(kept)))
        res[fam][p] = e; tl = e['t']; cs = e['cs']
        out.append(f'  p {p / 100:.2f} (forgo {1 - p / 100:.2f}): tau {e["tau"]:+.2f} s (truth {e["truth"]:+.2f}); t-rule: exposed {tl["exposed"]}, not {tl["not_exposed"]}, '
                   f'undecided {tl["undecided"]}, WRONG {tl["wrong"]}, days median {tl["median_days"]} max {tl["max_days"]} | CS: exposed {cs["exposed"]}, '
                   f'not {cs["not_exposed"]}, undecided {cs["undecided"]}, wrong {cs["wrong"]}, days median {cs["median_days"]} | cost vs SV: fuel '
                   f'{e["fuel_cost_pct"]:+.2f} %, agent TL {e["tl_cost"]:+.2f} s/veh, fuel benefit kept {e["benefit_kept"]:.2f}')
if SM:
    out.append('(smoke: truncated runs against full-length ground truth; numbers meaningless, pipeline check only)')
(D / f'report_w22a{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w22a{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
