#!/usr/bin/env python3
"""S-2 re-classification from EXISTING rows (04/10/2026, report written 12:02; correction requested by the user's audit CITY_B6_FINAL_AND_SPAT_AUDIT §2B).
The registered S-2 reporter (CITY_b6sh_report.py, frozen) printed 'within (dominated by some σ)' whenever the fleet was not shown better
than some σ.  Not shown better is NOT shown dominated.  This script keeps the registered S-2 verdict ('beyond' iff, for every σ,
TL upper < 0 OR fuel upper < 0) and adds two DESCRIPTIVE, unadjusted labels per (fleet, σ):
  'σ dominates F'   F - σ is worse on BOTH axes with one-sided 95 % LOWER bounds > 0 (TL and fuel %);
  'not separated'   neither the registered 'F better' nor 'σ dominates F'.
Fleet label: BEYOND (registered S-2) | DOMINATED by σ_k (some σ dominates) | NOT ESTABLISHED (neither).  No new simulation; the
bootstrap is the wave-2 helper (traffic or fleet-seed x traffic, 2000 draws, rng 0).  Multiplicity: per-σ tests are unadjusted, the
OR inside 'F better' is not a 5 % test; these labels are descriptive only."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
import scripts.CITY_b6sh_report as S  # noqa: E402

W = R.W


def boot(D, dr):
    v = np.array([D[np.ix_(*ix)].mean() for ix in dr]); return float(D.mean()), float(np.percentile(v, 5)), float(np.percentile(v, 95))


def classify(name, cubeT, cubeF, out):
    """cubeT[σ], cubeF[σ]: arrays of F - σ (TL) and fuel % of F vs σ, same shape; returns the fleet label."""
    labs = []
    for sg in sorted(cubeT):
        dr = R.draws(cubeT[sg].shape); t = boot(cubeT[sg], dr); f = boot(cubeF[sg], dr)
        better = t[2] < 0 or f[2] < 0; dom = t[1] > 0 and f[1] > 0
        labs.append((sg, 'F better' if better else ('σ dominates F' if dom else 'not separated'), t[0], f[0]))
    lab = ('BEYOND (registered S-2)' if all(l[1] == 'F better' for l in labs) else
           'DOMINATED by ' + ','.join(f'σ{l[0]}' for l in labs if l[1] == 'σ dominates F') if any(l[1] == 'σ dominates F' for l in labs) else
           'NOT ESTABLISHED beyond the tested σ-family (not shown dominated)')
    out.append(f'  {name}: ' + '; '.join(f'σ{sg} {l} (dTL {t:+.2f}, dfuel {f:+.2f}%)' for sg, l, t, f in labs) + f'  => {lab}')
    return lab


def per_traffic(out, title, fleets_dir, panel):
    fam, _, seeds = S.family(panel); A = S.load(W / fleets_dir); out.append(f'== {title}')
    res = {}
    for name in sorted(k for k in A if k.startswith('U-')):
        if not all(s in A[name] for s in seeds):
            continue
        cT = {sg: np.array([A[name][s]['timeloss_agent'] - B[s]['timeloss_agent'] for s in seeds]) for sg, B in fam.items()}
        cF = {sg: np.array([100 * (A[name][s]['fuel_agent'] / B[s]['fuel_agent'] - 1) for s in seeds]) for sg, B in fam.items()}
        res[name] = classify(name, cT, cF, out)
    return res


def r5h_pooled(out):
    d = W / '050r'; Rt = S.load(d); ts = list(range(410, 420)); fam = {0.5: Rt['OFF_ACT'], **{float(s): Rt[f'S{s}_ACT'] for s in ('0.0', '0.1', '0.2', '0.3', '0.4')}}
    out.append('== R5h pooled over the 4 replication seeds t2..t5 (fleet-seed x traffic), 410-419')
    F = [Rt[f'U-L-ACT-R5h_t{t}_ACT'] for t in (2, 3, 4, 5)]
    cT = {sg: np.array([[f[s]['timeloss_agent'] - B[s]['timeloss_agent'] for s in ts] for f in F]) for sg, B in fam.items()}
    cF = {sg: np.array([[100 * (f[s]['fuel_agent'] / B[s]['fuel_agent'] - 1) for s in ts] for f in F]) for sg, B in fam.items()}
    lab = classify('R5h pooled t2..t5', cT, cF, out)
    for t in (0, 1, 2, 3, 4, 5):
        f = Rt[f'U-L-ACT-R5h_t{t}_ACT']
        classify(f'R5h_t{t}' + (' (development)' if t < 2 else ''), {sg: np.array([f[s]['timeloss_agent'] - B[s]['timeloss_agent'] for s in ts]) for sg, B in fam.items()},
                 {sg: np.array([100 * (f[s]['fuel_agent'] / B[s]['fuel_agent'] - 1) for s in ts]) for sg, B in fam.items()}, out)
    return lab


if __name__ == '__main__':
    out = ['# S-2 re-classification (descriptive correction; registered verdicts unchanged). Labels: see the module docstring.']
    per_traffic(out, 'B6-R v6 fleets, SELECT 100-104 (040c)', '040c', 'SEL')
    per_traffic(out, 'B6-T fleets, 400-409 (046)', '046', 'T')
    per_traffic(out, 'B6-H fleets, SELECT 100-104 (049h)', '049h', 'SEL')
    r5h_pooled(out)
    txt = '\n'.join(out) + '\n'; (W / 'report_s2_classify_v2.txt').write_text(txt); print(txt)
