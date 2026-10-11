#!/usr/bin/env python3
"""M3 DEV report and mechanical selection (PROTOCOL_CITY_M3_COMPAT_UPDATE_20261004 §6 + A1; written before any DEV evaluation).
Dir research/city_sim/m3_20261004/dev.  Cube [light seed k in {0,1}, dev fleet in {s13, s113}, traffic 15] vs the reference R = RL-H:k + no SPaT
with the same fleet; crossed bootstrap over the three axes (2000 draws).
  M3-1 agent fuel % vs R (primary);  M3-2 city / agent / human TL upper < +0.5, teleports mean <= R + 0.1, unfinished <= R
  M3-3 fleet contribution (arm, fleet) vs (arm, σ* cars);  M3-4 light-side cost (arm, σ*) vs (RL-H:k, σ*): city TL, city fuel
  M3-5 message quality from the sidecars (query MAE, bias, commitment violations, commanded vehicle-seconds)
Selection: per family, among settings feasible under M3-2, the best M3-1 point; if none feasible, the best M3-1 marked INFEASIBLE.
Families: E-receiver, E-uniform, E-ETA, E-active (lam), E0p, E0q (reported, not in the gate); comparators F-q (q), D, W-c (W), B-ETA (W_B),
P-cyc (G) -> the best comparator = the best selected comparator (feasible first).  Writes dev/selection.json and report_m3_dev.txt.
DEV comparisons of E-receiver vs the others are DESCRIPTIVE (the gate is decided on the confirmation panel only)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/m3_20261004/dev'; S = [100, 101, 102, 103, 104] + list(range(200, 210))
KS, FLS = (0, 1), ('s13', 's113')
FAM = {'E-receiver': [f'E_receiver_lam{l}' for l in (1, 4)], 'E-uniform': [f'E_uniform_lam{l}' for l in (1, 4)], 'E-ETA': [f'E_eta_lam{l}' for l in (1, 4)],
       'E-active': [f'E_active_lam{l}' for l in (1, 4)], 'E0p': ['E_E0p_lam0'], 'E0q': ['E_E0q_lam0'],
       'F-q': [f'Fq{q}' for q in ('0.1', '0.2', '0.3', '0.5')], 'D': ['D'], 'W-c': [f'WC{w}' for w in (5, 10, 15)], 'B-ETA': [f'B{w}' for w in (10, 15)],
       'P-cyc': [f'CYC{g}' for g in (10, 15, 20, 25, 30)]}
COMP = ('F-q', 'D', 'W-c', 'B-ETA', 'P-cyc')


def tag(k, fl, arm):
    return f'{arm}_k{k}_{fl}' if not arm.startswith('CYC') else f'{arm}_{fl}'


def get(Rt, k, fl, arm):
    t = tag(k, fl, arm)
    if t not in Rt:
        raise SystemExit(f'MISSING rows {t}')
    r = Rt[t]
    if sorted(r) != S:
        raise SystemExit(f'INCOMPLETE seeds in {t}: {sorted(r)}')
    return r


def cube(Rt, arm, ref, key, pct, fl_arm=None):
    out = np.zeros((len(KS), len(FLS), len(S)))
    for i, k in enumerate(KS):
        for j, fl in enumerate(FLS):
            a = get(Rt, k, fl_arm or fl, arm); b = get(Rt, k, fl if ref != 'R_sig' else 'sig', 'R' if ref in ('R', 'R_sig') else ref)
            out[i, j] = [100 * (a[s][key] / b[s][key] - 1) if pct else a[s][key] - b[s][key] for s in S]
    return out


def summ(c, dr):
    v = np.array([c[np.ix_(*ix)].mean() for ix in dr]); return dict(p=float(c.mean()), lo=float(np.percentile(v, 2.5)), hi=float(np.percentile(v, 97.5)),
                                                                     up=float(np.percentile(v, 95)), low1=float(np.percentile(v, 5)))


def feasible(Rt, arm, dr):
    tl = {k: summ(cube(Rt, arm, 'R', k, False), dr) for k in ('timeloss', 'timeloss_agent', 'timeloss_human')}
    tel = np.mean([get(Rt, k, fl, arm)[s]['teleports'] for k in KS for fl in FLS for s in S]); tel0 = np.mean([get(Rt, k, fl, 'R')[s]['teleports'] for k in KS for fl in FLS for s in S])
    unf = sum(get(Rt, k, fl, arm)[s]['unfinished'] for k in KS for fl in FLS for s in S); unf0 = sum(get(Rt, k, fl, 'R')[s]['unfinished'] for k in KS for fl in FLS for s in S)
    ok = all(tl[k]['up'] < 0.5 for k in tl) and tel <= tel0 + 0.1 and unf <= unf0
    return ok, tl, tel, tel0


def select(score):
    """score: {setting: (feasible, M3-1 point)} -> (setting, feasible).  Feasible first, then the lowest fuel point."""
    fe = {s: v for s, v in score.items() if v[0]}
    pool = fe if fe else score; best = min(pool, key=lambda s: pool[s][1]); return best, bool(fe)


def main():
    Rt = rows(D); dr = R.draws((len(KS), len(FLS), len(S))); out = ['== M3 DEV screen (SELECT 100-104 + 200-209; light seeds 0, 1 x dev fleets s13, s113)']; sel = {}
    for fam, arms in FAM.items():
        score = {}
        for arm in arms:
            f1 = summ(cube(Rt, arm, 'R', 'fuel_agent', True), dr); ok, tl, tel, tel0 = feasible(Rt, arm, dr); score[arm] = (ok, f1['p'])
            line = (f"  {fam:10s} {arm:16s} M3-1 fuel % {f1['p']:+.2f} [{f1['lo']:+.2f}, {f1['hi']:+.2f}] (up {f1['up']:+.2f}) | city TL {tl['timeloss']['p']:+.2f} (up {tl['timeloss']['up']:+.2f}) "
                    f"agent {tl['timeloss_agent']['p']:+.2f} (up {tl['timeloss_agent']['up']:+.2f}) human {tl['timeloss_human']['p']:+.2f} (up {tl['timeloss_human']['up']:+.2f}) "
                    f"tele {tel:.2f} ({tel0:.2f}) -> {'FEASIBLE' if ok else 'infeasible'}")
            sig = 'R' if fam in ('F-q', 'D', 'B-ETA') else arm
            try:
                c3 = summ(_contrib(Rt, arm, sig), dr)
                line += f" | M3-3 fleet contrib fuel % {c3['p']:+.2f}" + (' (JOINT, B)' if fam == 'B-ETA' else '')
            except SystemExit:
                line += ' | M3-3 n/a'
            if fam not in ('F-q', 'D', 'B-ETA'):
                try:
                    c4 = summ(_lightcost(Rt, arm, 'timeloss', False), dr); c4f = summ(_lightcost(Rt, arm, 'fuel', True), dr)
                    line += f" | M3-4 light cost city TL {c4['p']:+.2f} (up {c4['up']:+.2f}), city fuel % {c4f['p']:+.2f}"
                except SystemExit:
                    line += ' | M3-4 n/a'
            line += _msg(arm); out.append(line)
        best, feas = select(score); sel[fam] = dict(setting=best, feasible=feas, fuel_point=score[best][1]); out.append(f'  -> {fam} selected: {best} ({"feasible" if feas else "INFEASIBLE"})')
    comp = {f: sel[f] for f in COMP}; fe = {f: v for f, v in comp.items() if v['feasible']}; pool = fe if fe else comp
    bf = min(pool, key=lambda f: pool[f]['fuel_point']); sel['best_comparator'] = dict(family=bf, **comp[bf])
    out.append(f"  BEST COMPARATOR (frozen for confirmation): {bf} / {comp[bf]['setting']} ({'feasible' if comp[bf]['feasible'] else 'INFEASIBLE'})")
    (D / 'selection.json').write_text(json.dumps(sel, indent=1)); t = '\n'.join(out) + '\n'; (D.parent / 'report_m3_dev.txt').write_text(t); print(t)


def _contrib(Rt, arm, sig_arm):
    c = np.zeros((len(KS), len(FLS), len(S)))
    for i, k in enumerate(KS):
        for j, fl in enumerate(FLS):
            a = get(Rt, k, fl, arm); b = get(Rt, k, 'sig', sig_arm); c[i, j] = [100 * (a[s]['fuel_agent'] / b[s]['fuel_agent'] - 1) for s in S]
    return c


def _lightcost(Rt, arm, key, pct):
    c = np.zeros((len(KS), len(FLS), len(S)))
    for i, k in enumerate(KS):
        a = get(Rt, k, 'sig', arm); b = get(Rt, k, 'sig', 'R')
        for j in range(len(FLS)):
            c[i, j] = [100 * (a[s][key] / b[s][key] - 1) if pct else a[s][key] - b[s][key] for s in S]
    return c


def _msg(arm):
    m = []
    for k in KS:
        for fl in FLS:
            f = D / f'{tag(k, fl, arm)}_m3.json'
            if f.exists():
                ps = json.loads(f.read_text())['per_seed'].values(); m += list(ps)
    if not m:
        return ''
    mae = [x['mae'] for x in m if x.get('mae') is not None]; vio = sum(x.get('violations', 0) for x in m); com = sum(x.get('commits', 0) for x in m)
    cmd = sum(x.get('commanded', 0) for x in m)
    return f" | M3-5 query MAE {np.mean(mae):.1f}s, commits {com}, violations {vio}, commanded {cmd}" if mae else f" | M3-5 commits {com}, violations {vio}, commanded {cmd}"


if __name__ == '__main__':
    main()
