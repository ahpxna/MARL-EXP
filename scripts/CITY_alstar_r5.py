#!/usr/bin/env python3
"""A-L* with F* = R5h (PROTOCOL_CITY_B6 §B6-R5-P, registered 04/10/2026 wake 9 BEFORE the B6-R5 verdict; runs only if 050r CONFIRMED).
Benefit = FUEL (B6-1).  Fleet seeds = the four replication seeds t2..t5.  Lights ACT and RL-H_0..3 (frozen).  Comparators under the SAME
light: always-SUMO (σ 0.5) and the σ-family σ 0..0.4 (CITY_eval4_sigma.py).
  plan_sel   CITY_eval5 lines, SELECT 100-104: F* x {none, fallback, clip, green+oos} (support from L-ACT:0) + always-SUMO per light
  plan_sig   CITY_eval4_sigma lines for a seed list (argv[2:]) under every light: σ 0, 0.1, 0.2, 0.3, 0.4
  select     choose the guard with the lowest point agent-FUEL % vs always-SUMO under RL-H on SELECT -> 051v/CHOSEN.txt; report AP-1 on SELECT
  plan_val   CITY_eval5 lines, VALIDATION 200-209 under RL-H_0..3: F* x {chosen, none} + always-SUMO
  judge      on VALIDATION:
     AP-1  regression: agent fuel % (F* vs always-SUMO | RL-H) - (the same | ACT, SELECT-free: VALIDATION has no ACT run, so AP-1 is read on SELECT)
     AP-2  benefit kept under RL-H (chosen guard): agent fuel superiority (upper < 0) and agent TL NI (upper < +0.5) vs always-SUMO, same light
     AP-3  human-vehicle TL NI (upper < +0.5)
     AP-4  S-2 under RL-H: beyond the σ-family under the same light (pooled light-seed x fleet-seed x traffic)
Crossed bootstrap light-seed x fleet-seed x traffic (2000 draws, rng 0); σ arms have no fleet seed (shared across F* seeds)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

W = R.W; FT = [2, 3, 4, 5]; LI = [0, 1, 2, 3]; VAL = list(range(200, 210)); GUARDS = ('none', 'fallback', 'clip', 'green+oos'); SIG = ('0.0', '0.1', '0.2', '0.3', '0.4')
tag = lambda t, L, g: f'R5h_t{t}_{L}_{g}'.replace(':', '-').replace('+', 'P')


def rows(d):
    Rt = {}
    for f in Path(d).glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    return Rt


def plan_sel():
    s = ' '.join(map(str, R.SEL))
    for L in ['ACT'] + [f'RL-H:{i}' for i in LI]:
        for t in FT:
            for g in GUARDS:
                print(f'--light {L} --fleet U:L-ACT-R5h_t{t} --guard {g} --support-from L-ACT:0 --seeds {s} --tag {tag(t, L, g)}')
        print(f"--light {L} --fleet L-ACT:0 --guard always --seeds {s} --tag OFF_{L.replace(':', '-')}")


def plan_sig():
    s = ' '.join(sys.argv[2:])
    for L in ['ACT'] + [f'RL-H:{i}' for i in LI]:
        for sg in SIG:
            print(f"{sg} {L} S{sg}_{L.replace(':', '-')} {s}")


def cube(A, B, fl, seeds, k, pct=False):
    """A: F* rows, B: comparator rows (no fleet seed); fl(i) -> light tag; returns [light, fleet, traffic]."""
    f = (lambda a, b: 100 * (a / b - 1)) if pct else (lambda a, b: a - b)
    return np.array([[[f(A[(tag(t, fl(i)[0], fl(i)[2]), s)][k], B[(fl(i)[1], s)][k]) for s in seeds] for t in FT] for i in LI])


def select():
    A = rows(W / '051s'); out = ['== A-L* (F* = R5h, benefit = fuel) SELECT 100-104']; dr = R.draws((4, 4, 5)); best = None
    for g in GUARDS:
        fl = lambda i: (f'RL-H:{i}', f'OFF_RL-H-{i}', g)
        F_ = R.crossed(cube(A, A, fl, R.SEL, 'fuel_agent', True), dr); T_ = R.crossed(cube(A, A, fl, R.SEL, 'timeloss_agent'), dr)
        out.append(f'  guard {g} under RL-H vs always-SUMO: agent fuel % {R.fmt(*F_)}; agent TL {R.fmt(*T_)}')
        if best is None or F_[0] < best[1]:
            best = (g, F_[0])
    ap1 = np.array([[[(100 * (A[(tag(t, f'RL-H:{i}', 'none'), s)]['fuel_agent'] / A[(f'OFF_RL-H-{i}', s)]['fuel_agent'] - 1))
                      - (100 * (A[(tag(t, 'ACT', 'none'), s)]['fuel_agent'] / A[('OFF_ACT', s)]['fuel_agent'] - 1)) for s in R.SEL] for t in FT] for i in LI])
    p, ci, up = R.crossed(ap1, dr)
    out.append(f'AP-1 regression of the fuel benefit, plain F*, RL-H vs ACT (SELECT): {R.fmt(p, ci, up)} -> {"SUPPORTED (benefit shrinks)" if ci[0] > 0 else "NOT SUPPORTED (no detected regression)"}')
    (W / '051v').mkdir(parents=True, exist_ok=True); (W / '051v' / 'CHOSEN.txt').write_text(f'guard={best[0]}\n')
    out.append(f'chosen guard (lowest point agent fuel % under RL-H, SELECT): {best[0]}')
    (W / 'report_alstar_r5_select.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


def plan_val():
    g = (W / '051v' / 'CHOSEN.txt').read_text().split('=')[1].strip(); s = ' '.join(map(str, VAL))
    for i in LI:
        for t in FT:
            for gd in sorted({g, 'none'}):
                print(f'--light RL-H:{i} --fleet U:L-ACT-R5h_t{t} --guard {gd} --support-from L-ACT:0 --seeds {s} --tag {tag(t, f"RL-H:{i}", gd)}')
        print(f'--light RL-H:{i} --fleet L-ACT:0 --guard always --seeds {s} --tag OFF_RL-H-{i}')


def judge():
    g = (W / '051v' / 'CHOSEN.txt').read_text().split('=')[1].strip(); A = rows(W / '051v'); dr = R.draws((4, 4, 10))
    out = [f'== A-L* VALIDATION 200-209 (F* = R5h t2..t5, chosen guard {g}); comparators under the same RL-H light']
    for gd in sorted({g, 'none'}):
        fl = lambda i: (f'RL-H:{i}', f'OFF_RL-H-{i}', gd)
        F_ = R.crossed(cube(A, A, fl, VAL, 'fuel_agent', True), dr); T_ = R.crossed(cube(A, A, fl, VAL, 'timeloss_agent'), dr)
        H_ = R.crossed(cube(A, A, fl, VAL, 'timeloss_human'), dr); C_ = R.crossed(cube(A, A, fl, VAL, 'timeloss'), dr)
        lab = 'AP-2/3' if gd == g else '(plain)'
        v2 = F_[2] < 0 and T_[2] < 0.5; v3 = H_[2] < 0.5
        out.append(f'{lab} guard {gd}: agent fuel % {R.fmt(*F_)}; agent TL {R.fmt(*T_)}; human TL {R.fmt(*H_)}; city TL {R.fmt(*C_)}'
                   + (f' -> AP-2 {"SUPPORTED" if v2 else "NOT SUPPORTED"}; AP-3 {"SUPPORTED" if v3 else "NOT SUPPORTED"}' if gd == g else ''))
        if gd == g:
            ok4 = True; parts = []
            for sg in SIG + ('0.5',):
                fl2 = (lambda i, sg=sg: (f'RL-H:{i}', f'OFF_RL-H-{i}' if sg == '0.5' else f'S{sg}_RL-H-{i}', gd))
                a = R.crossed(cube(A, A, fl2, VAL, 'fuel_agent', True), dr); c = R.crossed(cube(A, A, fl2, VAL, 'timeloss_agent'), dr)
                b = a[2] < 0 or c[2] < 0; ok4 &= b; parts.append(f'σ{sg}: fuel {a[0]:+.2f}% TL {c[0]:+.2f} {"better" if b else "NOT better"}')
            out.append('AP-4 S-2 under RL-H: ' + '; '.join(parts) + f' -> {"SUPPORTED" if ok4 else "NOT SUPPORTED"}')
    (W / 'report_alstar_r5_validation.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    {'plan_sel': plan_sel, 'plan_sig': plan_sig, 'select': select, 'plan_val': plan_val, 'judge': judge}[sys.argv[1]]()
