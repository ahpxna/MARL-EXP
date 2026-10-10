#!/usr/bin/env python3
"""B6-S / B6-H report (PROTOCOL_CITY_B6 §B6-S, §B6-H; registered 09:13 04/10/2026, written before the runs).
  sections: sigma  S-1 the sigma-family vs always-SUMO (SELECT: 049s + 046z; 400-409: 049s/T + 046z/T + 046), self-check sigma 0.5 == always-SUMO;
                   S-2 'beyond the sigma-family' for the B6-T fleets (400-409, dir 046) and the B6-R v6 fleets (SELECT, dir 040c)
            horizon  H-1 B6-1 (fuel) and B6-T (time) per B6-H fleet (049h); H-2 trip - approach per reward and DQN seed; H-3 S-2 on 049h
Bootstrap: the wave-2 reporter's draws / crossed (traffic resampled, 2000 draws, rng 0); one-sided 95 % upper bounds."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

W = R.W; SIG = (0.1, 0.2, 0.3, 0.4); TS = list(range(400, 410))


def load(d):
    Rt = {}
    for f in Path(d).glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt.setdefault(f.stem, {})[r['seed']] = r
    return Rt


def diff(A, B, seeds):
    dr = R.draws((len(seeds),))
    T = R.crossed(np.array([A[s]['timeloss_agent'] - B[s]['timeloss_agent'] for s in seeds]), dr)
    F = R.crossed(np.array([100 * (A[s]['fuel_agent'] / B[s]['fuel_agent'] - 1) for s in seeds]), dr)
    H = R.crossed(np.array([A[s]['timeloss_human'] - B[s]['timeloss_human'] for s in seeds]), dr)
    return T, F, H


def family(panel):
    """sigma -> {seed: row} for one panel ('SEL' or 'T'); None if incomplete."""
    if panel == 'SEL':
        S, Z, O, seeds = load(W / '049s'), load(W / '046z'), load(W / '046z'), R.SEL
    else:
        S, Z, O, seeds = load(W / '049s' / 'T'), load(W / '046z' / 'T'), load(W / '046'), TS
    fam = {0.0: Z.get('Z-sig0_ACT'), 0.5: O.get('OFF_ACT')}
    fam.update({sg: S.get(f'S{sg}_ACT') for sg in SIG})
    ok = all(v is not None and all(s in v for s in seeds) for v in fam.values())
    return (fam, S.get('S0.5_ACT'), seeds) if ok else (None, None, seeds)


def beyond(out, name, A, fam, seeds):
    res = []
    for sg, B in sorted(fam.items()):
        T, F, _ = diff(A, B, seeds); res.append((sg, T[2] < 0 or F[2] < 0, T[0], F[0]))
    ok = all(r[1] for r in res)
    out.append(f'  S-2 {name}: ' + '; '.join(f'σ{sg}: dTL {t:+.2f} dfuel {f:+.2f}% {"better" if b else "NOT better"}' for sg, b, t, f in res)
               + f' -> {"BEYOND the σ-family" if ok else "within (dominated by some σ)"}')
    return ok


def sigma(out):
    for panel in ('SEL', 'T'):
        fam, chk, seeds = family(panel)
        if fam is None:
            out.append(f'B6-S {panel} INCOMPLETE'); continue
        same = chk is not None and all(abs(chk[s]['timeloss_agent'] - fam[0.5][s]['timeloss_agent']) < 1e-9 and abs(chk[s]['fuel_agent'] - fam[0.5][s]['fuel_agent']) < 1e-9 for s in seeds)
        out.append(f'== B6-S σ-family vs always-SUMO, ACT, {panel} {seeds[0]}-{seeds[-1]}; self-check σ 0.5 == always-SUMO: {"PASS" if same else "FAIL (report void)"}')
        if not same:
            continue
        for sg in sorted(fam):
            T, F, H = diff(fam[sg], fam[0.5], seeds)
            out.append(f'  S-1 σ {sg}: agent TL {R.fmt(*T)}; agent fuel % {R.fmt(*F)}; human TL {R.fmt(*H)}')
        src = W / ('046' if panel == 'T' else '040c'); A = load(src)
        for name in sorted(k for k in A if k.startswith('U-')):
            if all(s in A[name] for s in seeds):
                beyond(out, name, A[name], fam, seeds)


def horizon(out):
    A = load(W / '049h'); fam, _, seeds = family('SEL')
    if 'OFF_ACT' not in A or fam is None:
        out.append('B6-H INCOMPLETE'); return
    out.append('== B6-H horizon screen, SELECT 100-104, ACT (049h); comparator always-SUMO in the same directory')
    for mode in ('fuel', 'time'):
        sub = []; R.rb6(sub, W / '049h', R.SEL, f'-H {mode} criterion', mode=mode); out += sub
    old = load(W / '040c')
    pairs = [('R3h', 'U-L-ACT-R3h_t{}_ACT', 'U-L-ACT-R3v6_t{}_ACT', old), ('R5h', 'U-L-ACT-R5h_t{}_ACT', 'U-L-ACT-R5a_t{}_ACT', A)]
    for lab, trip, appr, src in pairs:
        for t in (0, 1):
            a, b = A.get(trip.format(t)), src.get(appr.format(t))
            if a is None or b is None:
                out.append(f'  H-2 {lab} t{t}: missing'); continue
            T, F, H = diff(a, b, R.SEL)
            out.append(f'  H-2 {lab} t{t} trip - approach: agent TL {R.fmt(*T)}; agent fuel % {R.fmt(*F)}; human TL {R.fmt(*H)}')
    for name in sorted(k for k in A if k.startswith('U-')):
        beyond(out, name, A[name], fam, R.SEL)


if __name__ == '__main__':
    out = []; secs = sys.argv[1:] or ['sigma', 'horizon']
    for s in secs:
        {'sigma': sigma, 'horizon': horizon}[s](out)
    txt = '\n'.join(out) + '\n'; (W / f"report_b6sh_{'_'.join(secs)}.txt").write_text(txt); print(txt)
