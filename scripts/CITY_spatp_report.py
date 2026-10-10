#!/usr/bin/env python3
"""SPaT pilot / confirmation report (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendments R1-R3; written before any learned evaluation).
  pilot    dir research/city_sim/spat_pilot_20261004/eval_select (SELECT 100-104, FT): per learned seed (a) B6-1 vs always-SUMO; (b) vs σ*
           = σ 0.3 (frozen rule) and (c) SPaT - noSPaT paired by seed are DESCRIPTIVE; three-state σ labels; GLOSA descriptive.
           GATE: >= 1 learned seed of either arm passes (a) -> writes GATE_PASS.
  confirm  dir .../eval_confirm (420-429, FT; only if GATE_PASS): pooled fleet-seed x traffic (4 x 10) for each arm: (a), (b) vs σ*,
           and (c) SPaT vs noSPaT (fuel superiority + agent TL NI +0.5); per-seed (a); σ labels; GLOSA.
Endpoints are fuel-primary with TL / human constraints; no 'fuel OR TL' rule; reward values are never used."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
import scripts.CITY_s2_classify_v2 as C  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/spat_pilot_20261004'; SIG = ['0.0', '0.1', '0.2', '0.3', '0.4']; SSTAR = '0.3'


def rows(d):
    Rt = {}
    for f in Path(d).glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            Rt[f.stem] = {r['seed']: r for r in x['rows']}
    return Rt


def cmp(F, B, seeds, dr):
    """F: list of {seed: row} (fleet seeds), B: {seed: row}; cube [fleet, traffic]."""
    c = lambda k, pct=False: np.array([[100 * (f[s][k] / B[s][k] - 1) if pct else f[s][k] - B[s][k] for s in seeds] for f in F])
    return dict(fuel=R.crossed(c('fuel_agent', True), dr), tl=R.crossed(c('timeloss_agent'), dr), hu=R.crossed(c('timeloss_human'), dr), city=R.crossed(c('timeloss'), dr))


def a_pass(x, F, B, seeds):
    tel = np.mean([f[s]['teleports'] for f in F for s in seeds]); tel0 = np.mean([B[s]['teleports'] for s in seeds])
    unf = np.mean([f[s]['unfinished'] for f in F for s in seeds]); unf0 = np.mean([B[s]['unfinished'] for s in seeds])
    return x['fuel'][2] < 0 and x['tl'][2] < 0.5 and x['hu'][2] < 0.5 and tel <= tel0 + 1 and unf <= unf0, tel, tel0


def fmt(x):
    return f"fuel % {R.fmt(*x['fuel'])}; agent TL {R.fmt(*x['tl'])}; human TL {R.fmt(*x['hu'])}; city TL {R.fmt(*x['city'])}"


def labels(out, name, F, Rt, seeds):
    fam = {float(s): Rt[f'S{s}_FT'] for s in SIG}; fam[0.5] = Rt['OFF_FT']
    cT = {sg: np.array([[f[s]['timeloss_agent'] - B[s]['timeloss_agent'] for s in seeds] for f in F]) for sg, B in fam.items()}
    cF = {sg: np.array([[100 * (f[s]['fuel_agent'] / B[s]['fuel_agent'] - 1) for s in seeds] for f in F]) for sg, B in fam.items()}
    C.classify(name, cT, cF, out)


def pilot():
    d = D / 'eval_select'; Rt = rows(d); seeds = R.SEL; dr = R.draws((1, len(seeds))); out = ['== SPaT pilot, SELECT 100-104, FT (fuel primary; σ* = 0.3 frozen)']
    off, sst = Rt['OFF_FT'], Rt[f'S{SSTAR}_FT']; gate = False
    for arm in ('on', 'off'):
        for sd in (13, 113):
            k = f'B{arm}_s{sd}'
            if k not in Rt:
                out.append(f'  {k}: MISSING'); continue
            xa = cmp([Rt[k]], off, seeds, dr); ok, tel, tel0 = a_pass(xa, [Rt[k]], off, seeds); gate |= ok
            xb = cmp([Rt[k]], sst, seeds, dr)
            out.append(f'  {k} (a) vs always-SUMO: {fmt(xa)}; teleports {tel:.1f} ({tel0:.1f}) -> {"PASS" if ok else "FAIL"}')
            out.append(f'      (b, descriptive) vs σ*: {fmt(xb)}')
            labels(out, f'      σ labels {k}', [Rt[k]], Rt, seeds)
    for sd in (13, 113):
        if f'Bon_s{sd}' in Rt and f'Boff_s{sd}' in Rt:
            out.append(f'  (c, descriptive) SPaT - noSPaT seed {sd}: {fmt(cmp([Rt[f"Bon_s{sd}"]], Rt[f"Boff_s{sd}"], seeds, dr))}')
    if 'GLOSA_FT' in Rt:
        out.append(f'  GLOSA (simple heuristic) vs always-SUMO: {fmt(cmp([Rt["GLOSA_FT"]], off, seeds, dr))}')
    out.append(f'PILOT GATE (>= 1 learned seed passes (a)): {"PASS -> confirmation runs" if gate else "FAIL -> the SPaT branch stops for this recipe / budget"}')
    if gate:
        (d / 'GATE_PASS').write_text('1\n')
    txt = '\n'.join(out) + '\n'; (D / 'report_pilot.txt').write_text(txt); print(txt)


def confirm():
    d = D / 'eval_confirm'; Rt = rows(d); seeds = list(range(420, 430)); dr = R.draws((4, len(seeds))); out = ['== SPaT confirmation, 420-429, FT, pooled over seeds 213-513']
    off, sst = Rt['OFF_FT'], Rt[f'S{SSTAR}_FT']; NEW = (213, 313, 413, 513)
    for arm in ('on', 'off'):
        F = [Rt[f'B{arm}_s{s}'] for s in NEW]; xa = cmp(F, off, seeds, dr); ok, tel, tel0 = a_pass(xa, F, off, seeds)
        per = [a_pass(cmp([f], off, seeds, R.draws((1, len(seeds)))), [f], off, seeds) for f in F]; okall = all(p[1] <= p[2] + 1 for p in per)
        xb = cmp(F, sst, seeds, dr); okb = xb['fuel'][2] < 0 and xb['tl'][2] < 0.5 and xb['hu'][2] < 0.5
        out.append(f'  B-{arm}SPaT (a) vs always-SUMO: {fmt(xa)} -> {"SUPPORTED" if ok and okall else "NOT SUPPORTED"} (per-seed teleport rule {"ok" if okall else "violated"}); per-seed (a) {[bool(p[0]) for p in per]}')
        out.append(f'  B-{arm}SPaT (b) vs σ* = 0.3: {fmt(xb)} -> {"SUPPORTED" if okb else "NOT SUPPORTED"}')
        labels(out, f'  σ labels B-{arm}SPaT pooled', F, Rt, seeds)
    Fon = [Rt[f'Bon_s{s}'] for s in NEW]; Foff = [Rt[f'Boff_s{s}'] for s in NEW]
    cc = lambda k, pct=False: np.array([[100 * (a[s][k] / b[s][k] - 1) if pct else a[s][k] - b[s][k] for s in seeds] for a, b in zip(Fon, Foff)])
    xf, xt = R.crossed(cc('fuel_agent', True), dr), R.crossed(cc('timeloss_agent'), dr)
    out.append(f'  (c) SPaT - noSPaT (paired by policy seed): fuel % {R.fmt(*xf)}; agent TL {R.fmt(*xt)} -> {"SUPPORTED" if xf[2] < 0 and xt[2] < 0.5 else "NOT SUPPORTED"}')
    if 'GLOSA_FT' in Rt:
        out.append(f'  GLOSA (simple heuristic) vs always-SUMO: {fmt(cmp([Rt["GLOSA_FT"]], off, seeds, R.draws((1, len(seeds)))))}')
    txt = '\n'.join(out) + '\n'; (D / 'report_confirm.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    {'pilot': pilot, 'confirm': confirm}[sys.argv[1]]()
