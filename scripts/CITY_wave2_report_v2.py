#!/usr/bin/env python3
"""Report VERSION 2 for the two-population wave (Amendment W3 of research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md; written
04/10/2026 05:2x EDT, wake 3, before any held job produced a row, and before re-reading B4F / L4 under the new inference).
Inference (user audit items 2-3):
  * crossed bootstrap over light-seed x fleet-seed x traffic-seed (cross-play cells), or pair x traffic-seed (matched pairs); 2000 draws,
    rng 0, the SAME index draws for every arm compared;
  * "no harm" = non-inferiority: one-sided 95 % UPPER bound of the harm (bad direction positive) < the pre-set margin;
  * SELECT (100-104) and VALIDATION (200-209) are reported separately, never pooled.
Sections: b4f, l4 (analysis version 2; the registered verdicts in their own reports are unchanged), 021, 030, 040, 055 (inside b4f/l4),
095 (handoff, trip-weighted from stored counts and sums), and 060/070/080/090 via CITY_wave2_report.  Usage: CITY_wave2_report_v2.py [sections]"""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report as V1  # noqa: E402

W = Path('research/city_sim/wave2_20261004'); SEL = [100, 101, 102, 103, 104]; VAL = list(range(200, 210)); T = [0, 1, 2, 3]; B = 2000
H0 = Path('research/city_sim/xplay_h0_20261004'); GATE = Path('research/city_sim/xplay_gate_20261004'); GG = Path('research/city_sim/green_guard_20261004')


def load(d, key):
    R = {}
    for f in Path(d).glob('*.json'):
        if f.name.startswith('report'):
            continue
        x = json.loads(f.read_text())
        if isinstance(x, dict) and x.get('status') == 'COMPLETE':
            for r in x['rows']:
                k = key(r)
                if k is not None:
                    R[k] = r
    return R


def draws(shape, seed=0):
    rng = np.random.default_rng(seed)
    return [tuple(rng.integers(0, n, n) for n in shape) for _ in range(B)]


def crossed(D, dr):
    """D[light, fleet, traffic] (or D[pair, traffic]); returns point, two-sided 95 % CI, one-sided 95 % upper."""
    v = np.array([D[np.ix_(*ix)].mean() for ix in dr])
    return float(D.mean()), np.percentile(v, [2.5, 97.5]), float(np.percentile(v, 95))


def fmt(p, ci, up=None):
    return f'{p:+.2f} [{ci[0]:+.2f}, {ci[1]:+.2f}]' + (f' (one-sided 95 % upper {up:+.2f})' if up is not None else '')


def rb4f(out):
    P = load(H0, lambda r: (r['light'], r['fleet'], r['seed']) if r['sense'] == 'default' else None)
    G = load(GATE, lambda r: (r['light'], r['fleet'], r['gate'], r['seed']))
    Rn = load(W / '055', lambda r: (r['light'], r['fleet'], r['guard'], r['seed']))
    out.append('== B4F analysis v2 (crossed light-seed x fleet-seed x traffic-seed; registered verdicts unchanged in xplay_gate_20261004/report.txt)')
    dr = draws((4, 4, 5)); L = lambda i: f'RL-H:{i}'; F = lambda j: f'L-ACT:{j}'
    cube = lambda fn: np.array([[[fn(i, j, s) for s in SEL] for j in T] for i in T])
    dA = cube(lambda i, j, s: G[(L(i), F(j), 'fallback', s)]['timeloss_agent'] - P[(L(i), F(j), s)]['timeloss_agent'])
    out.append(f'FB-1 v2 agent TL change (fallback - plain) {fmt(*crossed(dA, dr))}')
    dH = cube(lambda i, j, s: G[(L(i), F(j), 'fallback', s)]['timeloss_human'] - P[(L(i), F(j), s)]['timeloss_human'])
    p, ci, up = crossed(dH, dr)
    out.append(f'FB-3 v2 human TL change {fmt(p, ci, up)} -> NI at margin +0.5: {"SUPPORTED" if up < 0.5 else "NOT SUPPORTED"}')
    off = cube(lambda i, j, s: G[(L(i), F(j), 'fallback', s)]['timeloss'] - P[(L(i), 'human', s)]['timeloss'])
    out.append(f'   comparator always-SUMO (= human-only run, verified identity): city TL fallback - always-SUMO {fmt(*crossed(off, dr))}')
    if all((L(i), F(j), 'random:0.046', s) in Rn for i in T for j in T for s in SEL):
        rnd = cube(lambda i, j, s: G[(L(i), F(j), 'fallback', s)]['timeloss'] - Rn[(L(i), F(j), 'random:0.046', s)]['timeloss'])
        out.append(f'   comparator matched-rate random override (P 0.046): city TL fallback - random {fmt(*crossed(rnd, dr))}')
    else:
        out.append('   comparator random override: 055 INCOMPLETE')


def rl4(out):
    S = load(GG / 'select', lambda r: (r['light'], r['fleet'], r['guard'], r['seed'])); X = load(GG / 'test', lambda r: (r['light'], r['fleet'], r['guard'], r['seed']))
    P = load(H0, lambda r: (r['light'], r['fleet'], r['seed']) if r['sense'] == 'default' else None)
    Rn = load(W / '055', lambda r: (r['light'], r['fleet'], r['guard'], r['seed']))
    out.append('== L4 analysis v2 (crossed; registered verdicts unchanged in green_guard_20261004/report.txt; 200-209 = VALIDATION from now on)')
    dr = draws((4, 4, 5)); L = lambda i: f'RL-H:{i}'; F = lambda j: f'L-ACT:{j}'
    cube = lambda fn, seeds=SEL: np.array([[[fn(i, j, s) for s in seeds] for j in T] for i in T])
    out.append(f"GG-1 v2 agent TL change (green+oos - none) {fmt(*crossed(cube(lambda i, j, s: S[(L(i), F(j), 'green+oos', s)]['timeloss_agent'] - S[(L(i), F(j), 'none', s)]['timeloss_agent']), dr))}")
    gain = cube(lambda i, j, s: S[(L(i), F(j), 'green+oos', s)]['timeloss'] - S[('ACT', F(j), 'none', s)]['timeloss'])
    out.append(f'GG-2 v2 city TL, guarded RL-H upgrade minus ACT with plain fleet (SELECT) {fmt(*crossed(gain, dr))}')
    gainV = cube(lambda i, j, s: X[(L(i), F(j), 'green+oos', s)]['timeloss'] - X[('ACT', F(j), 'none', s)]['timeloss'], VAL)
    out.append(f'GG-2 v2 same on VALIDATION 200-209 {fmt(*crossed(gainV, draws((4, 4, 10))))}')
    drA = draws((4, 5)); sq = lambda fn: np.array([[fn(j, s) for s in SEL] for j in T])
    dTa = sq(lambda j, s: S[('ACT', F(j), 'green+oos', s)]['timeloss_agent'] - S[('ACT', F(j), 'none', s)]['timeloss_agent'])
    dFa = sq(lambda j, s: 100 * (S[('ACT', F(j), 'green+oos', s)]['fuel_agent'] / S[('ACT', F(j), 'none', s)]['fuel_agent'] - 1))
    p1, c1, u1 = crossed(dTa, drA); p2, c2, u2 = crossed(dFa, drA)
    out.append(f'GG-4 v2 NI under ACT (fleet-seed x traffic-seed): agent TL {fmt(p1, c1, u1)} vs +0.5; agent fuel % {fmt(p2, c2, u2)} vs +2 % -> '
               f"{'SUPPORTED' if (u1 < 0.5 and u2 < 2.0) else 'NOT SUPPORTED'}")
    off = cube(lambda i, j, s: S[(L(i), F(j), 'green+oos', s)]['timeloss'] - P[(L(i), 'human', s)]['timeloss'])
    out.append(f'   comparator always-SUMO: city TL guarded fleet - always-SUMO (human-only) {fmt(*crossed(off, dr))}')
    if all((L(i), F(j), 'random:0.45', s) in Rn for i in T for j in T for s in SEL):
        rnd = cube(lambda i, j, s: S[(L(i), F(j), 'green+oos', s)]['timeloss'] - Rn[(L(i), F(j), 'random:0.45', s)]['timeloss'])
        out.append(f'   comparator matched-rate random override (P 0.45): city TL green+oos - random {fmt(*crossed(rnd, dr))}')
    else:
        out.append('   comparator random override: 055 INCOMPLETE')


def r021(out):
    f = W / '021' / 'v2_trace.json'
    if not f.exists():
        out.append('021 INCOMPLETE'); return
    d = json.loads(f.read_text()); out.append(f"== 021 reward-v2 trace: VERDICT {d['verdict']}")
    for r in d['rows']:
        out.append('   ' + ', '.join(f'{k} {v}' for k, v in r.items()))


def r030(out):
    R = load(W / '030', lambda r: (r['light'], r['fleet'], r['seed']))
    need = [(L, F, s) for X, L0, F0 in V1.PAIRS for F in [F0, 'human'] + [f'U:{r}_{X}' for r in V1.REC] for L in (L0, 'ACT') for s in SEL + VAL]
    if any(k not in R for k in need):
        out.append(f'030 INCOMPLETE ({sum(k not in R for k in need)} missing)'); return
    out.append('== 030 v2 (SELECT and VALIDATION separate; matched-pair bootstrap pair x traffic-seed)')
    q = V1.qualifying(); out.append(f'U-1 qualifying upgrades (SELECT gate, not a hypothesis): {[(x[0], x[3]) for x in q]}')
    for name, seeds in (('SELECT', SEL), ('VALIDATION', VAL)):
        dr = draws((len(q) or 1, len(seeds)))
        if q:
            dH = np.array([[R[(x[1], x[3], s)]['timeloss_human'] - R[(x[1], x[2], s)]['timeloss_human'] for s in seeds] for x in q])
            p, ci, up = crossed(dH, dr)
            out.append(f'U-2 {name}: human TL change under L0 (F1 - F0), qualifying pairs {fmt(p, ci, up)} -> NI at +0.5: {"SUPPORTED" if up < 0.5 else "NOT SUPPORTED"}')
        for rc in V1.REC:
            D = np.array([[R[(L0, f'U:{rc}_{X}', s)]['timeloss'] - R[(L0, F0, s)]['timeloss'] for s in seeds] for X, L0, F0 in V1.PAIRS])
            out.append(f'U-3 {name} {rc}: city TL change under L0 {fmt(*crossed(D, draws((4, len(seeds)))))}')
    out.append('(V3 rows, fleet-benefit vs always-SUMO for v2 fleets, and the cmd/realized v2 diagnostic are in CITY_wave2_report.py 030 and v3_cmd_realized_v2.json)')


def r040(out):
    R = load(W / '040', lambda r: None)
    tags = {f.stem for f in (W / '040').glob('*.json') if f.stem.startswith(('rec_', 'rep_'))}   # dir 040 is shared with B6-R (job 040)
    if len(tags) < 59:
        out.append(f'040 INCOMPLETE ({len(tags)}/59)'); return
    Rt = {}
    for f in (W / '040').glob('*.json'):
        if f.stem.startswith(('rec_', 'rep_')):
            for r in json.loads(f.read_text())['rows']:
                Rt[(f.stem, r['seed'])] = r
    out.append('== 040 v2 (D-0 = full trace: phases, spentDuration, action digest, TL; startup censoring reported)')
    own = {f'RLH{t}': 'human' for t in T}; own['ACT'] = 'human'; own.update({X: F0.replace(':', '-') for X, _, F0 in V1.PAIRS})
    for r, f in own.items():
        ok = []
        for s in SEL:
            a = np.load(W / '040' / f'rec_{r}' / f'phases_s{s}.npz'); b = np.load(W / '040' / f'trace_{r}_{f}' / f'phases_s{s}.npz')
            ok.append(np.array_equal(a['phases'], b['phases']) and np.array_equal(a['spent'], b['spent']) and Rt[(f'rec_{r}', s)]['timeloss'] == Rt[(f'rep_{r}_{f}', s)]['timeloss']
                      and Rt[(f'rec_{r}', s)]['action_digest'] == Rt[(f'rep_{r}_{f}', s)]['action_digest'])
        out.append(f'D-0 {r}: {sum(ok)}/5 seeds trace-identical -> {"PASS" if all(ok) else "FAIL (excluded from D-1/D-2)"}')
    out.append('D-1 / D-2 are read as "response differs under the same forcing" only (audit item 6); closed-loop adapters vs guards decide repairs.')
    for t in sorted(tags):
        if t.startswith('rep_'):
            rs = [Rt[(t, s)] for s in SEL]
            out.append(f"   {t[4:]}: discharge/green-s {np.mean([r['per_green_second'] for r in rs]):.3f}, startup {np.nanmean([r['startup_mean'] for r in rs]):.2f} s "
                       f"(n {sum(r['startup_n'] for r in rs)}, censored {sum(r['startup_censored'] for r in rs)}), teleport exits {sum(r['teleport_exits'] for r in rs)}")


def r095(out):
    Rt = {}
    for f in (W / '050').glob('*.json'):
        if not f.name.startswith('report'):
            for r in json.loads(f.read_text())['rows']:
                Rt[(f.stem, r['seed'])] = r
    tags = {k[0] for k in Rt}
    if len(tags) < 76:
        out.append(f'095 INCOMPLETE ({len(tags)}/76)'); return
    def tw(tag, s, who=(0, 2)):                                     # trip-weighted TL of trips departing >= 1800, from counts / sums
        w = Rt[(tag, s)]['window_counts_sums']; n = sum(w[k][g] for k in w if int(k) >= 1800 for g in who); return sum(w[k][g + 1] for k in w if int(k) >= 1800 for g in who) / max(1, n)
    def pres(tag, s):
        c = Rt[(tag, s)]['cohort_counts_sums']['present']; return (c[1] + c[3]) / max(1, c[0] + c[2])
    def dly(tag, s):
        d = Rt[(tag, s)]['delay_by_window']; return sum(sum(v) for k, v in d.items() if int(k) >= 1800)
    dr = draws((4, 4, 10)); cube = lambda fn: np.array([[[fn(t, f, s) for s in VAL] for f in T] for t in T])
    out.append('== 095 (job 050) handoff, VALIDATION 200-209; endpoint = trip-weighted TL of trips departing in [1800, 5400) from stored counts / sums')
    h1 = cube(lambda t, f, s: tw(f'L_RLH{t}_F{f}_none', s) - tw(f'B_F{f}_none', s))
    out.append(f'H-1 plain light-only upgrade minus no-swap: {fmt(*crossed(h1, dr))}; cells worse {int((h1.mean(2) > 0).sum())}/16 (>= 10) -> {"SUPPORTED" if (h1.mean(2) > 0).sum() >= 10 else "NOT SUPPORTED"}')
    g1 = cube(lambda t, f, s: tw(f'L_RLH{t}_F{f}_greenPoos', s) - tw(f'B_F{f}_greenPoos', s)); g2 = cube(lambda t, f, s: tw(f'L_RLH{t}_F{f}_greenPoos', s) - tw(f'B_F{f}_none', s))
    both = ((g1.mean(2) < 0) & (g2.mean(2) < 0)).sum()
    out.append(f'H-2 guarded upgrade minus guarded no-swap {fmt(*crossed(g1, dr))}; minus plain no-swap {fmt(*crossed(g2, dr))}; cells below both {both}/16 (>= 12) -> {"SUPPORTED" if both >= 12 else "NOT SUPPORTED"}')
    for name, fm in (('present-at-swap cohort TL', pres), ('system delay increment after 1800 (veh-s)', dly)):
        for g in ('none', 'greenPoos'):
            D = cube(lambda t, f, s: fm(f'L_RLH{t}_F{f}_{g}', s) - fm(f'B_F{f}_{g}', s))
            out.append(f'H-3 {name}, light-only {g} minus no-swap {g}: {fmt(*crossed(D, dr))}')
    for name, fmt_ in (('simultaneous', 'S_RLH{t}_F{f}'), ('light-only fallback', 'L_RLH{t}_F{f}_fallback')):
        D = cube(lambda t, f, s: tw(fmt_.format(t=t, f=f), s) - tw(f'B_F{f}_none', s)); out.append(f'H-3 {name} minus plain no-swap: {fmt(*crossed(D, dr))}')
    sw = [Rt[(f'L_RLH{t}_F{f}_none', s)]['swap_trace'] for t in T for f in T for s in VAL]
    out.append(f"   swap trace: all lights switched {sum(x['never_switched'] == 0 for x in sw)}/{len(sw)} runs; intended phase {sum(x['phase_kept'] == x['n'] for x in sw)}/{len(sw)}; last switch max {max(x['last_switch'] for x in sw)}")


def rb6(out, d=None, seeds=None, tag='', mode='fuel'):
    """B6-1 screen / B6-2 confirmation (PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004 + Amendment B6-A1): fleet vs always-SUMO (SUMO's default
    driver model) on the same vehicles under ACT.  Per candidate: agent fuel superiority (one-sided upper < 0), agent TL NI (+0.5), human-vehicle
    TL NI (+0.5), city TL reported, teleports / run <= always-SUMO + 1, unfinished <= always-SUMO.  Writes <dir>/b6_verdicts.json."""
    d = Path(d) if d else W / '036'; seeds = seeds or SEL; Rt = {}
    for f in d.glob('*.json'):
        if not f.name.startswith('report') and not f.name.startswith('b6_'):
            x = json.loads(f.read_text())
            if not isinstance(x, dict) or 'rows' not in x:
                continue
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    cands = sorted({k[0][:-4] for k in Rt if k[0].endswith('_ACT') and k[0].startswith('U-')})   # fleet tags only (job 042 shares dir 040)
    if not cands or any((f'{F}_ACT', s) not in Rt or ('OFF_ACT', s) not in Rt for F in cands for s in seeds):
        out.append(f'B6{tag} INCOMPLETE ({d})'); return
    out.append(f'== B6{tag} fleet vs always-SUMO (SUMO default driver model) on the same vehicles, ACT, traffic {seeds[0]}-{seeds[-1]} ({d.name})')
    dr = draws((len(seeds),)); verdict = {}
    for F in cands:
        g = lambda k, base=None: np.array([Rt[(f'{F}_ACT', s)][k] - Rt[('OFF_ACT', s)][k] for s in seeds])
        fT = crossed(g('timeloss_agent'), dr); fH = crossed(g('timeloss_human'), dr); fC = crossed(g('timeloss'), dr)
        fF = crossed(np.array([100 * (Rt[(f'{F}_ACT', s)]['fuel_agent'] / Rt[('OFF_ACT', s)]['fuel_agent'] - 1) for s in seeds]), dr)
        tel = np.mean([Rt[(f'{F}_ACT', s)]['teleports'] for s in seeds]); tel0 = np.mean([Rt[('OFF_ACT', s)]['teleports'] for s in seeds])
        unf = np.mean([Rt[(f'{F}_ACT', s)]['unfinished'] for s in seeds]); unf0 = np.mean([Rt[('OFF_ACT', s)]['unfinished'] for s in seeds])
        ok = (fF[2] < 0 and fT[2] < 0.5 if mode == 'fuel' else fT[2] < 0 and fF[2] < 2.0) and fH[2] < 0.5 and tel <= tel0 + 1 and unf <= unf0
        verdict[F] = bool(ok)
        out.append(f'  {F}: agent fuel % {fmt(*fF)}; agent TL {fmt(*fT)}; human-vehicle TL {fmt(*fH)}; city TL {fmt(*fC)}; teleports/run {tel:.1f} (always-SUMO {tel0:.1f}); '
                   f'unfinished {unf:.1f} ({unf0:.1f}) -> {"PASS" if ok else "FAIL"}')
        regs = [f'{F}_RL-H-{i}' for i in T if (f'{F}_RL-H-{i}', seeds[0]) in Rt and (f'OFF_RL-H-{i}', seeds[0]) in Rt]
        if regs:
            out.append(f'     (reported) under RL-H_0..3, agent TL vs always-SUMO {np.mean([Rt[(r, s)]["timeloss_agent"] - Rt[("OFF_" + r[len(F) + 1:], s)]["timeloss_agent"] for r in regs for s in seeds]):+.2f}')
    (d / 'b6_verdicts.json').write_text(json.dumps(verdict, indent=1))
    out.append(f'  recipes with >= 1 passing seed: {sorted({F.rsplit("_t", 1)[0] for F, v in verdict.items() if v})} (a pass selects a recipe for B6-2; it is not a beneficial-fleet claim)')


def rb6t(out):
    """B6-T confirmation (PROTOCOL_CITY_B6 §B6-T, registered post hoc): TL superiority + fuel NI 2 %, new seeds 213/313, traffic 400-409."""
    rb6(out, W / '046', list(range(400, 410)), '-T time-beneficial confirmation (post hoc criterion)', mode='time')


def rb6c(out):
    rb6(out, W / '037', list(range(400, 410)), '-2 confirmation')


def ralstar(out):
    """A-L* on F* (PROTOCOL_CITY_B6 decision tree Branch P, registered 05:47; benefit = TIME per B6-T).  SELECT 100-104.
    AL*-1  regression: agent TL(F* | RL-H_t) - agent TL(F* | ACT) > 0 (crossed CI lower > 0; light-seed x fleet-seed x traffic)
    AL*-2  per guard, under RL-H: F* vs always-SUMO under the SAME light: agent TL superiority (upper < 0) and fuel NI (upper < +2 %);
           the guard with the lowest point agent TL is CHOSEN here and judged on VALIDATION in a follow-up job
    AL*-3  human-vehicle TL NI (+0.5) vs always-SUMO under the same light, for the chosen guard
    AL*-4  (reported) the same under RL-C50; release / guard shares"""
    d = W / '047'; f = d / 'FSTAR.txt'
    if not f.exists():
        out.append('A-L* INCOMPLETE (no F*: Branch P not run)'); return
    N = f.read_text().split('=')[1].strip(); Rt = {}
    for g in d.glob('*.json'):
        x = json.loads(g.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(g.stem, r['seed'])] = r
    tag = lambda t, L, gd: f"{N}_t{t}_{L}_{gd}".replace(':', '-').replace('+', 'P')
    dr = draws((4, 4, 5)); out.append(f'== A-L* on F* = {N} (time-beneficial per B6-T), SELECT; comparator always-SUMO under the same light')
    cube = lambda fn: np.array([[[fn(i, t, s) for s in SEL] for t in T] for i in T])
    reg = cube(lambda i, t, s: Rt[(tag(t, f'RL-H:{i}', 'none'), s)]['timeloss_agent'] - Rt[(tag(t, 'ACT', 'none'), s)]['timeloss_agent'])
    p_, ci, up = crossed(reg, dr)
    out.append(f'AL*-1 regression under RL-H (plain F*): agent TL {fmt(p_, ci, up)} -> {"SUPPORTED (F* regresses)" if ci[0] > 0 else "NOT SUPPORTED (F* does not regress under the learned light)"}')
    best = None
    for fam in ('RL-H', 'RL-C50'):
        for gd in ('none', 'fallback', 'clip', 'green+oos'):
            dT = cube(lambda i, t, s: Rt[(tag(t, f'{fam}:{i}', gd), s)]['timeloss_agent'] - Rt[(f'OFF_{fam}-{i}', s)]['timeloss_agent'])
            dF = cube(lambda i, t, s: 100 * (Rt[(tag(t, f'{fam}:{i}', gd), s)]['fuel_agent'] / Rt[(f'OFF_{fam}-{i}', s)]['fuel_agent'] - 1))
            dH = cube(lambda i, t, s: Rt[(tag(t, f'{fam}:{i}', gd), s)]['timeloss_human'] - Rt[(f'OFF_{fam}-{i}', s)]['timeloss_human'])
            T_, F_, H_ = crossed(dT, dr), crossed(dF, dr), crossed(dH, dr)
            sh = np.mean([Rt[(tag(t, f'{fam}:{i}', gd), s)]['guard_share'] for i in T for t in T for s in SEL])
            ok2 = T_[2] < 0 and F_[2] < 2.0
            lab = 'AL*-2' if fam == 'RL-H' else 'AL*-4'
            out.append(f'{lab} {fam} guard {gd}: agent TL vs always-SUMO {fmt(*T_)}; agent fuel % {fmt(*F_)}; human TL {fmt(*H_)}; release/guard share {sh:.3f}'
                       + (f' -> {"benefit kept" if ok2 else "benefit NOT kept"}' if fam == 'RL-H' else ''))
            if fam == 'RL-H' and (best is None or T_[0] < best[1]):
                best = (gd, T_[0], H_)
    out.append(f'AL*-2 chosen guard on SELECT (lowest point agent TL under RL-H): {best[0]}; AL*-3 human TL NI for it: upper {best[2][2]:+.2f} -> '
               f'{"SUPPORTED" if best[2][2] < 0.5 else "NOT SUPPORTED"} (SELECT; the verdict is read on VALIDATION in the follow-up job)')


if __name__ == '__main__':
    out = []; fns = dict(b4f=rb4f, l4=rl4, b6=rb6, b6c=rb6c, b6t=rb6t, alstar=ralstar, **{'021': r021, '030': r030, '040': r040, '095': r095})
    for k in (sys.argv[1:] or list(fns)):
        if k in fns:
            fns[k](out)
        else:
            getattr(V1, f'r{k}')(out)
    txt = '\n'.join(out) + '\n'; (W / f"report_v2_{'_'.join(sys.argv[1:]) or 'all'}.txt").write_text(txt); print(txt)
