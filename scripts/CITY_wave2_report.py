#!/usr/bin/env python3
"""Report of spool jobs 030-090 (research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md and PROTOCOL_CITY_FLEET_UPGRADE_20261004.md;
written 04/10/2026 wake 3 before any of these jobs produced a row).  Usage: CITY_wave2_report.py [030 040 050 060 070 080 090]; a section
whose job output is incomplete prints INCOMPLETE and nothing else."""
import json, sys
from pathlib import Path
import numpy as np

W = Path('research/city_sim/wave2_20261004'); SEL = [100, 101, 102, 103, 104]; TST = list(range(200, 210)); T = [0, 1, 2, 3]
PAIRS = [('RJ0', 'RL-J:0', 'L-ACT:0'), ('RJ1', 'RL-J:1', 'L-ACT:1'), ('SH0', 'SIM-halt:0', 'SIM-halt:0'), ('SH1', 'SIM-halt:1', 'SIM-halt:1')]
REC = ('FTv1', 'FTv2', 'NEWv2')


def load(d, by_tag=False):
    R = {}
    for f in Path(d).glob('*.json'):
        if f.name.startswith('report'):
            continue
        x = json.loads(f.read_text())
        if not isinstance(x, dict) or x.get('status') != 'COMPLETE':
            continue
        for r in x['rows']:
            R[(f.stem, r['seed']) if by_tag else (r['light'], r['fleet'], r['seed'])] = r
    return R


def m(R, l, f, k, seeds):
    return float(np.mean([R[(l, f, s)][k] for s in seeds]))


def boot2(D, rng):
    n, k = D.shape; bs = [D[rng.integers(0, n, n)][:, rng.integers(0, k, k)].mean() for _ in range(2000)]
    return np.percentile(bs, [2.5, 97.5])


def qualifying():
    R = load(W / '030'); q = []
    for X, L0, F0 in PAIRS:
        for rc in REC:
            F1 = f'U:{rc}_{X}'
            if all((L0, f, s) in R for f in (F0, F1) for s in SEL) and m(R, L0, F1, 'timeloss_agent', SEL) - m(R, L0, F0, 'timeloss_agent', SEL) <= -0.5:
                q.append((X, L0, F0, F1))
    return q


def r030(out):
    R = load(W / '030'); need = [(L, F, s) for X, L0, F0 in PAIRS for F in [F0, 'human'] + [f'U:{r}_{X}' for r in REC] for L in (L0, 'ACT') for s in SEL + TST]
    need += [(L, f'U:L-ACT-v2_t{t}', s) for t in (0, 1) for L in ['ACT'] + [f'RL-H:{i}' for i in T] for s in SEL]
    miss = [k for k in need if k not in R]
    if miss:
        out.append(f'030 INCOMPLETE ({len(miss)} missing, e.g. {miss[:2]})'); return
    out.append('== 030 F1 evaluation (fleet upgraded, light frozen)')
    for X, L0, F0 in PAIRS:
        line = [f'  {X} L0={L0}: F0 {F0} agent/human/city {m(R, L0, F0, "timeloss_agent", SEL):.2f}/{m(R, L0, F0, "timeloss_human", SEL):.2f}/{m(R, L0, F0, "timeloss", SEL):.2f}']
        for rc in REC:
            F1 = f'U:{rc}_{X}'
            line.append(f'{rc} dAgent {m(R, L0, F1, "timeloss_agent", SEL) - m(R, L0, F0, "timeloss_agent", SEL):+.2f} dHuman {m(R, L0, F1, "timeloss_human", SEL) - m(R, L0, F0, "timeloss_human", SEL):+.2f} '
                        f'(TEST {m(R, L0, F1, "timeloss_human", TST) - m(R, L0, F0, "timeloss_human", TST):+.2f}) dCity {m(R, L0, F1, "timeloss", SEL) - m(R, L0, F0, "timeloss", SEL):+.2f} '
                        f'dFuelAgent {100 * (m(R, L0, F1, "fuel_agent", SEL) / m(R, L0, F0, "fuel_agent", SEL) - 1):+.1f}%')
        out.append(' | '.join(line))
    q = qualifying(); out.append(f'U-1 qualifying upgrades (agent TL under L0 down >= 0.5 s/veh, SELECT): {[(x[0], x[3]) for x in q]}')
    if q:
        dh = [(x[0], x[3], m(R, x[1], x[3], 'timeloss_human', SEL) - m(R, x[1], x[2], 'timeloss_human', SEL), m(R, x[1], x[3], 'timeloss_human', TST) - m(R, x[1], x[2], 'timeloss_human', TST)) for x in q]
        ok = [d for d in dh if d[2] <= 0.5 and d[3] <= 0.5]
        out.append(f'U-2 human TL change under L0 (SELECT, TEST): {[(d[0], d[1], round(d[2], 2), round(d[3], 2)) for d in dh]}; within +0.5 on both: {len(ok)}/{len(dh)} '
                   f"-> {'SUPPORTED' if len(ok) >= 0.75 * len(dh) else 'NOT SUPPORTED'} (asymmetry: the frozen light's users are not hurt)")
    else:
        out.append('U-2 not evaluable: no qualifying upgrade (the F-branch is reported empty, as registered)')
    rng = np.random.default_rng(0)
    for rc in REC:
        D = np.array([[R[(L0, f'U:{rc}_{X}', s)]['timeloss'] - R[(L0, F0, s)]['timeloss'] for s in SEL + TST] for X, L0, F0 in PAIRS]); lo, hi = boot2(D, rng)
        out.append(f'U-3 {rc}: city TL change under L0 {D.mean():+.2f} [{lo:+.2f}, {hi:+.2f}] (pairs x SELECT+TEST seeds) -> {"SUPPORTED" if hi < 0 else "NOT SUPPORTED"}')
    v = W / '030' / 'v3_cmd_realized.json'
    if v.exists():
        V = json.loads(v.read_text()); out.append('V3-1 realized-idle decisions avoided by command (ACT, seeds 100-101): ' + ', '.join(f"{r['fleet']} s{r['seed']} {r['idle_avoided_of_real_idle']:.3f}" for r in V) +
                                                  f" -> {'SUPPORTED' if all(r['idle_avoided_of_real_idle'] <= 0.2 for r in V if 'v2' in r['fleet']) else 'NOT SUPPORTED'}")
    reg = [np.mean([m(R, f'RL-H:{i}', f'U:L-ACT-v2_t{t}', 'timeloss_agent', SEL) - m(R, 'ACT', f'U:L-ACT-v2_t{t}', 'timeloss_agent', SEL) for i in T]) for t in (0, 1)]
    out.append(f'V3-2 v2 fleets agent regression under RL-H (mean over RL-H_0..3, vs ACT): t0 {reg[0]:+.2f}, t1 {reg[1]:+.2f} -> {"SUPPORTED" if max(reg) > 2 else "NOT SUPPORTED"} '
               f'(v2 under ACT agent/human TL: ' + ', '.join(f"t{t} {m(R, 'ACT', f'U:L-ACT-v2_t{t}', 'timeloss_agent', SEL):.2f}/{m(R, 'ACT', f'U:L-ACT-v2_t{t}', 'timeloss_human', SEL):.2f}" for t in (0, 1)) + ')')


def r040(out):
    R = load(W / '040', by_tag=True); tags = {k[0] for k in R}
    need = [f'rec_RLH{t}' for t in T] + ['rec_ACT'] + [f'rec_{X}' for X, _, _ in PAIRS]
    need += [f'rep_{r}_{f}' for r in [f'RLH{t}' for t in T] + ['ACT'] for f in ('human', 'L-ACT-0', 'L-ACT-1', 'L-ACT-2', 'L-ACT-3', 'L-RLH-0')]
    need += [f'rep_{X}_{f}' for X, _, F0 in PAIRS for f in [F0.replace(':', '-'), 'human'] + [f'U-{r}_{X}' for r in REC]]
    miss = [t for t in need if t not in tags]
    if miss:
        out.append(f'040 INCOMPLETE ({len(miss)} tags missing, e.g. {miss[:2]})'); return
    out.append('== 040 F3 open-loop discharge')
    own = {f'RLH{t}': 'human' for t in T}; own['ACT'] = 'human'; own.update({X: F0.replace(':', '-') for X, _, F0 in PAIRS}); d0 = {}
    for r, f in own.items():
        d0[r] = all(R[(f'rep_{r}_{f}', s)]['timeloss'] == R[(f'rec_{r}', s)]['timeloss'] for s in SEL)
    out.append(f'D-0 replay with the recording fleet reproduces the recording: {d0}')
    rate = lambda tag: float(np.mean([R[(tag, s)]['per_green_second'] for s in SEL]))
    if all(d0[f'RLH{t}'] for t in T):
        rel = {f: np.mean([rate(f'rep_RLH{t}_{f}') / rate(f'rep_RLH{t}_human') - 1 for t in T]) for f in ('L-ACT-0', 'L-ACT-1', 'L-ACT-2', 'L-ACT-3', 'L-RLH-0')}
        out.append(f"D-1 discharge rate vs human under replayed RL-H_t: {', '.join(f'{k} {100 * v:+.1f}%' for k, v in rel.items())} -> "
                   f"{'SUPPORTED' if rel['L-ACT-0'] <= -0.05 and abs(rel['L-ACT-3']) <= 0.05 else 'NOT SUPPORTED'}")
    else:
        out.append('D-1 not evaluable: D-0 failed on an RL-H recording')
    q = qualifying(); res = []
    for X, L0, F0, F1 in q:
        if d0.get(X):
            res.append((X, F1, rate(f"rep_{X}_{F1.replace(':', '-')}") / rate(f"rep_{X}_{F0.replace(':', '-')}") - 1))
    out.append(f"D-2 qualifying F1 discharge vs F0 under replayed L0: {[(a, b, round(100 * c, 1)) for a, b, c in res]} -> "
               + (('SUPPORTED' if all(abs(c) <= 0.05 for _, _, c in res) else 'NOT SUPPORTED') if res else 'not evaluable (no qualifying upgrade with D-0)'))
    out.append('D-3 (reported) discharge per green second and start-up delay: ' + '; '.join(
        f"{t[4:]} {rate(t):.3f}/{np.nanmean([R[(t, s)]['startup_mean'] for s in SEL]):.2f}" for t in sorted(tags) if t.startswith('rep_')))


def r050(out):
    R = load(W / '050', by_tag=True); tags = {k[0] for k in R}
    need = [f'L_RLH{t}_F{f}_{g}' for t in T for f in T for g in ('none', 'fallback', 'greenPoos')] + [f'S_RLH{t}_F{f}' for t in T for f in T] + [f'F_F{f}' for f in T] + [f'B_F{f}_{g}' for f in T for g in ('none', 'greenPoos')]
    miss = [t for t in need if t not in tags]
    if miss:
        out.append(f'050 INCOMPLETE ({len(miss)} tags missing)'); return
    wtl = lambda tag: float(np.mean([np.mean([R[(tag, s)]['tl_by_depart_window'][w] for w in ('1800', '2700', '3600', '4500')]) for s in TST]))
    worst = lambda tag: float(np.mean([max(R[(tag, s)]['tl_by_depart_window'][w] for w in ('1800', '2700', '3600', '4500')) for s in TST]))
    out.append('== 050 P2 mid-run handoff (TEST 200-209; window = trips departing in [1800, 5400))')
    h1 = [wtl(f'L_RLH{t}_F{f}_none') > wtl(f'B_F{f}_none') for t in T for f in T]
    out.append(f"H-1 plain light-only upgrade raises window city TL: {sum(h1)}/16 (>= 10) -> {'SUPPORTED' if sum(h1) >= 10 else 'NOT SUPPORTED'}")
    h2 = [(wtl(f'L_RLH{t}_F{f}_greenPoos') < wtl(f'B_F{f}_greenPoos')) and (wtl(f'L_RLH{t}_F{f}_greenPoos') < wtl(f'B_F{f}_none')) for t in T for f in T]
    out.append(f"H-2 guarded light-only upgrade below both no-swap baselines: {sum(h2)}/16 (>= 12) -> {'SUPPORTED' if sum(h2) >= 12 else 'NOT SUPPORTED'}")
    for name, fmt in (('light-only plain', 'L_RLH{t}_F{f}_none'), ('light-only fallback', 'L_RLH{t}_F{f}_fallback'), ('light-only green+oos', 'L_RLH{t}_F{f}_greenPoos'), ('simultaneous', 'S_RLH{t}_F{f}')):
        v = [wtl(fmt.format(t=t, f=f)) - wtl(f'B_F{f}_none') for t in T for f in T]; wv = [worst(fmt.format(t=t, f=f)) for t in T for f in T]
        out.append(f'H-3 {name}: window TL minus plain no-swap {np.mean(v):+.2f} (cells worse {sum(x > 0 for x in v)}/16), worst window mean {np.mean(wv):.2f}')
    out.append('H-3 fleet-only (L-ACT_f -> L-RLH_f under ACT): ' + ', '.join(f'F{f} {wtl(f"F_F{f}") - wtl(f"B_F{f}_none"):+.2f}' for f in T))


def r060(out):
    R = load(W / '060', by_tag=True); tags = {k[0] for k in R}
    if len(tags) < 80:
        out.append(f'060 INCOMPLETE ({len(tags)}/80)'); return
    out.append('== 060 F2 observation adapters at the frozen light (SELECT; human / city TL change vs raw)')
    for X, L0, F0 in PAIRS:
        for F in [F0] + [f'U:{r}_{X}' for r in REC]:
            fs = F.replace(':', '-'); base = f'{X}_{fs}_raw'
            cells = []
            for A in ('q-0p5-0', 'q-1-0', 'q-1-0p5', 'q-1-1'):
                t = f'{X}_{fs}_{A}'
                cells.append(f"{A} {np.mean([R[(t, s)]['timeloss_human'] - R[(base, s)]['timeloss_human'] for s in SEL]):+.2f}/{np.mean([R[(t, s)]['timeloss'] - R[(base, s)]['timeloss'] for s in SEL]):+.2f}")
            out.append(f'  {X} {F}: ' + ', '.join(cells))
    out.append('A-1 is evaluated only on pairs where U-2 found harm (see 030); A-2 is the table above.')


def r070(out):
    R = load(W / '070' / 'eval', by_tag=True); tags = {k[0] for k in R}
    if not tags:
        out.append('070 INCOMPLETE'); return
    B = load(W / '030'); out.append('== 070 DC-Ada comparator (affine input transform tuned on training seeds; city / human TL change vs raw)')
    for X, L0, F0 in PAIRS:
        for F in (F0, f'U:FTv2_{X}'):
            for seeds, lab in ((SEL, '100'), (TST, '200')):
                t = f"eval_{X}_{F.replace(':', '-')}_{lab}"
                if (t, seeds[0]) in R:
                    out.append(f"  {X} {F} {'SELECT' if lab == '100' else 'TEST'}: city {np.mean([R[(t, s)]['timeloss'] - B[(L0, F, s)]['timeloss'] for s in seeds]):+.2f} "
                               f"human {np.mean([R[(t, s)]['timeloss_human'] - B[(L0, F, s)]['timeloss_human'] for s in seeds]):+.2f}")


def r080(out):
    R = load(W / '080', by_tag=True); tags = {k[0] for k in R}
    if len(tags) < 120:
        out.append(f'080 INCOMPLETE ({len(tags)}/120)'); return
    tg = lambda l, f, g: f"{l}_{f}_{g}".replace(':', '-').replace('+', 'P')
    d = [np.mean([R[(tg(f'RL-H:{i}', f'L-RLH:{j}', 'green+oos'), s)]['timeloss_agent'] - R[(tg(f'RL-H:{i}', f'L-RLH:{j}', 'none'), s)]['timeloss_agent'] for s in SEL]) for i in T for j in T]
    out.append('== 080 L3 guards on other fleets')
    out.append(f"G-L3 L-RLH_t under RL-H: agent TL change (green+oos - none) <= +1.0 in {sum(x <= 1.0 for x in d)}/16 (>= 14) -> {'SUPPORTED' if sum(x <= 1.0 for x in d) >= 14 else 'NOT SUPPORTED'}; mean {np.mean(d):+.2f}")
    for L in ('ACT', 'MP', 'RL-H:0', 'RL-H:1', 'RL-H:2', 'RL-H:3'):
        out.append(f'  {L}: ' + ', '.join(f"{F} {np.mean([R[(tg(L, F, 'green+oos'), s)]['timeloss'] - R[(tg(L, F, 'none'), s)]['timeloss'] for s in SEL]):+.2f}"
                                       for F in ('L-RLH:0', 'L-RLH:1', 'L-RLH:2', 'L-RLH:3', 'SIM-halt:0', 'SIM-halt:1', 'SIM-halt:2', 'SIM-halt:3', 'L-FT:0', 'L-FT:1')) + '  (city TL change)')


def r090(out):
    R = load(W / '090', by_tag=True); tags = {k[0] for k in R}
    if len(tags) < 25:
        out.append(f'090 INCOMPLETE ({len(tags)}/25)'); return
    X2 = load(Path('research/city_sim/xplay2_20261004'))
    out.append('== 090 MaxPressure (published light) x fleets: city TL MP vs ACT')
    spec = lambda f: f if f == 'human' else f[:f.rfind('-')] + ':' + f[f.rfind('-') + 1:]
    out.append('  ' + ', '.join(f"{t[3:]} MP {np.mean([R[(t, s)]['timeloss'] for s in SEL]):.2f} / ACT {np.mean([X2[('ACT', spec(t[3:]), s)]['timeloss'] for s in SEL]):.2f}"
                            for t in sorted(tags)))


if __name__ == '__main__':
    out = []; fns = dict(zip(['030', '040', '050', '060', '070', '080', '090'], [r030, r040, r050, r060, r070, r080, r090]))
    for k in (sys.argv[1:] or list(fns)):
        fns[k](out)
    txt = '\n'.join(out) + '\n'; (W / f"report_{'_'.join(sys.argv[1:]) or 'all'}.txt").write_text(txt); print(txt)
