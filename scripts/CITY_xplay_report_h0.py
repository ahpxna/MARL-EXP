#!/usr/bin/env python3
"""Report of B1 / B1b under Addendum A1 of research/city_sim/PROTOCOL_CITY_XPLAY_HCRAWL_20261004.md (written 04/10/2026 03:4x EDT,
wake 2, while the h0 panel ran and before any B1/B1b statistic was computed).  The analysis is CITY_xplay_report.py's, unchanged;
only the parity self-check is amended:
  * human-only rows (no CarRL, no set iteration) must reproduce Q7b exactly (1e-9);
  * fleet rows must lie within the jitter envelope J = max over (config, seed) of the range across hash seeds 0..4;
  * the determinism re-run (xplay_jitter/det0, PYTHONHASHSEED=0) must be bit-identical to the h0 panel.
The B1b verdicts are computed on the h0 panel (primary) and on the original random-hash panel (robustness)."""
import json
from pathlib import Path
import numpy as np

H0 = Path('research/city_sim/xplay_h0_20261004'); ORIG = Path('research/city_sim/xplay_20261004'); JIT = Path('research/city_sim/xplay_jitter_20261004')
Q7B = Path('research/city_sim/q7b_contract_20261002'); SEEDS = [100, 101, 102, 103, 104]; T = [0, 1, 2, 3]


def load(d):
    R = {}
    for f in d.glob('*.json'):
        if f.name.startswith('report'):
            continue
        x = json.loads(f.read_text())
        if x.get('status') != 'COMPLETE':
            continue
        for r in x['rows']:
            R[(r['light'], r['fleet'], r['sense'], r['seed'])] = r
    return R


def q7b_rows():
    for t in T:
        for q in json.loads((Q7B / f'eval_t{t}.json').read_text()):
            L = {'ACT': 'ACT', 'RL-H': f'RL-H:{t}', 'RL-C50': f'RL-C50:{t}', 'RL-J': f'RL-J:{t}'}.get(q['light']); F = {'human': 'human', 'L-ACT': f'L-ACT:{t}'}.get(q['fleet'])
            if L is not None and F is not None:
                yield (L, F, 'default', q['seed']), q


def parity(R0, reps, out):
    """reps: list of panels for hash seeds 1..4 (fleet configs only)."""
    J = dict(timeloss=0.0, approach_cost=0.0); nrep = 0
    for k, r in R0.items():
        if r['fleet'] == 'human' or r['sense'] != 'default':
            continue
        xs = [P[k] for P in reps if k in P]
        if len(xs) != len(reps):
            continue
        nrep += 1
        for m in J:
            v = [r[m]] + [x[m] for x in xs]; J[m] = max(J[m], max(v) - min(v))
    out.append(f"Jitter envelope over {nrep} (config, seed) pairs x {1 + len(reps)} hash seeds: J_TL {J['timeloss']:.3g} s/veh, J_cost {J['approach_cost']:.3g}")
    bad = []; nh = nf = 0
    for k, q in q7b_rows():
        if k not in R0:
            bad.append(('missing', k)); continue
        r = R0[k]
        if k[1] == 'human':
            nh += 1
            if abs(r['timeloss'] - q['timeloss']) > 1e-9:
                bad.append(('human-diff', k, r['timeloss'], q['timeloss']))
        else:
            nf += 1
            for m in ('timeloss', 'approach_cost'):
                if abs(r[m] - q[m]) > J[m] + 1e-12:
                    bad.append(('fleet-out-of-J', k, m, r[m], q[m]))
    D = load(JIT / 'det0'); det = [k for k in D if k not in R0 or any(D[k][m] != R0[k][m] for m in ('timeloss', 'approach_cost', 'hidden_a', 'hidden_h') if m in D[k])]
    ok = not bad and len(D) == 10 and not det and nrep == 80
    out.append(f"SELF-CHECK (A1): human rows exact {nh - len([b for b in bad if b[0] == 'human-diff'])}/{nh}; fleet rows within J "
               f"{nf - len({b[1] for b in bad if b[0] == 'fleet-out-of-J'})}/{nf}; determinism re-run {len(D) - len(det)}/{len(D)} bit-identical (expect 10/10); "
               f"jitter pairs {nrep}/80; problems {bad[:3]} -> {'PASS' if ok else 'FAIL'}")
    return ok, J


def analyse(R, out, tag):
    c = lambda L, F, s, sense='default': R[(L, F, sense, s)]['approach_cost']
    tl = lambda L, F, s, sense='default': R[(L, F, sense, s)]['timeloss']
    res = {}
    for fam in ('RL-H', 'RL-C50', 'RL-J'):
        M = np.array([[np.mean([c(f'{fam}:{i}', f'L-ACT:{j}', s) - c('ACT', f'L-ACT:{j}', s) for s in SEEDS]) for j in T] for i in T])
        Ms = np.array([[[c(f'{fam}:{i}', f'L-ACT:{j}', s) - c('ACT', f'L-ACT:{j}', s) for s in SEEDS] for j in T] for i in T])
        g = M.mean(); row = M.mean(1) - g; col = M.mean(0) - g; inter = M - g - row[:, None] - col[None, :]
        ss_r, ss_c, ss_i = 4 * (row ** 2).sum(), 4 * (col ** 2).sum(), (inter ** 2).sum(); tot = ss_r + ss_c + ss_i
        noise = Ms.var(2, ddof=1).mean() / 5
        CT = np.array([[np.mean([tl(f'{fam}:{i}', f'L-ACT:{j}', s) for s in SEEDS]) for j in T] for i in T])
        gain = [np.mean([tl('ACT', 'human', s) - tl(f'{fam}:{i}', 'human', s) for s in SEEDS]) for i in T]
        res[fam] = dict(M=M.tolist(), shares=dict(light=ss_r / tot, fleet=ss_c / tot, interaction=ss_i / tot), noise_var_of_cell_mean=float(noise),
                        city_TL=CT.tolist(), light_gain_human=gain)
        out.append(f"[{tag}] {fam} x L-ACT regression r (rows light t, cols fleet t'; diagonal = Q7b):")
        for i in T:
            out.append('   ' + ' '.join(f'{M[i, j]:+7.2f}' for j in T) + f"   | light gain (human) {gain[i]:+.2f} s/veh | city TL with fleet " + ' '.join(f'{CT[i, j]:6.2f}' for j in T))
        act = [np.mean([tl('ACT', f'L-ACT:{j}', s) for s in SEEDS]) for j in T]
        out.append(f"   variance shares of the 16 cell means: light {ss_r / tot:.2f}, fleet {ss_c / tot:.2f}, interaction {ss_i / tot:.2f} "
                   f"(cell-mean noise variance {noise:.3f} vs interaction mean square {ss_i / 9:.3f}); ACT city TL with fleet t' " + ' '.join(f'{x:.2f}' for x in act) +
                   f"; cells worse than ACT {int((CT > np.array([act] * 4)).sum())}/16")
    base = [c('RL-H:0', 'L-RLH:0', s) for s in SEEDS]
    out.append(f'[{tag}] L-RLH_0 (trained against RL-H_0): approach-cost change vs its deployed partner RL-H_0 — ' +
               ', '.join(f"{L} {np.mean([c(L, 'L-RLH:0', s) for s in SEEDS]) - np.mean(base):+.2f}" for L in ['ACT'] + [f'{f}:{t}' for f in ('RL-H', 'RL-C50', 'RL-J') for t in T]))
    out.append(f'[{tag}] L-RLH_0 vs L-ACT_0 under the same light (cost L-RLH_0 - L-ACT_0): ' +
               ', '.join(f"{L} {np.mean([c(L, 'L-RLH:0', s) - c(L, 'L-ACT:0', s) for s in SEEDS]):+.2f}" for L in ['ACT'] + [f'RL-H:{t}' for t in T]))
    cells = [(i, j) for i in T for j in T]
    h1 = [np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_a'] - R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_h'] for s in SEEDS]) for i, j in cells]
    hc1 = bool(np.mean(h1) > 0 and sum(x > 0 for x in h1) >= 14)
    out.append(f"[{tag}] HC-1 agent hidden-queue share > human: mean diff {np.mean(h1):+.4f}, positive cells {sum(x > 0 for x in h1)}/16 -> {'SUPPORTED' if hc1 else 'NOT SUPPORTED'}"
               f" (agent {np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_a'] for i, j in cells for s in SEEDS]):.3f}, human "
               f"{np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_h'] for i, j in cells for s in SEEDS]):.3f})")
    D = np.array([[c(f'RL-H:{i}', f'L-ACT:{j}', s, 'crawl') - c(f'RL-H:{i}', f'L-ACT:{j}', s) for s in SEEDS] for i, j in cells])
    rng = np.random.default_rng(0); bs = [D[rng.integers(0, 16, 16)][:, rng.integers(0, 5, 5)].mean() for _ in range(2000)]
    lo, hi = np.percentile(bs, [2.5, 97.5]); hc2 = bool(D.mean() < 0 and hi < 0)
    out.append(f"[{tag}] HC-2 crawl sensing lowers the fleet regression: mean r(crawl) - r(default) {D.mean():+.3f} [{lo:+.3f}, {hi:+.3f}]; cells lower {int((D.mean(1) < 0).sum())}/16 -> {'SUPPORTED' if hc2 else 'NOT SUPPORTED'}")
    h3 = [np.mean([tl(f'RL-H:{t}', 'human', s, 'crawl') - tl(f'RL-H:{t}', 'human', s) for s in SEEDS]) for t in T]
    hc3 = all(abs(x) <= 0.5 for x in h3)
    out.append(f"[{tag}] HC-3 crawl sensing near-identity for humans (|dTL| <= 0.5 s/veh every t): {[round(x, 3) for x in h3]} -> {'SUPPORTED' if hc3 else 'NOT SUPPORTED'}")
    h4 = np.array([[tl(f'RL-H:{i}', f'L-ACT:{j}', s, 'crawl') - tl(f'RL-H:{i}', f'L-ACT:{j}', s) for s in SEEDS] for i, j in cells])
    out.append(f"[{tag}] HC-4 (reported) city time loss with the fleet, crawl - default: {h4.mean():+.3f} s/veh (cells lower {int((h4.mean(1) < 0).sum())}/16); "
               f"L-RLH_0 under RL-H_t crawl - default (cost): {[round(np.mean([c(f'RL-H:{t}', 'L-RLH:0', s, 'crawl') - c(f'RL-H:{t}', 'L-RLH:0', s) for s in SEEDS]), 3) for t in T]}")
    tau = np.array([[np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['tau_oos_mass'] for s in SEEDS]) for j in T] for i in T])
    M = np.array(res['RL-H']['M']); rk = lambda z: np.argsort(np.argsort(z.ravel())).astype(float)
    out.append(f"   [{tag}] (descriptive) Spearman over the 16 RL-H cells: r vs fleet tau-OOS {np.corrcoef(rk(M), rk(tau))[0, 1]:+.2f}; "
               f"r vs agent-minus-human hidden share {np.corrcoef(rk(M), rk(np.array(h1).reshape(4, 4)))[0, 1]:+.2f}")
    res['verdicts'] = dict(HC1=hc1, HC2=hc2, HC3=hc3); res['HC2_ci'] = [float(D.mean()), float(lo), float(hi)]; res['HC1_diff'] = float(np.mean(h1)); res['HC3'] = h3
    return res


def main():
    R0 = load(H0); out = [f'== B1 / B1b cross-play, Addendum A1 (h0 panel {len(R0)} runs; original panel {len(load(ORIG))} runs)']
    reps = [load(JIT / f'h{k}') for k in (1, 2, 3, 4)]
    ok, J = parity(R0, reps, out)
    if not ok:
        (H0 / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    a = analyse(R0, out, 'h0'); b = analyse(load(ORIG), out, 'orig')
    out.append('Robustness (A1.4): ' + ', '.join(f"{k} {'same' if a['verdicts'][k] == b['verdicts'][k] else 'JITTER-SENSITIVE'}" for k in a['verdicts']))
    txt = '\n'.join(out) + '\n'; (H0 / 'report.txt').write_text(txt); (H0 / 'report.json').write_text(json.dumps(dict(h0=a, orig=b, J=J), indent=1, default=float)); print(txt)


if __name__ == '__main__':
    main()
