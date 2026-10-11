#!/usr/bin/env python3
"""Report of B1 / B1b (research/city_sim/PROTOCOL_CITY_XPLAY_HCRAWL_20261004.md; written 04/10/2026 02:4x EDT while the panel ran,
before any of its rows was read).  SELF-CHECK: parity with every Q7b stored row (same t, default sensing).  B1 exploratory: the
4 x 4 regression matrices (RL-H, RL-C50, RL-J x L-ACT), variance shares (light / fleet / interaction), the L-RLH_0 column.  B1b:
HC-1 (agent hidden-queue share > human, >= 14/16 cells), HC-2 (crawl sensing lowers r: two-level bootstrap upper < 0), HC-3
(|TL change| <= 0.5 s/veh for human traffic, every t), HC-4 reported."""
import json
from collections import defaultdict
from pathlib import Path
import numpy as np

O = Path('research/city_sim/xplay_20261004'); Q7B = Path('research/city_sim/q7b_contract_20261002'); SEEDS = [100, 101, 102, 103, 104]; T = [0, 1, 2, 3]


def main():
    R = {}
    for f in O.glob('*.json'):
        d = json.loads(f.read_text())
        if d.get('status') != 'COMPLETE':
            continue
        for r in d['rows']:
            R[(r['light'], r['fleet'], r['sense'], r['seed'])] = r
    out = [f'== B1 / B1b cross-play ({len(R)} runs)']
    # parity
    bad = []; n = 0
    for t in T:
        for q in json.loads((Q7B / f'eval_t{t}.json').read_text()):
            L = {'ACT': 'ACT', 'RL-H': f'RL-H:{t}', 'RL-C50': f'RL-C50:{t}', 'RL-J': f'RL-J:{t}'}.get(q['light']); F = {'human': 'human', 'L-ACT': f'L-ACT:{t}'}.get(q['fleet'])
            if L is None or F is None:
                continue
            k = (L, F, 'default', q['seed'])
            if k not in R:
                bad.append(('missing', k)); continue
            n += 1; r = R[k]
            if abs(r['timeloss'] - q['timeloss']) > 1e-9 or ('approach_cost' in q and abs(r['approach_cost'] - q['approach_cost']) > 1e-9):
                bad.append(('diff', k, r['timeloss'], q['timeloss']))
    out.append(f"SELF-CHECK parity with Q7b: {n - len([b for b in bad if b[0] == 'diff'])}/{n} rows identical; problems {bad[:3]} -> {'PASS' if not bad else 'FAIL'}")
    if bad:
        (O / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    c = lambda L, F, s, sense='default': R[(L, F, sense, s)]['approach_cost']
    tl = lambda L, F, s, sense='default': R[(L, F, sense, s)]['timeloss']
    res = {}
    for fam in ('RL-H', 'RL-C50', 'RL-J'):
        M = np.array([[np.mean([c(f'{fam}:{i}', f'L-ACT:{j}', s) - c('ACT', f'L-ACT:{j}', s) for s in SEEDS]) for j in T] for i in T])
        Ms = np.array([[[c(f'{fam}:{i}', f'L-ACT:{j}', s) - c('ACT', f'L-ACT:{j}', s) for s in SEEDS] for j in T] for i in T])
        g = M.mean(); row = M.mean(1) - g; col = M.mean(0) - g; inter = M - g - row[:, None] - col[None, :]
        ss_r, ss_c, ss_i = 4 * (row ** 2).sum(), 4 * (col ** 2).sum(), (inter ** 2).sum(); tot = ss_r + ss_c + ss_i
        noise = Ms.var(2, ddof=1).mean() / 5
        res[fam] = dict(M=M.tolist(), shares=dict(light=ss_r / tot, fleet=ss_c / tot, interaction=ss_i / tot), noise_var_of_cell_mean=float(noise))
        out.append(f"{fam} x L-ACT regression r (rows light t, cols fleet t'; diagonal = Q7b):")
        for i in T:
            out.append('   ' + ' '.join(f'{M[i, j]:+7.2f}' for j in T) + f"   | light gain (human) {np.mean([tl('ACT', 'human', s) - tl(f'{fam}:{i}', 'human', s) for s in SEEDS]):+.2f} s/veh")
        out.append(f"   variance shares of the 16 cell means: light {ss_r / tot:.2f}, fleet {ss_c / tot:.2f}, interaction {ss_i / tot:.2f} "
                   f"(cell-mean noise variance {noise:.3f} vs interaction mean square {ss_i / 9:.3f})")
        CT = np.array([[np.mean([tl(f'{fam}:{i}', f'L-ACT:{j}', s) for s in SEEDS]) for j in T] for i in T])
        out.append(f"   city time loss with the fleet (s/veh), mean {CT.mean():.2f} (ACT with the fleets: {np.mean([tl('ACT', f'L-ACT:{j}', s) for j in T for s in SEEDS]):.2f}); "
                   f"cells worse than ACT: {int((CT > np.array([[np.mean([tl('ACT', f'L-ACT:{j}', s) for s in SEEDS]) for j in T]] * 4)).sum())}/16")
    # L-RLH_0: the only fleet trained against a learned light; its deployed partner is RL-H_0
    base = [c('RL-H:0', 'L-RLH:0', s) for s in SEEDS]
    out.append('L-RLH_0 (trained against RL-H_0): approach-cost change vs its deployed partner RL-H_0 — ' +
               ', '.join(f"{L} {np.mean([c(L, 'L-RLH:0', s) for s in SEEDS]) - np.mean(base):+.2f}" for L in ['ACT'] + [f'{f}:{t}' for f in ('RL-H', 'RL-C50', 'RL-J') for t in T]))
    # B1b
    cells = [(i, j) for i in T for j in T]
    h1 = [np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_a'] - R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_h'] for s in SEEDS]) for i, j in cells]
    hc1 = np.mean(h1) > 0 and sum(x > 0 for x in h1) >= 14
    out.append(f"HC-1 agent hidden-queue share > human: mean diff {np.mean(h1):+.4f}, positive cells {sum(x > 0 for x in h1)}/16 -> {'SUPPORTED' if hc1 else 'NOT SUPPORTED'}"
               f" (agent {np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_a'] for i, j in cells for s in SEEDS]):.3f}, human "
               f"{np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['hidden_h'] for i, j in cells for s in SEEDS]):.3f})")
    D = np.array([[c(f'RL-H:{i}', f'L-ACT:{j}', s, 'crawl') - c(f'RL-H:{i}', f'L-ACT:{j}', s) for s in SEEDS] for i, j in cells])  # (16, 5)
    rng = np.random.default_rng(0); bs = [D[rng.integers(0, 16, 16)][:, rng.integers(0, 5, 5)].mean() for _ in range(2000)]
    lo, hi = np.percentile(bs, [2.5, 97.5]); hc2 = D.mean() < 0 and hi < 0
    out.append(f"HC-2 crawl sensing lowers the fleet regression: mean r(crawl) - r(default) {D.mean():+.3f} [{lo:+.3f}, {hi:+.3f}]; cells lower {int((D.mean(1) < 0).sum())}/16 -> {'SUPPORTED' if hc2 else 'NOT SUPPORTED'}")
    h3 = [np.mean([tl(f'RL-H:{t}', 'human', s, 'crawl') - tl(f'RL-H:{t}', 'human', s) for s in SEEDS]) for t in T]
    out.append(f"HC-3 crawl sensing near-identity for humans (|dTL| <= 0.5 s/veh every t): {[round(x, 3) for x in h3]} -> {'SUPPORTED' if all(abs(x) <= 0.5 for x in h3) else 'NOT SUPPORTED'}")
    h4 = np.array([[tl(f'RL-H:{i}', f'L-ACT:{j}', s, 'crawl') - tl(f'RL-H:{i}', f'L-ACT:{j}', s) for s in SEEDS] for i, j in cells])
    out.append(f"HC-4 (reported) city time loss with the fleet, crawl - default: {h4.mean():+.3f} s/veh (cells lower {int((h4.mean(1) < 0).sum())}/16); "
               f"L-RLH_0 under RL-H_t crawl - default: {[round(np.mean([c(f'RL-H:{t}', 'L-RLH:0', s, 'crawl') - c(f'RL-H:{t}', 'L-RLH:0', s) for s in SEEDS]), 3) for t in T]}")
    tau = np.array([[np.mean([R[(f'RL-H:{i}', f'L-ACT:{j}', 'default', s)]['tau_oos_mass'] for s in SEEDS]) for j in T] for i in T])
    M = np.array(res['RL-H']['M']); rk = lambda z: np.argsort(np.argsort(z.ravel())).astype(float)
    out.append(f"   (descriptive) Spearman over the 16 RL-H cells: r vs fleet tau-OOS {np.corrcoef(rk(M), rk(tau))[0, 1]:+.2f}; "
               f"r vs agent hidden share {np.corrcoef(rk(M), rk(np.array(h1).reshape(4, 4)))[0, 1]:+.2f}")
    txt = '\n'.join(out) + '\n'; (O / 'report.txt').write_text(txt); (O / 'report.json').write_text(json.dumps(res, indent=1)); print(txt)


if __name__ == '__main__':
    main()
