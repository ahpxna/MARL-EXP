#!/usr/bin/env python3
"""E13 (PROTOCOL_E3_E12_E14_G3_G6_20261004, frozen 01:21:14 EDT 04/10 before report_e7.txt was opened): per-agent outcomes in the
mixed fleet, from E7's stored rows only (w2/MIX_s{s}_{D,C}, w2/REF_s{s}).  Per-agent gain of arm A vs reference R, agent a, seed s:
g = -(sum_e q_a(A, e) / sum_e q_a(R, e) - 1) * 100, mean over seeds 0-9; two-level crossed bootstrap (seeds x panel episodes),
2000 draws, rng 0; Bonferroni within (layout, comparison, group) over the group's agents.
  E13-1 OLD, U2/EMU_OLD vs ALLOLD: # agents with upper < -0.5 (prediction 0 in D; SUPPORTED iff 0 in D)
  E13-2 OLD, U2/EMU_OLD vs U2/PLAIN: # agents with lower > 0 (prediction >= 6 of 8 in D)
  E13-3 NEW, U2/EMU_OLD vs U2/PLAIN: # agents with upper < -0.5 (prediction 0)
  E13-4 OLD vs K1/ROLLBACK, NEW vs U1/PLAIN: descriptive counts
The same for U2/EXACT_PROTO_OLD.  Descriptive: per-agent table (grid position, # NEW 4-neighbours), Spearman of OLD gain vs # NEW
neighbours.  INCOMPLETE if any cell is missing."""
import argparse, json
from pathlib import Path
import numpy as np

W = Path('research/marl_budget/e3_wave_20261003'); SEEDS = list(range(10)); R, C = 4, 4
EPS = [f'seed{t}_load{h}' for t in range(7501, 7565) for h in (8, 16)]
CMP = [('E13-1', 'OLD', 'ALLOLD', 'upper<-0.5'), ('E13-2', 'OLD', 'U2/PLAIN', 'lower>0'), ('E13-3', 'NEW', 'U2/PLAIN', 'upper<-0.5'),
       ('E13-4a', 'OLD', 'K1/ROLLBACK', 'both'), ('E13-4b', 'NEW', 'U1/PLAIN', 'both')]


def load(d):
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
    return json.loads((d / 'rows.json').read_text())


def spearman(x, y):
    rk = lambda z: np.argsort(np.argsort(z, kind='stable'), kind='stable').astype(float)
    x, y = np.asarray(x, float), np.asarray(y, float)
    return float(np.corrcoef(rk(x), rk(y))[0, 1]) if len(x) > 2 and np.std(x) > 0 and np.std(y) > 0 else float('nan')


def main(a):
    out = []; miss = []; res = {}
    for lay in ('D', 'C'):
        Q = {}; old = None
        for s in SEEDS:
            mix, ref = load(W / 'w2' / f'MIX_s{s}_{lay}'), load(W / 'w2' / f'REF_s{s}')
            if mix is None or ref is None:
                miss.append((lay, s)); continue
            for rows in (mix, ref):
                for x in rows:
                    Q.setdefault(x['arm'], {}).setdefault(s, {})[x['episode']] = np.asarray(x['q_agents'], float)
            o = mix[0]['old']; assert old is None or o == old; old = o
        if miss:
            continue
        arr = {arm: np.stack([np.stack([v[s][e] for e in EPS]) for s in SEEDS]) for arm, v in Q.items()}   # (S, E, 16)
        new = [k for k in range(R * C) if k not in old]
        nnew = {k: sum(1 for d in ((-1, 0), (1, 0), (0, -1), (0, 1)) if 0 <= k // C + d[0] < R and 0 <= k % C + d[1] < C
                       and (k // C + d[0]) * C + k % C + d[1] in new) for k in range(R * C)}
        rng = np.random.default_rng(0); B = 2000; S, E = len(SEEDS), len(EPS)
        draws = [(rng.integers(0, S, S), rng.integers(0, E, E)) for _ in range(B)]
        res[lay] = {}
        for arm in ('U2/EMU_OLD', 'U2/EXACT_PROTO_OLD'):
            for tag, grp, refarm, rule in CMP:
                ag = old if grp == 'OLD' else new; A_, Rf = arr[arm][:, :, ag], arr[refarm][:, :, ag]
                g = lambda si, ei: (-(A_[si][:, ei].sum(1) / Rf[si][:, ei].sum(1) - 1) * 100).mean(0)
                pt = g(np.arange(S), np.arange(E)); bs = np.stack([g(si, ei) for si, ei in draws])
                lo, hi = np.percentile(bs, 100 * 0.025 / len(ag), 0), np.percentile(bs, 100 * (1 - 0.025 / len(ag)), 0)
                n_bad, n_good = int((hi < -0.5).sum()), int((lo > 0).sum())
                res[lay][f'{arm}|{tag}'] = dict(agents=ag, gain=pt.tolist(), lo=lo.tolist(), hi=hi.tolist(), n_worse=n_bad, n_better=n_good,
                                                n_new_nb=[nnew[k] for k in ag])
                if arm == 'U2/EMU_OLD' or tag in ('E13-1', 'E13-3'):
                    verdict = ''
                    if tag == 'E13-1' and lay == 'D':
                        verdict = f" -> {'SUPPORTED' if n_bad == 0 else 'NOT SUPPORTED'} (prediction 0)"
                    elif tag == 'E13-2' and lay == 'D':
                        verdict = f" -> prediction >= 6: {'met' if n_good >= 6 else 'not met'}"
                    elif tag == 'E13-3' and lay == 'D':
                        verdict = f" -> prediction 0: {'met' if n_bad == 0 else 'not met'}"
                    out.append(f'[{lay}] {tag} {grp} {arm} vs {refarm}: worse (upper < -0.5) {n_bad}/{len(ag)}, better (lower > 0) {n_good}/{len(ag)}{verdict}')
            r1 = res[lay][f'{arm}|E13-1']
            if arm == 'U2/EMU_OLD':
                out.append(f"[{lay}]   per OLD agent vs ALLOLD (agent: gain [Bonferroni CI], # NEW neighbours): " +
                           '; '.join(f"{k}: {g_:+.2f} [{l_:+.2f}, {h_:+.2f}] n{nnew[k]}" for k, g_, l_, h_ in zip(r1['agents'], r1['gain'], r1['lo'], r1['hi'])))
                r2 = res[lay][f'{arm}|E13-2']
                out.append(f"[{lay}]   per OLD agent vs U2/PLAIN: " + '; '.join(f"{k}: {g_:+.2f} [{l_:+.2f}, {h_:+.2f}]" for k, g_, l_, h_ in zip(r2['agents'], r2['gain'], r2['lo'], r2['hi'])))
                r3 = res[lay][f'{arm}|E13-3']
                out.append(f"[{lay}]   per NEW agent vs U2/PLAIN: " + '; '.join(f"{k}: {g_:+.2f} [{l_:+.2f}, {h_:+.2f}]" for k, g_, l_, h_ in zip(r3['agents'], r3['gain'], r3['lo'], r3['hi'])))
                out.append(f"[{lay}]   Spearman(OLD gain vs ALLOLD, # NEW neighbours) {spearman(r1['gain'], r1['n_new_nb']):+.2f} (descriptive)")
    if miss:
        out = [f'INCOMPLETE: missing {miss}']
    txt = '== E13 per-agent outcomes (E7 rows; seeds 0-9; panel 7501-7564 x 8/16)\n' + '\n'.join(out) + '\n'
    (W / 'w2' / 'report_e13.txt').write_text(txt); (W / 'w2' / 'report_e13.json').write_text(json.dumps(res)); print(txt)


if __name__ == '__main__':
    main(argparse.ArgumentParser(description=__doc__).parse_args())
