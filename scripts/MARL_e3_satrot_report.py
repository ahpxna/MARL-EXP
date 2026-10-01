#!/usr/bin/env python3
"""Report for the saturated-age relay grid (30/09 14:4x EDT; ledger L-173).  Development panel 901-964 x 8/16.

Input: research/marl_budget/e3_satrot_eval_20260930/<actor>_<order>_<cap>/rows.json, written by
scripts/MARL_e3_delivery_eval_relay_satrot.py (the 25 B relay layout of L-165, cap-correct orders, AgeMirror self-check).
Conditions per actor: order in {prefix, agefirst} x {iid: rules prefix and cap4; low: rule prefix}.
Every comparison is PAIRED per episode: the ratio of summed waiting minus 1, with a 95 % bootstrap over traffic seeds (both
headways of a seed resampled together, 4000 draws, rng seed 0) — the method of scripts/MARL_e3_music_report.py.
Per actor and seed:
  * every condition vs the same-seed 0-byte distilled student (distill_none_s<s>, rule none);
  * agefirst - prefix order under each capacity condition;
  * for relay_st_s<s> only: SATURATED - EXACT ages, against the exact-age rows of the same actor and condition
    (research/marl_budget/e3_codesign_eval_20260929/relay_st_s<s>_eval, research/marl_budget/e3_music_eval_20260930/...).
Across seeds (actors with >= 3 seeds): a two-level bootstrap (training seeds, then traffic seeds), the method of
scripts/MARL_e3_ten_seed_synthesis.py.  Bytes per episode are reported for every condition.
No verdict is computed: the development panel has been used many times; a pre-registered new-panel test decides.
"""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
import numpy as np

R = Path('research/marl_budget/e3_satrot_eval_20260930'); C = Path('research/marl_budget/e3_codesign_eval_20260929')
MUS = Path('research/marl_budget/e3_music_eval_20260930')
CONDS = [('prefix', 'iid', 'prefix'), ('prefix', 'iid', 'cap4'), ('prefix', 'low', 'prefix'),
         ('agefirst', 'iid', 'prefix'), ('agefirst', 'iid', 'cap4'), ('agefirst', 'low', 'prefix')]


def rows(path, rule):
    p = Path(path)
    if not p.exists() or not (p.parent / 'manifest.json').exists():
        return None
    return {r['episode']: r for r in json.loads(p.read_text()) if r['rule'] == rule}


def exact_rows(s, order, cap, rule):
    if order == 'prefix' and cap == 'iid':
        return rows(C / f'relay_st_s{s}_eval/rows.json', rule) if (s == 0 or rule == 'prefix') else rows(MUS / f'relay_st_s{s}_prefix_cap4/rows.json', rule)
    return rows(MUS / f'relay_st_s{s}_{order}_{cap}/rows.json', rule)


def paired(A, B, draws=4000, seed=0):
    eps = sorted(set(A) & set(B)); assert len(eps) == 128, len(eps)
    seeds = sorted({e.split('_')[0] for e in eps}); by = {sd: [e for e in eps if e.startswith(sd + '_')] for sd in seeds}
    a = {e: A[e]['queue_sum'] for e in eps}; b = {e: B[e]['queue_sum'] for e in eps}
    est = sum(a.values()) / sum(b.values()) - 1; rng = np.random.default_rng(seed); bs = []
    for _ in range(draws):
        pick = rng.choice(seeds, len(seeds)); ee = [e for sd in pick for e in by[sd]]
        bs.append(sum(a[e] for e in ee) / sum(b[e] for e in ee) - 1)
    lo, hi = np.quantile(bs, [0.025, 0.975])
    return [round(100 * est, 2), round(100 * lo, 2), round(100 * hi, 2)]


def multi(pairs, draws=4000, seed=0):
    """pairs: {training seed: (A rows, B rows)}; mean over seeds of the per-seed ratio, two-level bootstrap."""
    S = sorted(pairs); eps = sorted(set.intersection(*[set(pairs[s][0]) & set(pairs[s][1]) for s in S]))
    ts = sorted({e.split('_')[0] for e in eps}); by = {t: [i for i, e in enumerate(eps) if e.startswith(t + '_')] for t in ts}
    A = {s: np.array([pairs[s][0][e]['queue_sum'] for e in eps]) for s in S}; B = {s: np.array([pairs[s][1][e]['queue_sum'] for e in eps]) for s in S}
    per = {s: float(A[s].sum() / B[s].sum() - 1) for s in S}; rng = np.random.default_rng(seed); bs = []
    for _ in range(draws):
        ss = rng.choice(S, len(S)); ii = np.concatenate([by[ts[p]] for p in rng.choice(len(ts), len(ts))])
        bs.append(np.mean([A[s][ii].sum() / B[s][ii].sum() - 1 for s in ss]))
    lo, hi = np.percentile(bs, [2.5, 97.5])
    return dict(seeds=S, per_seed={f's{s}': round(100 * v, 2) for s, v in per.items()}, mean=round(100 * float(np.mean(list(per.values()))), 2),
                ci=[round(100 * lo, 2), round(100 * hi, 2)], below0=int(sum(v < 0 for v in per.values())))


def main(a):
    rep = dict(producer='scripts/MARL_e3_satrot_report.py', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), actors={}, across_seeds={})
    lines = []; stu = {s: rows(C / f'distill_none_s{s}/rows.json', 'none') for s in range(10)}
    for fam in a.families:
        for s in range(10):
            actor = f'{fam}_s{s}'; G = {k: rows(R / f'{actor}_{k[0]}_{k[1]}/rows.json', k[2]) for k in CONDS}; G = {k: v for k, v in G.items() if v}
            if not G:
                continue
            rs = rep['actors'][actor] = dict(means={}, vs_student={}, agefirst_minus_prefix={}, saturated_minus_exact={})
            lines.append(f'== {actor}')
            for k, v in G.items():
                rs['means']['/'.join(k)] = dict(waiting=round(float(np.mean([r['queue_sum'] for r in v.values()])), 1),
                                                bytes_per_episode=round(float(np.mean([r['bytes'] for r in v.values()])), 1), n=len(v))
                if stu[s]:
                    rs['vs_student']['/'.join(k)] = paired(v, stu[s])
                if fam == 'relay_st':
                    ex = exact_rows(s, *k)
                    if ex:
                        rs['saturated_minus_exact']['/'.join(k)] = paired(v, ex)
            for cap, rule in (('iid', 'prefix'), ('iid', 'cap4'), ('low', 'prefix')):
                x, y = ('agefirst', cap, rule), ('prefix', cap, rule)
                if x in G and y in G:
                    rs['agefirst_minus_prefix'][f'{cap}/{rule}'] = paired(G[x], G[y])
            for k, m in rs['means'].items():
                vs = rs['vs_student'].get(k); se = rs['saturated_minus_exact'].get(k)
                lines.append(f'   {k:22s} waiting {m["waiting"]:7.1f}  B/ep {m["bytes_per_episode"]:7.1f}'
                             + (f'  vs student {vs[0]:+6.2f} [{vs[1]:+6.2f}, {vs[2]:+6.2f}]' if vs else '')
                             + (f'  sat-exact {se[0]:+6.2f} [{se[1]:+6.2f}, {se[2]:+6.2f}]' if se else ''))
            for k, (e, lo, hi) in rs['agefirst_minus_prefix'].items():
                lines.append(f'   agefirst - prefix order, {k:12s} {e:+6.2f} [{lo:+6.2f}, {hi:+6.2f}]')
        for k in CONDS:
            pairs = {}
            for s in range(10):
                v = rows(R / f'{fam}_s{s}_{k[0]}_{k[1]}/rows.json', k[2])
                if v and stu[s]:
                    pairs[s] = (v, stu[s])
            if len(pairs) >= 3:
                m = rep['across_seeds'][f'{fam}/{"/".join(k)} vs student'] = multi(pairs)
                lines.append(f'ACROSS SEEDS {fam} {"/".join(k):22s} vs student: mean {m["mean"]:+.2f} [{m["ci"][0]:+.2f}, {m["ci"][1]:+.2f}] '
                             f'below 0 {m["below0"]}/{len(m["seeds"])}  ' + ' '.join(f'{t}:{x:+.1f}' for t, x in m['per_seed'].items()))
    print('\n'.join(lines)); Path(a.out).write_text(json.dumps(rep, indent=1)); Path(a.out).with_suffix('.txt').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--families', nargs='+', default=['relay_st', 'relay6_st', 'relay6Cage_st', 'relay6B12_st'])
    p.add_argument('--out', required=True)
    main(p.parse_args())
