#!/usr/bin/env python3
"""Fig 3 v4: closed-loop quality at ONE operating point against total accounted bytes (read-only).

Changes from v3 (readiness audit, "Figure 3 đã được nhìn trực tiếp"): short legend names explained
in the caption; legend outside the data area; run directory, hardware and latency notes moved to a
caption file; "lower is better" and "one operating point" stated; the two-point latency panel is
replaced by a latency table in the caption file.  v3 and its figures are unchanged.

Input: a main closed-loop run dir, optional extra run dirs given as PATH=TAG (their non-prefix
methods are added as TAG/method; their prefix rows must reproduce the main run's), optional
methods to drop, optional latency JSONs.  Per method: init seeds averaged per episode; paired
relative change of sum-of-waiting against the prefix on the same episode, 95% bootstrap CI over
episodes; mean total accounted bytes per decision step (bids included).
Self-checks (refuse to plot): every deployable row has zero oracle access; every method covers the
prefix episodes; every extra run's prefix reproduces the main run's prefix.
Writes <stem>.png, <stem>.json (numbers, rows sha256) and <stem>.caption.txt.
"""
from __future__ import annotations
import argparse, hashlib, json
from collections import defaultdict
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

N_DEC = 26
SHORT = {'prefix': 'Prefix', 'ctrl_history': 'Direct', 'mlp_top2_joint': 'Response-bid',
         'schednet_fresh': 'Fresh-queue', 'where2comm_top2_bin': 'Request', 'where2comm_top2': 'Request (v3, leaky)',
         'oracle_heldphase': 'Oracle'}
EXPLAIN = {'Prefix': 'cached-queue priority, R = 0 (committed order)',
           'Direct': 'learned direct budget-conditioned selector, no bid',
           'Response-bid': 'learned direct selector + 1 B receiver bid (top-2 MP2 phases, gap bin) with a stage-A response model',
           'Fresh-queue': 'HEURISTIC, 1 B fresh own-queue weight per sender orders the stream (not learned SchedNet)',
           'Request': 'HEURISTIC request rule on the same 1 B bid (not learned; not Where2comm)',
           'Oracle': 'held-phase oracle choice over the same candidates (reference, not deployable)'}
LAT_KEY = {'prefix': 'prefix_post', 'mlp_top2_joint': 'scheduler_post'}


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])


def main(a):
    run = Path(a.run); raw = (run / 'rows.json').read_bytes(); rows = json.loads(raw)
    for r in rows:
        r['_m'] = r['method'].split('/')[0]
    prefix = {r['episode']: r for r in rows if r['_m'] == 'prefix'}
    extra_sha = {}
    for spec in a.extra or []:
        path, _, tag = spec.partition('=')
        xb = (Path(path) / 'rows.json').read_bytes(); xr = json.loads(xb); extra_sha[path] = hashlib.sha256(xb).hexdigest()
        for r in xr:
            if r['method'] == 'prefix':
                q = prefix.get(r['episode'])
                if q is None or any(q[k] != r[k] for k in ('queue_sum', 'finished', 'bytes')):
                    raise SystemExit(f'SELF-CHECK FAIL: prefix of {path} does not reproduce {run} on {r["episode"]}')
            else:
                b = r['method'].split('/')[0]; r['_m'] = f'{tag}/{b}' if tag else b; rows.append(r)
    drop = set(a.drop or [])
    per = defaultdict(lambda: defaultdict(list))
    for r in rows:
        if r['_m'] in drop:
            continue
        if not r['method'].startswith('oracle') and r['summary'].get('oracle_access_used'):
            raise SystemExit(f'SELF-CHECK FAIL: deployable {r["method"]} used oracle access in {r["episode"]}')
        per[r['_m']][r['episode']].append(r)
    eps = sorted(per['prefix'])
    for m, d in per.items():
        if sorted(d) != eps:
            raise SystemExit(f'SELF-CHECK FAIL: {m} does not cover the prefix episodes')
    pq = {e: per['prefix'][e][0]['queue_sum'] for e in eps}
    out = {}
    for m, d in per.items():
        rel = [100 * (np.mean([r['queue_sum'] for r in d[e]]) - pq[e]) / pq[e] for e in eps]
        lo, hi = boot(rel)
        out[m] = dict(rel_waiting_pct=float(np.mean(rel)), ci95=[float(lo), float(hi)],
                      bytes_per_step=float(np.mean([np.mean([r['bytes'] for r in d[e]]) for e in eps]) / N_DEC),
                      edits_per_episode=float(np.mean([r['edits'] for e in eps for r in d[e]])),
                      better_episodes=int(sum(x < 0 for x in rel)), n_episodes=len(eps), init_seeds=len(d[eps[0]]))
    label = {m: (f'{m.split("/")[0]}: ' if '/' in m else '') + SHORT.get(m.split('/')[-1], m) for m in out}
    fig, ax = plt.subplots(figsize=(8.2, 4.2))
    names = sorted(out, key=lambda m: out[m]['bytes_per_step'])
    cols = plt.rcParams['axes.prop_cycle'].by_key()['color']
    for i, m in enumerate(names):
        o = out[m]; y = o['rel_waiting_pct']; hollow = m.startswith('oracle')
        ax.errorbar(o['bytes_per_step'], y, yerr=[[y - o['ci95'][0]], [o['ci95'][1] - y]], fmt='o', ms=7, capsize=3,
                    color=cols[i % len(cols)], mfc='white' if hollow else cols[i % len(cols)], label=label[m])
    ax.axhline(0, color='gray', lw=0.8)
    ax.set_xlabel('total accounted bytes per decision step (payload + control + bid)', fontsize=10)
    ax.set_ylabel('Σ waiting vs Prefix, same episode (%)\nlower is better', fontsize=10)
    ax.set_title(f'{a.title} — one operating point, mean ± 95% CI over {len(eps)} episodes', fontsize=10)
    ax.legend(fontsize=9, loc='upper left', bbox_to_anchor=(1.02, 1.0), frameon=False)
    fig.tight_layout()
    od = Path(a.out); od.mkdir(parents=True, exist_ok=True); stem = a.stem or f'fig3v4_{run.name}'
    fig.savefig(od / f'{stem}.png', dpi=200, bbox_inches='tight'); fig.savefig(od / f'{stem}.pdf', bbox_inches='tight'); plt.close(fig)
    lat = {}
    for f in a.latency or []:
        L = json.loads(Path(f).read_text())
        for m, k in LAT_KEY.items():
            if k in L:
                lat[SHORT[m]] = dict(median_ms=L[k]['median'], p95_ms=L[k]['p95'], max_ms=L[k]['max'], source=f, note=L.get('note', ''))
    cap = [f'Figure 3. {a.title}. Closed loop on {len(eps)} episodes ({run.name}); frozen MP2 actor on every method; '
           f'3x3 CityFlow; one broadcast with heterogeneous receiver decoding budgets (i.i.d.); cap +84 B over the prefix '
           f'bytes, bids charged inside the cap; zero delivery delay. One operating point, not a multi-budget frontier. '
           f'Lower is better. Hollow marker: reference, not deployable.']
    for m in names:
        s = label[m].split(': ')[-1]
        unit = 'receiver swaps/episode' if s.startswith('Request') else 'edited steps/episode (of 26)'
        cap.append(f'  {label[m]}: {EXPLAIN.get(s, s)}; {out[m]["edits_per_episode"]:.1f} {unit}, '
                   f'init seeds {out[m]["init_seeds"]}.')
    if lat:
        cap.append('Latency table (CPU compute only, post-grant scheduler; no uplink or network delay; measured on this host):')
        for k, v in lat.items():
            cap.append(f'  {k}: median {v["median_ms"]:.3f} ms, p95 {v["p95_ms"]:.3f} ms, max {v["max_ms"]:.3f} ms ({v["source"]})')
        if a.latency_note:
            cap.append('  ' + a.latency_note)
    (od / f'{stem}.caption.txt').write_text('\n'.join(cap) + '\n')
    (od / f'{stem}.json').write_text(json.dumps(dict(run=str(run), rows_sha256=hashlib.sha256(raw).hexdigest(),
        extra_runs_sha256=extra_sha, dropped=sorted(drop), methods=out, labels=label, latency=lat), indent=1))
    for m in names:
        o = out[m]
        print(f'{label[m]:28s} bytes/step {o["bytes_per_step"]:7.1f}  Σwait {o["rel_waiting_pct"]:+6.2f}% '
              f'[{o["ci95"][0]:+6.2f}, {o["ci95"][1]:+6.2f}]  better {o["better_episodes"]}/{o["n_episodes"]}  edits {o["edits_per_episode"]:.1f}')
    print('wrote', od / f'{stem}.png')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True); p.add_argument('--stem')
    p.add_argument('--title', default='Closed-loop comparison')
    p.add_argument('--extra', nargs='*', help='PATH=TAG run dirs whose non-prefix methods are added as TAG/method')
    p.add_argument('--drop', nargs='*'); p.add_argument('--latency', nargs='*'); p.add_argument('--latency-note', default='')
    main(p.parse_args())
