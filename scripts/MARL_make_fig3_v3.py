#!/usr/bin/env python3
"""Fig 3 v3: closed-loop quality against bytes and against measured post-grant latency (read-only).

Input: one closed-loop run dir (rows.json from MARL_hetero_closed_loop{,_v2,_v3}.py) and optional
latency JSONs (MARL_hetero_latency*.py).  Per method, the init seeds s0-s2 are averaged per
episode first (one value per episode), then:
  quality  paired relative change of sum-of-waiting against the prefix on the same episode (%),
           mean and 95% bootstrap CI over episodes (negative = better);
  bytes    mean accounted bytes per decision step, bids included (the rows' 'bytes' field).
Latency panel: median post-grant scheduler time with a p95 whisker, only for methods whose latency
was measured; the others are listed as not measured.  oracle_* rows are references (not
deployable) and are drawn hollow.  A numbers JSON with the sha256 of rows.json is written next to
the figure.  Self-check: every episode must have every plotted method, and every deployable row
must show zero oracle access; otherwise the script refuses to plot.
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
LAT_KEY = {'prefix': 'prefix_post', 'mlp_top2_joint': 'scheduler_post'}
LABEL = {'prefix': 'prefix (cached-queue priority, R = 0)',
         'ctrl_history': 'ctrl_history: direct selector, no bid (frozen B2 control)',
         'mlp_top2_joint': 'mlp_top2_joint: direct selector + 1 B bid (frozen B2 design)',
         'schednet_fresh': 'schednet_fresh: HEURISTIC fresh-queue weight (not learned SchedNet)',
         'where2comm_top2_bin': 'where2comm_top2_bin: HEURISTIC request rule on the 1 B bid (not learned)',
         'where2comm_top2': 'where2comm_top2 (v3, LEAKS exact gap; superseded)',
         'oracle_heldphase': 'oracle_heldphase (reference, not deployable)'}


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])


def base(m):
    return m.split('/')[0]


def main(a):
    run = Path(a.run); raw = (run / 'rows.json').read_bytes(); rows = json.loads(raw)
    drop = set(a.drop or []); extra_sha = {}
    for x in a.extra or []:                         # extra run dir: its non-prefix methods are added
        xr = json.loads((Path(x) / 'rows.json').read_bytes()); extra_sha[x] = hashlib.sha256((Path(x) / 'rows.json').read_bytes()).hexdigest()
        mine = {r['episode']: r for r in rows if r['method'] == 'prefix'}
        for r in xr:
            if r['method'] == 'prefix':             # same episode must reproduce the same prefix run
                q = mine.get(r['episode'])
                if q is None or any(q[k] != r[k] for k in ('queue_sum', 'finished', 'bytes')):
                    raise SystemExit(f'SELF-CHECK FAIL: prefix of {x} does not reproduce {run} on {r["episode"]}')
        rows = rows + [r for r in xr if r['method'] != 'prefix']
    rows = [r for r in rows if base(r['method']) not in drop]
    per = defaultdict(lambda: defaultdict(list))
    for r in rows:
        if not r['method'].startswith('oracle') and r['summary'].get('oracle_access_used'):
            raise SystemExit(f'SELF-CHECK FAIL: deployable {r["method"]} used oracle access in {r["episode"]}')
        per[base(r['method'])][r['episode']].append(r)
    eps = sorted(per['prefix'])
    for m, d in per.items():
        if sorted(d) != eps:
            raise SystemExit(f'SELF-CHECK FAIL: {m} does not cover the prefix episodes')
    pq = {e: per['prefix'][e][0]['queue_sum'] for e in eps}
    out = {}
    for m, d in per.items():
        rel = [100 * (np.mean([r['queue_sum'] for r in d[e]]) - pq[e]) / pq[e] for e in eps]
        by = [np.mean([r['bytes'] for r in d[e]]) / N_DEC for e in eps]
        lo, hi = boot(rel)
        out[m] = dict(rel_waiting_pct=float(np.mean(rel)), ci95=[float(lo), float(hi)], bytes_per_step=float(np.mean(by)),
                      better_episodes=int(sum(x < 0 for x in rel)), n_episodes=len(eps), init_seeds=len(d[eps[0]]))
    lat = {}
    for f in a.latency or []:
        L = json.loads(Path(f).read_text())
        for m, k in LAT_KEY.items():
            if k in L:
                lat[m] = dict(median=L[k]['median'], p95=L[k]['p95'], source=f, note=L.get('note', ''))
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.4))
    names = sorted(out, key=lambda m: out[m]['bytes_per_step'])
    cols = plt.rcParams['axes.prop_cycle'].by_key()['color']
    for i, m in enumerate(names):
        o = out[m]; c = cols[i % len(cols)]; hollow = m.startswith('oracle')
        y = o['rel_waiting_pct']; err = [[y - o['ci95'][0]], [o['ci95'][1] - y]]
        kw = dict(fmt='o', color=c, ms=6, capsize=3, mfc='white' if hollow else c, label=LABEL.get(m, m))
        axes[0].errorbar(o['bytes_per_step'], y, yerr=err, **kw)
        if m in lat:
            L = lat[m]
            axes[1].errorbar(L['median'], y, yerr=err, xerr=[[0], [L['p95'] - L['median']]], **kw)
    for ax in axes:
        ax.axhline(0, color='gray', lw=0.8)
        ax.set_ylabel('Σ waiting vs prefix, same episode (%)')
    axes[0].set_xlabel('accounted bytes per decision step (bids included)')
    axes[0].set_title(f'{run.name}: {len(eps)} episodes, 95% episode bootstrap CI', fontsize=9)
    axes[0].legend(fontsize=6.5, loc='best')
    axes[1].set_xscale('log'); axes[1].set_xlabel('post-grant scheduler time, median (ms); whisker to p95')
    missing = [m for m in names if m not in lat]
    axes[1].set_title('latency measured for: ' + (', '.join(sorted(lat)) or 'none'), fontsize=9)
    notes = sorted({L['note'] for L in lat.values() if L['note']}) + ([a.latency_note] if a.latency_note else [])
    axes[1].text(0.02, 0.02, 'not measured: ' + ', '.join(missing) + ('\n' + '\n'.join(notes) if notes else ''),
                 transform=axes[1].transAxes, fontsize=6, va='bottom')
    fig.suptitle('Fig 3 v3 — closed loop, frozen MP2 actor, 3×3 CityFlow, PROTOCOL_HETERO_v0 (i.i.d. capacities)', fontsize=9)
    fig.tight_layout()
    od = Path(a.out); od.mkdir(parents=True, exist_ok=True)
    stem = f'fig3_closed_loop_{run.name}'
    fig.savefig(od / f'{stem}.png', dpi=160); plt.close(fig)
    (od / f'{stem}.json').write_text(json.dumps(dict(run=str(run), rows_sha256=hashlib.sha256(raw).hexdigest(),
        extra_runs_sha256=extra_sha, dropped=sorted(drop), methods=out, latency=lat, latency_not_measured=missing), indent=1))
    for m in names:
        o = out[m]
        print(f'{m:20s} bytes/step {o["bytes_per_step"]:7.1f}  Σwait {o["rel_waiting_pct"]:+6.2f}% '
              f'[{o["ci95"][0]:+6.2f}, {o["ci95"][1]:+6.2f}]  better {o["better_episodes"]}/{o["n_episodes"]}')
    print('wrote', od / f'{stem}.png')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True)
    p.add_argument('--latency', nargs='*')
    p.add_argument('--extra', nargs='*', help='run dirs whose non-prefix methods are added (prefix must reproduce)')
    p.add_argument('--drop', nargs='*', help='methods to leave out (e.g. a superseded leaky baseline)')
    p.add_argument('--latency-note', default='', help='caveat printed on the latency panel')
    main(p.parse_args())
