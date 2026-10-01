#!/usr/bin/env python3
"""Read the v7 learnability jobs (read-only; auditor's test 2).  Per actor and TRAINED target (g1 / delayed / g3): the
DEV tie-half pair accuracy against every target (per state, averaged over the 3 inits), traffic-seed cluster bootstrap;
the TRAIN and SELECT pair accuracy on the own target at the chosen epoch; across actors (the replication unit) the
two-level bootstrap and the number of actors whose CI excludes 0.5.  Refuses an actor with a missing job.
Usage: MARL_e3_v7_learnability_report.py --actor DIR... --out X.json
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_panel_report import boot_cluster, boot_two_level

TG = ('g1', 'delayed', 'g3')


def main(a):
    out = dict(actors={}, across={}); lines = []; across = {(t, e): [] for t in TG for e in TG}
    for A in map(Path, a.actor):
        res = {}
        for t in TG:
            J = [json.loads((A / 'selectors_v7' / f'job_legal_bid_resp_{t}_s{s}.json').read_text()) for s in (0, 1, 2)]
            seeds = J[0]['dev_traffic_seeds']
            if any(j['dev_traffic_seeds'] != seeds or j['target'] != t for j in J):
                raise SystemExit(f'SELF-CHECK FAIL: {A} {t}: jobs disagree on DEV states or target')
            ep = [next(c for c in j['curve'] if c['epoch'] == j['best_epoch']) for j in J]
            r = dict(train_pa=float(np.mean([c['train_pa'] for c in ep])), select_pa=float(np.mean([c['select_pa'] for c in ep])))
            for e in TG:
                v = np.nanmean(np.array([j['dev_pa'][e] for j in J], float), 0); cl = {}
                for s, x in zip(seeds, v):
                    if not np.isnan(x):
                        cl.setdefault(s, []).append(x)
                cl = {s: np.array(x) for s, x in cl.items()}; across[(t, e)].append(cl)
                r[f'dev_pa_{e}'] = dict(mean=float(np.nanmean(v)), ci=boot_cluster(cl))
            res[t] = r
            lines.append(f"{A.parent.name}/{A.name} trained on {t:7s}: train {r['train_pa']:.3f} select {r['select_pa']:.3f} | DEV " +
                         ' '.join(f"vs {e} {r[f'dev_pa_{e}']['mean']:.3f} [{r[f'dev_pa_{e}']['ci'][0]:.3f},{r[f'dev_pa_{e}']['ci'][1]:.3f}]" for e in TG))
        out['actors'][str(A)] = res
    for (t, e), L in across.items():
        ci = boot_two_level(L); m = float(np.mean([np.mean(np.concatenate(list(c.values()))) for c in L]))
        above = sum(out['actors'][str(A)][t][f'dev_pa_{e}']['ci'][0] > 0.5 for A in a.actor)
        out['across'][f'{t}->{e}'] = dict(mean=m, ci=ci, actors_ci_above_half=above, actors=len(L))
        if t == e:
            lines.append(f"ACROSS {len(L)} actors trained on {t:7s}, DEV vs own target: {m:.3f} [{ci[0]:.3f},{ci[1]:.3f}] | actors with CI > 0.5: {above}/{len(L)}")
    Path(a.out).write_text(json.dumps(out, indent=1)); print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--actor', nargs='+', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
