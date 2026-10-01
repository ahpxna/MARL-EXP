#!/usr/bin/env python3
"""Read MARL_e3_edit_ttl_probe.py outputs (read-only).  Per actor and revert horizon L: the full-episode gain vs the
prefix of the stored oracle-best candidate and of the random feasible candidates, WITHOUT the revert (the label horizon
probe's rows) and WITH it, paired per state; how many off-schedule entries were reverted (not refreshed by the prefix in
between).  Traffic-seed cluster bootstrap of the paired difference.  Refuses an incomplete directory.
Usage: MARL_e3_edit_ttl_report.py DIR... --out X.json
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_panel_report import boot_cluster


def main(a):
    out = {}; lines = []
    for D in map(Path, a.dirs):
        man = json.loads((D / 'manifest.json').read_text())
        if man.get('status') != 'COMPLETE' or man.get('self_check') != 'PASS':
            raise SystemExit(f'refusing: {D} not COMPLETE/PASS')
        R = json.loads((D / 'rows.json').read_text()); res = {}
        for L in man['args']['ttls']:
            per = []
            for r in R:
                Q0 = np.array(r['no_revert_queues']); QL = np.array(r['ttl'][str(L)]['queues']); P = r['prefix_episode_queue_sum']
                g0 = -(Q0.sum(1) - Q0[0].sum()); gL = -(QL.sum(1) - QL[0].sum()); v = r['ttl'][str(L)]
                per.append(dict(seed=int(re.match(r'seed(\d+)_', r['episode']).group(1)), best0=100 * g0[1] / P, bestL=100 * gL[1] / P,
                                rnd0=100 * g0[2:].mean() / P, rndL=100 * gL[2:].mean() / P,
                                rev_share=sum(v['reverted'][1:]) / max(1, sum(v['added'][1:]))))
            def ci(k):
                cl = {}
                for p in per:
                    cl.setdefault(p['seed'], []).append(p[k] if not isinstance(k, tuple) else p[k[0]] - p[k[1]])
                return boot_cluster({s: np.array(x) for s, x in cl.items()})
            m = lambda k: float(np.mean([p[k] for p in per]))
            res[str(L)] = dict(best_no_revert=m('best0'), best_revert=m('bestL'), best_diff_ci=ci(('bestL', 'best0')),
                               random_no_revert=m('rnd0'), random_revert=m('rndL'), random_diff_ci=ci(('rndL', 'rnd0')),
                               reverted_share=m('rev_share'), states=len(per))
            x = res[str(L)]
            lines.append(f"{D.name} L={L}: oracle-best {x['best_no_revert']:+.2f}% -> {x['best_revert']:+.2f}% (diff CI [{x['best_diff_ci'][0]:+.2f},{x['best_diff_ci'][1]:+.2f}]) | "
                         f"random {x['random_no_revert']:+.2f}% -> {x['random_revert']:+.2f}% (diff CI [{x['random_diff_ci'][0]:+.2f},{x['random_diff_ci'][1]:+.2f}]) | "
                         f"entries reverted {x['reverted_share']:.2f} | states {x['states']}")
        out[str(D)] = res
    Path(a.out).write_text(json.dumps(out, indent=1)); print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('dirs', nargs='+'); p.add_argument('--out', required=True)
    main(p.parse_args())
