#!/usr/bin/env python3
"""Selector diagnostic v3 (independent recheck 18:50; v2 and its JSON outputs are kept).

v2's pair_order_accuracy counted a predicted tie as WRONG (strict), so it cannot be compared with 0.5.  v3 is v2
with ONE change to that metric, tie-half credit:
    pair_order_accuracy = P(pred_diff > 0 | true_diff > 0) + 0.5 * P(pred_diff == 0 | true_diff > 0)
and it also reports the predicted-tie fraction and v2's strict value, for reference.  Everything else (the choice,
realised gain, edit and harmful-edit rates, tie-aware Spearman, gain-error quantiles) is v2's code path, unchanged.
Self-test: an all-tie predictor scores 0.5, a perfect one 1, a reversed one 0.
"""
from __future__ import annotations
import argparse, glob, gzip, json, sys
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_selector_diag_v2 as v2
from scripts.MARL_e3_selector_train import load, Net
from scripts.MARL_e3_ranking_diag_v2 import pair_acc, selftest
from models.marl_e3_response import RespNet


def assess_v3(S, meta, net, hn, pol):
    base = v2.assess(S, meta, net, hn, pol)                    # v2 path: choice, gains, edit/harm, Spearman, errors
    tau = meta['tau'][pol]; acc, strict, ties = [], [], []
    for st in S:
        an, y, feas, r1 = v2.predictions(meta, net, hn, st)
        allow = r1 if pol == 'R1' else np.ones_like(r1); ok = feas & allow; ok[0] = True
        a_, y_ = an[ok], y[ok]; t, tf, n = pair_acc(a_, y_)
        if n:
            acc.append(t); ties.append(tf); strict.append(t - 0.5 * tf)
    base.update(pair_order_accuracy=float(np.mean(acc)), pair_order_accuracy_strict_v2=float(np.mean(strict)), predicted_tie_fraction=float(np.mean(ties)),
                metric='tie-half pair accuracy (v3)')
    return base


def main(a):
    selftest(); D = Path(a.actor_dir); out = {}
    data = {sp: load([x for x in sorted(glob.glob(str(D / pat))) if Path(x).is_dir()])[0] for sp, pat in (('select', 'labels_select'), ('dev', 'labels_dev'))}
    for sp, pat in (('select', 'labels_select'), ('dev', 'labels_dev')):
        qd = D / f'qbid_{pat}'
        if (qd / 'manifest.json').exists():
            Q = {(r['episode_id'], r['t']): r['qbid'] for r in map(json.loads, gzip.open(qd / 'qbid.jsonl.gz', 'rt'))}
            for st in data[sp]:
                st['qbid'] = Q.get((st['episode_id'], st['t']))
    for mf in sorted(glob.glob(str(D / a.selectors / 'model_*.pt'))):
        meta = torch.load(mf, weights_only=False); name = Path(mf).stem.replace('model_', '')
        net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        out[name] = {pol: {sp: assess_v3(S, meta, net, hn, pol) for sp, S in data.items()} for pol in ('direct', 'R1')}
        r = out[name]['direct']['dev']
        print(f"{name:22s} dev: gain {r['realised_gain']:+.2f} {r['realised_gain_ci']} | pair-acc (tie-half) {r['pair_order_accuracy']:.3f} "
              f"(strict v2 {r['pair_order_accuracy_strict_v2']:.3f}, ties {r['predicted_tie_fraction']:.3f}) | spearman {r['spearman_ties']:+.3f}", flush=True)
    Path(a.out).write_text(json.dumps(out, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--selectors', default='selectors_v2'); p.add_argument('--out', required=True)
    main(p.parse_args())
