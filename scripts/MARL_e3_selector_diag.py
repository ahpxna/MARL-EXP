#!/usr/bin/env python3
"""Why do the E3 selectors not help?  Estimation error of the anchored critic against the gain scale (read-only).

For each trained selector (MARL_e3_selector_train_v2.py job/model) and its label splits: anchored predictions
a(S) = pred(S) - pred(P) on every feasible candidate of every SELECT and DEV state, against the true
continuation gain y(S) = cont(S) - cont(P).  Reported: quantiles of |a - y| (the empirical epsilon), Spearman
correlation within states, the oracle gain scale, the share of states whose best gain exceeds 2*eps_q, and the
realised dev gain of the SAFE rule 'edit only if a(S*) > 2*eps' with eps fixed on SELECT (theory: argmax stability,
LeanMarlEstimatedRevisionV1.deployed_regret / LeanMarlSafeEditV1).  Development diagnostic; no retraining.
"""
from __future__ import annotations
import argparse, glob, json, sys
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, featurize, Net
from models.marl_e3_response import resp_features, RespNet


def rank_corr(a, b):
    ra, rb = np.argsort(np.argsort(a)), np.argsort(np.argsort(b))
    return float(np.corrcoef(ra, rb)[0, 1]) if np.std(ra) > 0 and np.std(rb) > 0 else np.nan


def main(a):
    D = Path(a.actor_dir); out = {}
    data = {sp: load([x for x in sorted(glob.glob(str(D / pat))) if Path(x).is_dir()])[0]
            for sp, pat in (('select', 'labels_select'), ('dev', 'labels_dev'))}
    for mf in sorted(glob.glob(str(D / a.selectors / 'model_*.pt'))):
        meta = torch.load(mf, weights_only=False); name = Path(mf).stem.replace('model_', '')
        net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval()
        hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        res = {}
        for sp, S in data.items():
            err, corr, best, A, Y = [], [], [], [], []
            for st in S:
                c, d, y, feas, _ = featurize(st, meta['bid'], meta['gap_thr'])
                if hn is not None:
                    X = resp_features(st, meta['bid'], meta['gap_thr'])
                    with torch.no_grad():
                        pr = torch.sigmoid(hn(torch.as_tensor((X - meta['head']['mu']) / meta['head']['sd']))).numpy()
                    d = np.concatenate([d, pr, pr.sum(1, keepdims=True)], 1).astype(np.float32)
                with torch.no_grad():
                    p = net(torch.as_tensor((c - meta['cm']) / meta['cs'])[None], torch.as_tensor(d)).numpy() * meta['ys']
                an = p - p[0]; m = feas.copy(); m[0] = True
                err += list(np.abs(an[m][1:] - y[m][1:])); corr.append(rank_corr(an[m], y[m])); best.append(float(y[m].max()))
                A.append(an[m]); Y.append(y[m])
            res[sp] = dict(eps_q50=float(np.quantile(err, .5)), eps_q90=float(np.quantile(err, .9)), eps_q99=float(np.quantile(err, .99)),
                           spearman_within_state=float(np.nanmean(corr)), best_gain_mean=float(np.mean(best)), _A=A, _Y=Y)
        eps = res['select']['eps_q90']
        safe = []
        for an, y in zip(res['dev']['_A'], res['dev']['_Y']):
            j = int(np.argmax(an)); safe.append(float(y[j]) if an[j] > 2 * eps else 0.0)
        for sp in res:
            res[sp].pop('_A'); res[sp].pop('_Y')
        res['safe_rule'] = dict(eps_select_q90=eps, dev_gain=float(np.mean(safe)), dev_edit_rate=float(np.mean([x != 0 for x in safe])),
                                share_dev_states_best_gain_above_2eps=None)
        out[name] = res
        print(f"{name:18s} eps(sel) q50 {res['select']['eps_q50']:.1f} q90 {eps:.1f} | dev best gain {res['dev']['best_gain_mean']:.1f} | "
              f"spearman {res['dev']['spearman_within_state']:+.3f} | safe rule (a>2eps) dev gain {res['safe_rule']['dev_gain']:+.2f} edit {res['safe_rule']['dev_edit_rate']:.2f}", flush=True)
    Path(a.out).write_text(json.dumps(out, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--selectors', default='selectors_v2'); p.add_argument('--out', required=True)
    main(p.parse_args())
