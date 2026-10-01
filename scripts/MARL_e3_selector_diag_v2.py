#!/usr/bin/env python3
"""Selector diagnostic v2 (28/09; corrects MARL_e3_selector_diag.py after the step-3 audit; read-only, no rollouts).

Fixes against v1:
  * rank correlation with TIES handled (average ranks, scipy.stats.spearmanr); about 96% of candidate values tie
    with another candidate in the same state, so v1's double-argsort ranks were not valid;
  * the chosen profile is recomputed from the checkpoint with its saved tau (None = -inf, the v2 trainer's grid has
    no +inf), and an EDIT is 'chosen index != prefix', not 'gain != 0';
  * reported: realised gain of the actual choice, edit rate, harmful-edit rate P(gain < 0 | edit), gain given an
    edit, top-1 regret, pairwise order accuracy on candidate pairs whose true gains differ;
  * the quantiles of |predicted gain - true gain| are a DIAGNOSTIC of the gain error, not a certified bound; they are
    not the per-value epsilon of LeanMarlSafeEditV1 (a per-value bound eps implies a gain-error bound 2*eps).
Uncertainty: bootstrap over EPISODES (all snapshots of an episode resampled together).
"""
from __future__ import annotations
import argparse, glob, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, featurize, Net, choose
from models.marl_e3_response import resp_features, RespNet


def ep_boot(vals, eps, B=5000, seed=0):
    by = defaultdict(list)
    for v, e in zip(vals, eps):
        by[e].append(v)
    E = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[E[k]] for k in rng.integers(0, len(E), len(E))])) for _ in range(B)]
    return [float(x) for x in np.quantile(out, [0.025, 0.975])]


def predictions(meta, net, hn, st):
    c, d, y, feas, r1 = featurize(st, meta['bid'], meta['gap_thr'])
    ctx_extra = None
    if meta.get('qbid'):
        from scripts.MARL_e3_selector_train import BID_BYTES as _BB, CAP as _CAP
        c = np.concatenate([c, np.asarray(st['qbid'], np.float32) / 50.0]).astype(np.float32)
        feas = np.array([cc['bytes'] <= st['b0'] + _CAP - _BB for cc in st['cands']])
    if hn is not None:
        X = resp_features(st, meta['bid'], meta['gap_thr'])
        with torch.no_grad():
            pr = torch.sigmoid(hn(torch.as_tensor((X - meta['head']['mu']) / meta['head']['sd']))).numpy()
        d = np.concatenate([d, pr, pr.sum(1, keepdims=True)], 1).astype(np.float32)
    if meta.get('priv_joint'):
        P = st['cands'][0]['joint']; J = np.array([cc['joint'] for cc in st['cands']])
        oh = np.eye(9, dtype=np.float32)[J].reshape(len(J), -1); ch = (J != np.array(P)[None]).astype(np.float32)
        c = np.concatenate([c, np.eye(9, dtype=np.float32)[np.array(P)].ravel()]).astype(np.float32)
        d = np.concatenate([d, oh, ch, ch.sum(1, keepdims=True)], 1).astype(np.float32)
    if meta.get('resp_multi'):                                  # v5 multi-class head, same order as the trainer
        from scripts.MARL_e3_selector_train_v5 import RespMulti, multi_features
        hm = meta['head_multi']; nm = RespMulti(); nm.load_state_dict(hm['state']); nm.eval()
        pm, tv = multi_features(nm, hm['mu'], hm['sd'], resp_features(st, meta['bid'], meta['gap_thr'])); C_ = pm.shape[0]
        c = np.concatenate([c, pm[0].ravel()]).astype(np.float32)
        d = np.concatenate([d, pm.reshape(C_, -1), tv, tv.sum(1, keepdims=True)], 1).astype(np.float32)
    with torch.no_grad():
        p = net(torch.as_tensor((c - meta['cm']) / meta['cs'])[None], torch.as_tensor(d)).numpy() * meta['ys']
    return p - p[0], y, feas, r1


def assess(S, meta, net, hn, pol):
    tau = meta['tau'][pol]; tau = {None: -np.inf, '-inf': -np.inf, '+inf': np.inf}.get(tau, tau) if not isinstance(tau, float) else tau
    rows = []
    for st in S:
        an, y, feas, r1 = predictions(meta, net, hn, st)
        allow = r1 if pol == 'R1' else np.ones_like(r1); ok = feas & allow; ok[0] = True
        j = choose(an, feas, allow, tau)
        a_, y_ = an[ok], y[ok]
        rho = spearmanr(a_, y_).correlation if np.ptp(a_) > 0 and np.ptp(y_) > 0 else np.nan
        dy = y_[:, None] - y_[None, :]; da = a_[:, None] - a_[None, :]; m = dy > 0
        rows.append(dict(ep=st['episode_id'], gain=float(y[j]), edit=bool(j != 0), best=float(y_.max()), rho=rho,
                         pair_acc=float((da[m] > 0).mean()) if m.any() else np.nan, err=np.abs(a_[1:] - y_[1:])))
    g = [r['gain'] for r in rows]; e = [r['ep'] for r in rows]; ed = [r['edit'] for r in rows]
    harm = [r['gain'] < 0 for r in rows if r['edit']]
    err = np.concatenate([r['err'] for r in rows]) if rows else np.array([0.0])
    return dict(realised_gain=float(np.mean(g)), realised_gain_ci=ep_boot(g, e), edit_rate=float(np.mean(ed)),
                harmful_edit_rate=float(np.mean(harm)) if harm else None, gain_given_edit=float(np.mean([r['gain'] for r in rows if r['edit']])) if any(ed) else None,
                oracle_best=float(np.mean([r['best'] for r in rows])), top1_regret=float(np.mean([r['best'] - r['gain'] for r in rows])),
                spearman_ties=float(np.nanmean([r['rho'] for r in rows])), pair_order_accuracy=float(np.nanmean([r['pair_acc'] for r in rows])),
                gain_error_q50=float(np.quantile(err, .5)), gain_error_q90=float(np.quantile(err, .9)), states=len(rows), tau=None if np.isinf(tau) else float(tau))


def main(a):
    D = Path(a.actor_dir); out = {}
    data = {sp: load([x for x in sorted(glob.glob(str(D / pat))) if Path(x).is_dir()])[0] for sp, pat in (('select', 'labels_select'), ('dev', 'labels_dev'))}
    import gzip
    for sp, pat in (('select', 'labels_select'), ('dev', 'labels_dev')):          # same-byte queue bid side data, if collected
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
        out[name] = {pol: {sp: assess(S, meta, net, hn, pol) for sp, S in data.items()} for pol in ('direct', 'R1')}
        r = out[name]['direct']['dev']
        print(f"{name:22s} dev direct: gain {r['realised_gain']:+.2f} [{r['realised_gain_ci'][0]:+.2f},{r['realised_gain_ci'][1]:+.2f}] "
              f"edit {r['edit_rate']:.2f} harm|edit {r['harmful_edit_rate'] if r['harmful_edit_rate'] is None else round(r['harmful_edit_rate'], 2)} "
              f"| oracle {r['oracle_best']:.1f} | spearman(ties) {r['spearman_ties']:+.3f} pair-acc {r['pair_order_accuracy']:.3f} | gain-err q90 {r['gain_error_q90']:.1f}", flush=True)
    Path(a.out).write_text(json.dumps(out, indent=1))


if __name__ == '__main__':
    # RETIRED 28/09 19:18 (handoff MARL_REMAINING_WORK_HANDOFF_20260928_1910 W1; ledger L-58): the pair order accuracy of this
    # entry point is STRICT (a predicted tie counts as wrong), so it must not be read against 0.5 or a tie-half rule.  The
    # functions stay importable unchanged; new runs use scripts/MARL_e3_selector_diag_v3.py.  E3_ALLOW_STRICT_DIAG_V2=1 reproduces a historical artifact.
    import os
    if os.environ.get('E3_ALLOW_STRICT_DIAG_V2') != '1':
        sys.exit('refusing: this diagnostic is retired (strict pair metric); run scripts/MARL_e3_selector_diag_v3.py '
                 '(or E3_ALLOW_STRICT_DIAG_V2=1 to reproduce a historical artifact)')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--selectors', default='selectors_v2'); p.add_argument('--out', required=True)
    main(p.parse_args())
