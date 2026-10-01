#!/usr/bin/env python3
"""Why does the E3 critic order candidates WORSE than chance? (read-only; saved checkpoints and labels, no training.)

Diagnostic v2 found pairwise order accuracy 0.40-0.48 on held-out development states for every evaluator arm,
below the 0.5 of a random scorer.  A systematic sub-0.5 ordering means the critic follows some signal that is
ANTI-aligned with the true gains on held-out states.  This script tests three explanations, per checkpoint, on
the TRAIN, SELECT and DEV states (feasible candidates, pairs whose true gains differ):
  (1) overfitting: pair accuracy in-sample (TRAIN) vs held-out (SELECT, DEV);
  (2) edit size: the number of replaced senders n_repl.  Reported: rank correlation of the true gain and of the
      prediction with n_repl; the pair accuracy of the simple rule "fewer replacements is better"; and the
      critic's pair accuracy restricted to pairs with EQUAL n_repl (edit size controlled);
  (3) magnitude: pair accuracy on pairs whose true gain differs by at least 5 units.
Also: the fraction of candidates whose true gain is exactly 0 (ties with the prefix).
"""
from __future__ import annotations
import argparse, glob, json, sys
from pathlib import Path
import numpy as np
import torch
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, Net
from scripts.MARL_e3_selector_diag_v2 import predictions
from models.marl_e3_response import RespNet


def n_repl(c, P):
    return sum(len(set(s) - set(p)) for s, p in zip(c['sets'], P['sets']))


def pair_stats(an, y, nr, mask_extra=None):
    dy = y[:, None] - y[None, :]; da = an[:, None] - an[None, :]; dn = nr[:, None] - nr[None, :]
    m = dy > 0
    out = dict(pairs=int(m.sum()), acc=float((da[m] > 0).mean()) if m.any() else np.nan,
               fewer_edits_rule=float((dn[m] < 0).mean() + 0.5 * (dn[m] == 0).mean()) if m.any() else np.nan)
    me = m & (dn == 0); out['acc_equal_edit_size'] = float((da[me] > 0).mean()) if me.any() else np.nan; out['pairs_equal_edit_size'] = int(me.sum())
    mb = (dy >= 5); out['acc_big_differences'] = float((da[mb] > 0).mean()) if mb.any() else np.nan; out['pairs_big'] = int(mb.sum())
    return out


def main(a):
    D = Path(a.actor_dir); res = {}
    splits = {sp: load([x for x in sorted(glob.glob(str(D / pat))) if Path(x).is_dir()])[0]
              for sp, pat in (('train', 'labels_train_*'), ('select', 'labels_select'), ('dev', 'labels_dev'))}
    if a.max_train:
        splits['train'] = splits['train'][:a.max_train]
    for mf in sorted(glob.glob(str(D / a.models))):
        meta = torch.load(mf, weights_only=False); net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        r = {}
        for sp, S in splits.items():
            agg = dict(acc=[], fewer=[], acc_eq=[], acc_big=[], rho_true_n=[], rho_pred_n=[], zero_gain=[])
            for st in S:
                an, y, feas, _ = predictions(meta, net, hn, st); ok = feas.copy(); ok[0] = True
                P = st['cands'][0]; nr = np.array([n_repl(c, P) for c in st['cands']], float)
                a_, y_, n_ = an[ok], y[ok], nr[ok]; ps = pair_stats(a_, y_, n_)
                agg['acc'].append(ps['acc']); agg['fewer'].append(ps['fewer_edits_rule']); agg['acc_eq'].append(ps['acc_equal_edit_size']); agg['acc_big'].append(ps['acc_big_differences'])
                if np.ptp(y_) > 0 and np.ptp(n_) > 0:
                    agg['rho_true_n'].append(spearmanr(y_, n_).correlation)
                if np.ptp(a_) > 0 and np.ptp(n_) > 0:
                    agg['rho_pred_n'].append(spearmanr(a_, n_).correlation)
                agg['zero_gain'].append(float((y_[1:] == 0).mean()))
            r[sp] = {k: round(float(np.nanmean(v)), 3) for k, v in agg.items()} | dict(states=len(S))
        res[Path(mf).stem] = r
        print(f'{Path(mf).stem:28s} ' + ' | '.join(f'{sp}: acc {v["acc"]:.3f} (equal-size {v["acc_eq"]:.3f}, big {v["acc_big"]:.3f}) fewer-edits rule {v["fewer"]:.3f} '
              f'rho(true,n) {v["rho_true_n"]:+.2f} rho(pred,n) {v["rho_pred_n"]:+.2f} zero {v["zero_gain"]:.2f}' for sp, v in r.items()), flush=True)
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    # RETIRED 28/09 19:18 (handoff MARL_REMAINING_WORK_HANDOFF_20260928_1910 W1; ledger L-58): the pair order accuracy of this
    # entry point is STRICT (a predicted tie counts as wrong), so it must not be read against 0.5 or a tie-half rule.  The
    # functions stay importable unchanged; new runs use scripts/MARL_e3_ranking_diag_v2.py.  E3_ALLOW_STRICT_RANKING_V1=1 reproduces a historical artifact.
    import os
    if os.environ.get('E3_ALLOW_STRICT_RANKING_V1') != '1':
        sys.exit('refusing: this diagnostic is retired (strict pair metric); run scripts/MARL_e3_ranking_diag_v2.py '
                 '(or E3_ALLOW_STRICT_RANKING_V1=1 to reproduce a historical artifact)')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--models', default='selectors_v3/model_legal_bid_resp_s*.pt')
    p.add_argument('--max-train', type=int, default=0); p.add_argument('--out', required=True)
    main(p.parse_args())
