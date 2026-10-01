#!/usr/bin/env python3
"""v8 copy (29/09): the SAME decision table run on the selector-v8 (floored normaliser) replication of the DFL round
(<actor>/selectors_v8dfl, RUN_marl_e3_dfl_v8.sh); descriptive replication after the L-65 fix, not the registered round.
Original: PROTOCOL_E3_DFL_20260928.md (with Amendment 1, 20:08) decision table.  Read-only: saved checkpoints and labels, no
training, no rollouts.

Arms on ONE label table (default <actor>/labels_dev), each the 3 init checkpoints of one v6 recipe (equal lr grid,
chosen on SELECT):
  mse_all   selectors_v8dfl/model_legal_bid_resp_mse_s*.pt      (v3 MSE over every candidate)
  mse_feas  selectors_v8dfl/model_legal_bid_resp_msefeas_s*.pt  (MSE over the feasible set)
  dfl       selectors_v8dfl/model_legal_bid_resp_dfl_s*.pt      (expected-gain loss, T = 1)
  v3_hist   selectors_v3/model_legal_bid_resp_s*.pt          (historical, lr 1e-3 only; DESCRIPTIVE)
Per state, an arm's realised gain = mean over its checkpoints of y[chosen] (MARL_e3_paired_eval.arm_gains: each
checkpoint's own tau, direct policy); edits, harm | edit and charged bytes (chosen profile bytes - prefix bytes + the
10 B bid, which is charged at every step) are recomputed from the same choices.
Screen (primary actor, primary table), per Amendment 1: for each contrast (dfl - prefix, dfl - mse_all, dfl - mse_feas)
the statistic is the mean of the 8 traffic-seed means; PASS iff the mean > 0 and the one-sided sign-flip p over all
2^8 sign vectors is <= 0.05, for ALL three (intersection-union).  Stated assumption: under the null the seed-level
differences are independent and symmetric about 0; the p-value is a screening statistic under it, not a
distribution-free guarantee about the mean.  Also reported: seed-level means, traffic-seed percentile bootstrap and
episode bootstrap CIs, leave-one-seed-out ranges, oracle regret.
Self-checks (abort): every checkpoint was trained on the labels' actor checkpoint; each primary arm has 3 inits;
sign-flip unit test (a symmetric all-positive vector of 8 gives p = 1/256).
"""
from __future__ import annotations
import argparse, glob, hashlib, itertools, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, Net, choose, BID_BYTES, CAP
from scripts.MARL_e3_selector_diag_v2 import predictions
from scripts.MARL_e3_paired_eval import boot
from models.marl_e3_response import RespNet

ARMS = {'mse_all': 'selectors_v8dfl/model_legal_bid_resp_mse_s*.pt', 'mse_feas': 'selectors_v8dfl/model_legal_bid_resp_msefeas_s*.pt',
        'dfl': 'selectors_v8dfl/model_legal_bid_resp_dfl_s*.pt', 'v3_hist': 'selectors_v3/model_legal_bid_resp_s*.pt'}
PRIMARY = ('mse_all', 'mse_feas', 'dfl')


def sign_flip_p(x):
    """One-sided p of mean(x) > 0 over all 2^n sign vectors (x = seed-level differences)."""
    x = np.asarray(x, float); t = x.mean(); n = len(x)
    S = np.array(list(itertools.product((1.0, -1.0), repeat=n)))
    return float(((S * x[None]).mean(1) >= t - 1e-12).mean())


def selftest():
    assert abs(sign_flip_p(np.ones(8)) - 1 / 256) < 1e-12, 'sign-flip p of an all-positive vector must be 1/256'
    assert sign_flip_p(np.zeros(8)) == 1.0
    print('selftest PASS (sign-flip: all-positive 1/256, all-zero 1)', flush=True)


def arm_choices(files, S):
    G = np.zeros((len(files), len(S))); E = np.zeros_like(G); H = np.full_like(G, np.nan); Bt = np.zeros_like(G)
    for n, mf in enumerate(files):
        meta = torch.load(mf, weights_only=False); net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        tau = meta['tau']['direct']; tau = {None: -np.inf, '-inf': -np.inf, '+inf': np.inf}.get(tau, tau) if not isinstance(tau, float) else tau
        for s, st in enumerate(S):
            an, y, feas, r1 = predictions(meta, net, hn, st); j = choose(an, feas, np.ones_like(r1), tau)
            G[n, s] = y[j]; E[n, s] = j != 0; H[n, s] = float(y[j] < 0) if j != 0 else np.nan
            Bt[n, s] = st['cands'][j]['bytes'] - st['b0'] + (BID_BYTES if meta['bid'] else 0)
    return G.mean(0), E.mean(0), H, Bt.mean(0)


def seed_means(v, seeds):
    by = defaultdict(list)
    for x, k in zip(v, seeds):
        by[k].append(x)
    K = sorted(by)
    return K, np.array([np.mean(by[k]) for k in K])


def main(a):
    selftest()
    A = Path(a.actor_dir); L = Path(a.labels) if a.labels else A / 'labels_dev'
    S, ck = load([L]); seeds = [str(st['traffic_seed']) for st in S]; eps = [st['episode_id'] for st in S]
    files = {k: sorted(glob.glob(str(A / p))) for k, p in ARMS.items()}
    for k in PRIMARY:
        if len(files[k]) != 3:
            raise SystemExit(f'SELF-CHECK FAIL: arm {k} has {len(files[k])} checkpoints, expected 3')
    for k, fs in files.items():
        for f in fs:
            j = json.loads(Path(f.replace('model_', 'job_').replace('.pt', '.json')).read_text())
            if {j['actor_ckpt']} != ck:
                raise SystemExit(f'SELF-CHECK FAIL: {f} trained on {j["actor_ckpt"]}, labels from {ck}')
    orc = np.array([max(float(c['cont'] - st['cands'][0]['cont']) for i, c in enumerate(st['cands']) if i == 0 or c['bytes'] <= st['b0'] + CAP - BID_BYTES) for st in S])
    res = dict(actor_dir=str(A), labels=str(L), states=len(S), traffic_seeds=len(set(seeds)), episodes=len(set(eps)), label_ckpt=sorted(ck), primary=a.primary,
               assumption='sign-flip: seed-level differences independent and symmetric about 0 under the null (screening statistic, not a distribution-free mean guarantee)',
               checkpoints={k: [dict(file=f, sha256=hashlib.sha256(Path(f).read_bytes()).hexdigest()) for f in fs] for k, fs in files.items()},
               oracle_mean=float(orc.mean()), arms={}, contrasts={})
    G = {}
    for k, fs in files.items():
        if not fs:
            continue
        g, e, h, b = arm_choices(fs, S); G[k] = g
        K, sm = seed_means(g, seeds)
        res['arms'][k] = dict(mean_gain=float(g.mean()), seed_means=dict(zip(K, sm.round(4).tolist())), ci_traffic_seed=boot(g, seeds)[0], ci_episode=boot(g, eps)[0],
                              edit_rate=float(e.mean()), harm_given_edit=float(np.nanmean(h)) if np.isfinite(h).any() else None,
                              regret=float((orc - g).mean()), charged_bytes_over_prefix=float(b.mean()), role='primary' if k in PRIMARY else 'descriptive')
    for name, d in (('dfl_minus_prefix', G['dfl']), ('dfl_minus_mse_all', G['dfl'] - G['mse_all']), ('dfl_minus_mse_feas', G['dfl'] - G['mse_feas'])):
        K, sm = seed_means(d, seeds)
        loo = [float(np.delete(sm, q).mean()) for q in range(len(sm))]
        p = sign_flip_p(sm); passed = bool(sm.mean() > 0 and p <= 0.05)
        res['contrasts'][name] = dict(mean_of_seed_means=float(sm.mean()), mean_over_states=float(d.mean()), seed_means=dict(zip(K, sm.round(4).tolist())),
                                      sign_flip_p_one_sided=p, ci_traffic_seed=boot(d, seeds)[0], ci_episode=boot(d, eps)[0],
                                      leave_one_seed_out=[min(loo), max(loo)], screen_pass=passed)
    allpass = all(c['screen_pass'] for c in res['contrasts'].values())
    res['screen'] = ('PASS' if allpass else 'FAIL') if a.primary else f"not gating (secondary); would be {'PASS' if allpass else 'FAIL'}"
    for k, v in res['arms'].items():
        print(f"{A.name} {L.name} {k:8s} [{v['role']}]: gain {v['mean_gain']:+.3f} seed CI [{v['ci_traffic_seed'][0]:+.2f},{v['ci_traffic_seed'][1]:+.2f}] "
              f"edit {v['edit_rate']:.3f} harm|edit {v['harm_given_edit']} regret {v['regret']:.2f} bytes +{v['charged_bytes_over_prefix']:.1f} (oracle {res['oracle_mean']:.2f})", flush=True)
    for k, c in res['contrasts'].items():
        print(f"  {k:20s} mean of seed means {c['mean_of_seed_means']:+.3f}  sign-flip p {c['sign_flip_p_one_sided']:.4f}  seed CI [{c['ci_traffic_seed'][0]:+.2f},{c['ci_traffic_seed'][1]:+.2f}]  "
              f"LOO [{c['leave_one_seed_out'][0]:+.2f},{c['leave_one_seed_out'][1]:+.2f}]  -> {'pass' if c['screen_pass'] else 'fail'}", flush=True)
    print(f"SCREEN: {res['screen']}", flush=True)
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor-dir', required=True); p.add_argument('--labels'); p.add_argument('--primary', action='store_true')
    p.add_argument('--out', required=True)
    main(p.parse_args())
