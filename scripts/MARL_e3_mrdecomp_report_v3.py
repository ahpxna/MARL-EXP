#!/usr/bin/env python3
"""F5b report v3 (independent recheck 16:11, findings N1 and N2; read-only).  NOTE: written 16:42 by the worker as an
independent re-implementation; it OVERWROTE another session's MARL_e3_mrdecomp_report_v2.py (source lost: not in git, no
snapshot), whose outputs report_v2.{json,txt} (16:21) are kept unchanged.  v1 and its report.json are kept.

N1  "Best found" is the best of BOTH searches, per state: max(V_LS, V_LSP). V_LS alone is the search started at
    the family's best profile. Coverage lower bound = best found - V_famB; prefix-start share = sum V_LSP / sum best.
N2  The v1 "estimation loss" V_own - f(chosen) mixes the critic's ranking with the tuned edit threshold tau.  Split,
    per checkpoint and state, on the stored development labels (original loader order; no training, no rollouts):
        V_own - f(chosen) = [V_own - f(critic argmax)]  +  [f(critic argmax) - f(chosen)]
                            ranking regret (>= 0)          signed threshold effect (negative when tau helps)
    with the critic argmax over the arm's OWN feasible family (tau = -inf), the number of decisions the threshold
    changes, and the predicted optimisation gap fhat(argmax) - fhat(chosen) (>= 0), so the Lean deployed_regret
    bound needs its search term nu, not only epsilon, for the thresholded rule.
Self-checks (abort): recomputing each checkpoint's choice with its saved tau reproduces the saved dev_chosen; the
F5b rows' family values equal the label values; the arm realised gains equal the v1 rows.
"""
from __future__ import annotations
import argparse, glob, gzip, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, Net, choose
from scripts.MARL_e3_selector_diag_v2 import predictions
from models.marl_e3_response import RespNet

ARMS = {'legal': 'selectors_v3/model_legal_bid_resp_s*.pt', 'no_bid': 'selectors_v4/model_sb_nobid_s*.pt',
        'queue_bid': 'selectors_v4/model_sb_queuebid_s*.pt', 'multi_head': 'selectors_v5/model_multi_bid_s*.pt',
        'privileged': 'selectors_v3/model_priv_only_s*.pt'}
ACTORS = {'scratch_s3': 'research/marl_budget/e3_scratch_seeds34_20260928/actor_s3', 'bc_s3': 'research/marl_budget/e3_run_seeds34_20260928/actor_s3'}


def boot(v, keys, B=5000, seed=0):
    by = defaultdict(list)
    for x, k in zip(v, keys):
        by[k].append(x)
    K = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[K[i]] for i in rng.integers(0, len(K), len(K))])) for _ in range(B)]
    return [round(float(x), 2) for x in np.quantile(out, [0.025, 0.975])]


def stat(v, eps):
    v = np.asarray(v, float); return dict(mean=round(float(v.mean()), 4), ci_episode=boot(v, eps), ci_seed=boot(v, [e.split('_')[0] for e in eps]))


def parse_tau(t):
    return {None: -np.inf, '-inf': -np.inf, '+inf': np.inf}.get(t, t) if not isinstance(t, float) else t


def main(a):
    R = Path(a.dir); res = {}
    for actor, D in ACTORS.items():
        D = Path(D); rows = [r for s in sorted(glob.glob(str(R / f'{actor}_shard[0-9]'))) for r in json.loads(Path(s, 'rows.json').read_text())]
        if len(rows) != 48 or not all(Path(s, 'manifest.json').exists() for s in glob.glob(str(R / f'{actor}_shard[0-9]'))):
            raise SystemExit(f'{actor}: F5b incomplete')
        S, _ = load([D / 'labels_dev']); key = {(st['episode_id'], st['t']): k for k, st in enumerate(S)}
        qd = D / 'qbid_labels_dev'
        if (qd / 'manifest.json').exists():
            Q = {(r['episode_id'], r['t']): r['qbid'] for r in map(json.loads, gzip.open(qd / 'qbid.jsonl.gz', 'rt'))}
            for st in S:
                st['qbid'] = Q.get((st['episode_id'], st['t']))
        idx = [key[(r['episode'], r['t'])] for r in rows]; eps = [r['episode'] for r in rows]
        y = [np.array([c['cont'] for c in S[k]['cands']]) - S[k]['cands'][0]['cont'] for k in idx]
        for r, yy, k in zip(rows, y, idx):
            fB = np.array([c['bytes'] <= S[k]['b0'] + 84 for c in S[k]['cands']])
            if abs(yy[fB].max() - r['V_famB']) > 1e-9:
                raise SystemExit('SELF-CHECK FAIL: F5b V_famB differs from the label table')
        best = np.array([max(r['V_LS'], r['V_LSP']) for r in rows]); famB = np.array([r['V_famB'] for r in rows]); lsp = np.array([r['V_LSP'] for r in rows])
        out = dict(states=48, n1=dict(best_found_both_searches=stat(best, eps), family_start_search=stat([r['V_LS'] for r in rows], eps),
                   prefix_start_search=stat(lsp, eps), prefix_better_states=int(sum(r['V_LSP'] > r['V_LS'] for r in rows)),
                   coverage_lb_best=stat(best - famB, eps), prefix_start_share_of_best=round(float(lsp.sum() / best.sum()), 4)), n2={})
        for arm, pat in ARMS.items():
            per = defaultdict(list); ck = []
            for mf in sorted(glob.glob(str(D / pat))):
                meta = torch.load(mf, weights_only=False); job = json.loads(Path(mf.replace('model_', 'job_').replace('.pt', '.json')).read_text())
                net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
                if meta.get('resp'):
                    hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
                tau = parse_tau(meta['tau']['direct']); saved = job['results']['direct']['dev_chosen']; real = []; arg = []; changed = 0; gap = []
                for n, (k, yy) in enumerate(zip(idx, y)):
                    an, _, feas, r1 = predictions(meta, net, hn, S[k]); al = np.ones_like(r1)
                    jc = choose(an.copy(), feas, al, tau); ja = choose(an.copy(), feas, al, -np.inf)
                    if jc != saved[k]:
                        raise SystemExit(f'SELF-CHECK FAIL: {mf}: recomputed choice {jc} != saved {saved[k]} at state {k}')
                    own = yy[np.where(feas | (np.arange(len(yy)) == 0))[0]].max()
                    per['ranking'].append((n, own - yy[ja])); per['threshold'].append((n, yy[ja] - yy[jc])); per['total'].append((n, own - yy[jc]))
                    real.append(yy[jc]); arg.append(yy[ja]); changed += int(ja != jc); gap.append(float(an[ja] - an[jc]))
                ck.append(dict(model=Path(mf).name, tau=None if np.isinf(tau) else round(float(tau), 4), realised=round(float(np.mean(real)), 4),
                               argmax_gain=round(float(np.mean(arg)), 4), decisions_changed_by_tau=changed, predicted_opt_gap=round(float(np.mean(gap)), 4)))
            avg = lambda name: [np.mean([v for n, v in per[name] if n == i]) for i in range(48)]
            real_arm = [np.mean([y[i][json.loads(Path(m.replace('model_', 'job_').replace('.pt', '.json')).read_text())['results']['direct']['dev_chosen'][idx[i]]]
                                 for m in sorted(glob.glob(str(D / pat)))]) for i in range(48)]
            if max(abs(u - r['arms'][arm]['realised']) for u, r in zip(real_arm, rows)) > 1e-9:
                raise SystemExit(f'SELF-CHECK FAIL: {actor} {arm}: realised gains differ from the F5b rows')
            out['n2'][arm] = dict(checkpoints=ck, total_within_family_regret=stat(avg('total'), eps), ranking_regret=stat(avg('ranking'), eps),
                                  threshold_effect_signed=stat(avg('threshold'), eps))
        res[actor] = out
        n1 = out['n1']
        print(f'== {actor}: best found (both searches) {n1["best_found_both_searches"]["mean"]:+.2f} {n1["best_found_both_searches"]["ci_episode"]}; '
              f'prefix-start better in {n1["prefix_better_states"]}/48; coverage lb {n1["coverage_lb_best"]["mean"]:+.2f} {n1["coverage_lb_best"]["ci_episode"]}; '
              f'prefix-start share {100 * n1["prefix_start_share_of_best"]:.1f}%')
        for arm, v in out['n2'].items():
            print(f'   {arm:11s} total {v["total_within_family_regret"]["mean"]:+6.2f} = ranking {v["ranking_regret"]["mean"]:+6.2f} {v["ranking_regret"]["ci_episode"]} '
                  f'+ threshold {v["threshold_effect_signed"]["mean"]:+6.2f} {v["threshold_effect_signed"]["ci_episode"]} | ' +
                  '; '.join(f'tau {c["tau"]} real {c["realised"]:+.3f} argmax {c["argmax_gain"]:+.3f} chg {c["decisions_changed_by_tau"]} gap {c["predicted_opt_gap"]:.3f}' for c in v['checkpoints']))
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--dir', required=True); p.add_argument('--out', required=True); main(p.parse_args())
