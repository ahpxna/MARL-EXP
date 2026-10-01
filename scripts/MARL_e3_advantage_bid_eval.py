#!/usr/bin/env python3
"""Route 2, step 2 (MARL_DEEP_RESEARCH_20260929.md): does a per-agent action-value model, used SMV-style, rank the E3
message candidates?  Offline development diagnostic (read-only: saved models, forced-probe v2 rows, stored labels).

For every DEV state (forced-probe v2 rows carry each agent's actor input x_i) and every feasible candidate c:
  PRIV  (diagnostic)  score(c) = sum_i [a_i(c) != a0_i] * Qhat(x_i, a_i(c))   with the candidate's TRUE induced actions
                      (the SMV value of the induced action changes; tells whether Qhat + perfect response knowledge ranks);
  BID   (legal form)  score(c) = sum_i Phat_i(c) * Qhat(x_i, p2_i)             Phat = the saved v8 response head's
                      probability that c changes receiver i's action, p2_i = the receiver's runner-up in its bid;
                      Qhat(x_i, p2_i) is what a receiver would send as a 1-byte advantage bid.
Compared on the same states with the saved v8 legal critic (selectors_v8, the test-1 checkpoints) and the oracle.
Reported: tie-half pair accuracy over the feasible (+74 B) set, Spearman, realised gain of the argmax and of a tau rule
chosen on the SELECT rows (grid {-inf, 0, q90, q99, +inf}).  x_i is the post-prefix view (see MARL_e3_agent_q_train.py);
this is a ranking diagnostic, not a deployable rule.
"""
from __future__ import annotations
import argparse, glob, json, sys
from pathlib import Path
import numpy as np
import torch
from torch import nn
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, CAP, BID_BYTES
from scripts.MARL_e3_ranking_diag_v2 import pair_acc
from scripts.MARL_e3_selector_train_v3 import head_probs
from scripts.MARL_e3_selector_diag_v2 import predictions
from scripts.MARL_e3_selector_train import Net
from models.marl_e3_response import resp_features, RespNet


def load_q(path):
    m = torch.load(path, weights_only=False)
    net = nn.Sequential(nn.Linear(m['dim'], m['hidden']), nn.ReLU(), nn.Linear(m['hidden'], m['hidden']), nn.ReLU(), nn.Linear(m['hidden'], 1))
    net.load_state_dict(m['state']); net.eval()
    return lambda F: net(torch.as_tensor((F - m['mu']) / m['sd'])).squeeze(-1).detach().numpy() * m['ys']


def q_table(Q, r):
    """Qhat(x_i, a) for every agent and phase (the model's input layout of MARL_e3_agent_q_train.state_arrays)."""
    x = np.asarray(r['x'], np.float32); L = np.asarray(r['logits'], np.float32); j0 = r['prefix_joint']; m = len(j0)
    F = np.stack([np.concatenate([x[i], np.eye(9, dtype=np.float32)[a], np.eye(9, dtype=np.float32)[j0[i]], [L[i, a] - L[i, j0[i]]]])
                  for i in range(m) for a in range(9)])
    return Q(F).reshape(m, 9)


def main(a):
    St = {}
    for sp in ('select', 'dev'):
        S = load([Path(a.actor_dir) / f'labels_{sp}'])[0]
        St[sp] = {(f"seed{st['traffic_seed']}_load{st['headway']:g}", st['t']): st for st in S}
    Qs = [load_q(p) for p in sorted(glob.glob(a.q_models))]
    heads = []
    for p in sorted(glob.glob(str(Path(a.actor_dir) / 'selectors_v8/model_legal_bid_resp_s*.pt'))):
        meta = torch.load(p, weights_only=False); net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval()
        hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval(); heads.append((meta, net, hn))
    out = {}
    for sp in ('select', 'dev'):
        R = json.loads(Path(a.rows[sp], 'rows.json').read_text()); per = []
        for r in R:
            st = St[sp][(r['episode'], r['t'])]; C = st['cands']; m = st['m']; j0 = r['prefix_joint']
            y = np.array([c['cont'] for c in C]) - C[0]['cont']
            ok = np.array([k == 0 or c['bytes'] <= st['b0'] + CAP - BID_BYTES for k, c in enumerate(C)])
            QT = np.mean([q_table(Q, r) for Q in Qs], 0)
            J = np.array([c['joint'] for c in C])
            priv = np.array([sum(QT[i, J[k, i]] for i in range(m) if J[k, i] != j0[i]) for k in range(len(C))])
            p2 = np.array([b['p2'] for b in st['bid']])
            bid = np.zeros(len(C))
            crit = np.zeros(len(C))
            for meta, net, hn in heads:
                P = head_probs(hn, meta['head']['mu'], meta['head']['sd'], resp_features(st, meta['bid'], meta['gap_thr']))
                bid += (P * QT[np.arange(m), p2][None, :]).sum(1) / len(heads)
                crit += predictions(meta, net, hn, st)[0] / len(heads)
            per.append(dict(y=y, ok=ok, scores=dict(priv=priv - priv[0], bid=bid - bid[0], critic_v8=crit - crit[0]), seed=r['traffic_seed']))
        out[sp] = per
    res = {}
    for name in ('priv', 'bid', 'critic_v8'):
        def decide(sp, tau):
            return float(np.mean([float(p['y'][j]) if (v := np.where(p['ok'], p['scores'][name], -np.inf))[(j := int(np.argmax(v)))] > tau else 0.0
                                  for p in out[sp]]))
        grid = [-np.inf, 0.0] + sorted({float(np.quantile(p['scores'][name][1:], q)) for p in out['select'] for q in (0.9, 0.99)}) + [np.inf]
        tau = max(grid, key=lambda t: decide('select', t))
        D = out['dev']
        pa = [pair_acc(p['scores'][name][p['ok']], p['y'][p['ok']])[0] for p in D]
        rho = [spearmanr(p['scores'][name][p['ok']], p['y'][p['ok']]).correlation for p in D if np.ptp(p['scores'][name][p['ok']]) > 0]
        res[name] = dict(dev_pair_acc=float(np.nanmean(pa)), dev_spearman=float(np.nanmean(rho)), dev_gain_argmax=decide('dev', -np.inf),
                         dev_gain_tau=decide('dev', tau), tau=('+inf' if tau > 0 else '-inf') if np.isinf(tau) else float(tau))
        print(f"{name:10s} DEV pair acc {res[name]['dev_pair_acc']:.4f} spearman {res[name]['dev_spearman']:+.3f} | gain argmax {res[name]['dev_gain_argmax']:+.2f} "
              f"tau rule {res[name]['dev_gain_tau']:+.2f} (tau {res[name]['tau']})", flush=True)
    res['dev_oracle'] = float(np.mean([p['y'][p['ok']].max() for p in out['dev']])); print(f"oracle {res['dev_oracle']:+.2f}")
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor-dir', required=True); p.add_argument('--q-models', required=True, help='glob of model_agentq_s*.pt')
    p.add_argument('--select-rows', required=True); p.add_argument('--dev-rows', required=True); p.add_argument('--out', required=True)
    a = p.parse_args(); a.rows = dict(select=a.select_rows, dev=a.dev_rows); main(a)
