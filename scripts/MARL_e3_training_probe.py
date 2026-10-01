#!/usr/bin/env python3
"""Why does the E3 critic not rank candidates?  A read-only probe of the TRAINING side (no rollouts, no label change).

D1  fit vs generalisation of the existing flat critic (selector v3 legal_bid_resp, 3 init seeds): within-state pair-order
    accuracy (pairs with different true gains), tie-aware Spearman and argmax-regret on TRAIN, SELECT and DEV, on all
    candidates and on single-receiver one-swaps only.  Underfit (TRAIN ~ chance) and overfit (TRAIN high, DEV chance)
    call for different changes.
D2  where the headroom lives: best single one-swap vs family best; share of zero-gain candidates.
D3  is there LEGAL ranking signal an EDGE-structured model extracts?  For every one-swap (receiver i drops a, adds b):
    edge features e(i, j) = [mirror block (what i caches from j): present, age, phase, elapsed, vehicles, waiting;
    scheduler block z_j (latest paid payload of j); z_j - mirror (content change since i's copy); grid adjacency],
    receiver features r(i) = [k_i / m, z_i (i's own last payload)].  Models on [e(i,b), e(i,a), e(i,b) - e(i,a), r(i)]:
      ridge   linear, closed form;
      mlp     one shared small MLP (the same scorer for every edge), MSE on the swap gain, early stop on SELECT.
    Trained on TRAIN one-swaps only; reported on DEV one-swaps: pair accuracy and the gain of the best-predicted swap.
All inputs are legal scheduler data (z, mirror, K, public topology); labels are used only as training targets.
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
from scripts.MARL_e3_selector_train import load, Net, choose
from scripts.MARL_e3_selector_diag_v2 import predictions
from models.marl_e3_response import RespNet, grid_adjacent


def swaps(st):
    P = st['cands'][0]['sets']; out = []
    for k, c in enumerate(st['cands'][1:], 1):
        d = [(i, set(P[i]) - set(c['sets'][i]), set(c['sets'][i]) - set(P[i])) for i in range(st['m']) if set(c['sets'][i]) != set(P[i])]
        if len(d) == 1 and len(d[0][1]) == 1:
            i, a, b = d[0]; out.append((k, i, a.pop(), b.pop()))
    return out


def edge(st, i, j):
    m = st['m']; k = i * (m - 1) + (j if j < i else j - 1)
    mb = np.asarray(st['mirror'][12 * k:12 * (k + 1)], np.float32); zb = np.asarray(st['z'][1 + 12 * j:1 + 12 * (j + 1)], np.float32)
    return np.concatenate([mb, zb, zb[4:] - mb[4:], [1.0 if grid_adjacent(i, j) else 0.0]])


def recv(st, i):
    return np.concatenate([[st['K'][i] / st['m']], np.asarray(st['z'][1 + 12 * i:1 + 12 * (i + 1)], np.float32)])


def swap_data(S):
    X, Y, G = [], [], []
    for g, st in enumerate(S):
        y0 = st['cands'][0]['cont']
        for k, i, a, b in swaps(st):
            eb, ea = edge(st, i, b), edge(st, i, a)
            X.append(np.concatenate([eb, ea, eb - ea, recv(st, i)])); Y.append(st['cands'][k]['cont'] - y0); G.append(g)
    return np.array(X, np.float32), np.array(Y, np.float32), np.array(G)


def pair_acc(pred, y, groups):
    num = den = 0; rhos = []; reg = []
    for g in np.unique(groups):
        m_ = groups == g; p, t = pred[m_], y[m_]
        dy = t[:, None] - t[None, :]; dp = p[:, None] - p[None, :]; mask = dy > 0
        num += (dp[mask] > 0).sum(); den += mask.sum()
        if np.ptp(p) > 0 and np.ptp(t) > 0:
            rhos.append(spearmanr(p, t).correlation)
        reg.append(float(t.max() - t[int(np.argmax(p))]))
    return dict(pair_acc=round(float(num / max(den, 1)), 4), spearman=round(float(np.nanmean(rhos)), 4) if rhos else None,
                argmax_regret=round(float(np.mean(reg)), 3), best_mean=round(float(np.mean([y[groups == g].max() for g in np.unique(groups)])), 3))


def flat_critic(D, S_by, pat):
    out = {}
    for mf in sorted(glob.glob(str(D / pat))):
        meta = torch.load(mf, weights_only=False); net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        res = {}
        for sp, S in S_by.items():
            P_all, Y_all, G_all, P_sw, Y_sw, G_sw = [], [], [], [], [], []
            for g, st in enumerate(S):
                an, y, feas, _ = predictions(meta, net, hn, st)
                P_all.append(an); Y_all.append(y); G_all.append(np.full(len(y), g))
                sw = swaps(st)
                if sw:
                    idx = [k for k, *_ in sw]; P_sw.append(an[idx]); Y_sw.append(y[idx]); G_sw.append(np.full(len(idx), g))
            res[sp] = dict(all=pair_acc(np.concatenate(P_all), np.concatenate(Y_all), np.concatenate(G_all)),
                           one_swaps=pair_acc(np.concatenate(P_sw), np.concatenate(Y_sw), np.concatenate(G_sw)))
        out[Path(mf).name] = res
    return out


def ridge(Xtr, Ytr, lam=1.0):
    mu, sd = Xtr.mean(0), Xtr.std(0) + 1e-6; Z = (Xtr - mu) / sd
    w = np.linalg.solve(Z.T @ Z + lam * np.eye(Z.shape[1]), Z.T @ (Ytr - Ytr.mean()))
    return lambda X: ((X - mu) / sd) @ w


def mlp(Xtr, Ytr, Xs, Ys, Gs, seed, epochs=60):
    torch.manual_seed(seed); mu, sd = Xtr.mean(0), Xtr.std(0) + 1e-6; ys = Ytr.std() + 1e-6
    net = nn.Sequential(nn.Linear(Xtr.shape[1], 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 1)); opt = torch.optim.Adam(net.parameters(), lr=1e-3, weight_decay=1e-4)
    T = lambda X: torch.as_tensor((X - mu) / sd); Xt, Yt = T(Xtr), torch.as_tensor(Ytr / ys); rng = np.random.default_rng(seed); best, saved = -1, None
    for ep in range(epochs):
        for b in torch.as_tensor(rng.permutation(len(Ytr))).split(512):
            loss = ((net(Xt[b]).squeeze(-1) - Yt[b]) ** 2).mean(); opt.zero_grad(); loss.backward(); opt.step()
        with torch.no_grad():
            acc = pair_acc(net(T(Xs)).squeeze(-1).numpy(), Ys, Gs)['pair_acc']
        if acc > best:
            best, saved = acc, {k: v.clone() for k, v in net.state_dict().items()}
    net.load_state_dict(saved)
    return lambda X: net(T(X)).squeeze(-1).detach().numpy()


def main(a):
    rep = {}
    for name, d in a.actor:
        D = Path(d); S_by = {'train': load([x for x in sorted(glob.glob(str(D / 'labels_train_*'))) if Path(x).is_dir()])[0],
                             'select': load([D / 'labels_select'])[0], 'dev': load([D / 'labels_dev'])[0]}
        r = dict(states={k: len(v) for k, v in S_by.items()})
        fam = [float(max(c['cont'] for c in st['cands']) - st['cands'][0]['cont']) for st in S_by['dev']]
        sw_best = [max([st['cands'][k]['cont'] - st['cands'][0]['cont'] for k, *_ in swaps(st)] or [0.0]) for st in S_by['dev']]
        zero = np.mean([np.mean([c['cont'] == st['cands'][0]['cont'] for c in st['cands'][1:]]) for st in S_by['dev']])
        r['D2'] = dict(dev_family_best_mean=round(float(np.mean(fam)), 3), dev_best_one_swap_mean=round(float(np.mean(sw_best)), 3),
                       one_swap_share_of_family_best=round(float(np.sum(sw_best) / max(np.sum(fam), 1e-9)), 3), dev_zero_gain_share=round(float(zero), 3),
                       one_swaps_per_state=round(float(np.mean([len(swaps(st)) for st in S_by['dev']])), 1))
        r['D1_flat_critic'] = flat_critic(D, S_by, a.flat)
        Xtr, Ytr, Gtr = swap_data(S_by['train']); Xs, Ys, Gs = swap_data(S_by['select']); Xd, Yd, Gd = swap_data(S_by['dev'])
        rr = ridge(Xtr, Ytr); r['D3'] = dict(n_train_swaps=int(len(Ytr)), ridge=dict(train=pair_acc(rr(Xtr), Ytr, Gtr), dev=pair_acc(rr(Xd), Yd, Gd)))
        for s in (0, 1, 2):
            f = mlp(Xtr, Ytr, Xs, Ys, Gs, s); r['D3'][f'mlp_s{s}'] = dict(train=pair_acc(f(Xtr), Ytr, Gtr), select=pair_acc(f(Xs), Ys, Gs), dev=pair_acc(f(Xd), Yd, Gd))
        rep[name] = r
        print(f'== {name}: states {r["states"]}')
        print(f'   D2 dev: family best {r["D2"]["dev_family_best_mean"]}, best ONE-SWAP {r["D2"]["dev_best_one_swap_mean"]} ({100 * r["D2"]["one_swap_share_of_family_best"]:.0f}% of the family best), '
              f'{r["D2"]["one_swaps_per_state"]} one-swaps/state, zero-gain share {r["D2"]["dev_zero_gain_share"]}')
        for ck, v in r['D1_flat_critic'].items():
            print(f'   D1 {ck:30s} pair-acc all: train {v["train"]["all"]["pair_acc"]} select {v["select"]["all"]["pair_acc"]} dev {v["dev"]["all"]["pair_acc"]} | '
                  f'one-swaps: train {v["train"]["one_swaps"]["pair_acc"]} dev {v["dev"]["one_swaps"]["pair_acc"]} (argmax regret {v["dev"]["one_swaps"]["argmax_regret"]} of best {v["dev"]["one_swaps"]["best_mean"]})')
        for k in ['ridge', 'mlp_s0', 'mlp_s1', 'mlp_s2']:
            v = r['D3'][k]
            print(f'   D3 {k:8s} one-swaps pair-acc: train {v["train"]["pair_acc"]} dev {v["dev"]["pair_acc"]} spearman {v["dev"]["spearman"]} | '
                  f'dev argmax regret {v["dev"]["argmax_regret"]} of best {v["dev"]["best_mean"]}')
    Path(a.out).write_text(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor', nargs=2, action='append', metavar=('NAME', 'DIR'), required=True)
    p.add_argument('--flat', default='selectors_v3/model_legal_bid_resp_s*.pt'); p.add_argument('--out', required=True)
    main(p.parse_args())
