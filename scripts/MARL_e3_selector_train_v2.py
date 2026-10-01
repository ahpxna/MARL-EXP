#!/usr/bin/env python3
"""E3 selector v2: optional RESPONSE HEAD (models/marl_e3_response.py) on top of MARL_e3_selector_train.py.

Variants (readiness audit P3 ablation axes, same data, same critic, same tuning allowance):
  sel_nobid     no bid, no head          (as v1)
  sel_bid       1-byte bid, no head      (as v1)
  sel_resp      head from LEGAL data only, no bid
  sel_bid_resp  bid + head               (the response-bid method; B2's design ported to the new actor)
The head predicts, per (candidate, receiver), whether the frozen actor's current action changes from its
action under the prefix; it is trained on the TRAIN split with the actor's actual joint actions stored
in the continuation labels (privileged training labels only), its epoch chosen on SELECT log-loss.  The
critic receives the predicted change probabilities (m values and their sum) as extra candidate features.
Epoch and tau of the critic are chosen on SELECT; DEV is reported, with the head's change-prediction
accuracy, precision and recall and the base rate (overall and on action-changing candidates).
v1 is unchanged (it is used by running chains).
"""
from __future__ import annotations
import argparse, glob, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, featurize, Net, choose
from models.marl_e3_response import resp_features, change_targets, RespNet, DIM

SOURCES = ['scripts/MARL_e3_selector_train_v2.py', 'scripts/MARL_e3_selector_train.py', 'models/marl_e3_response.py']


def train_head(F, R, T, seed, threads, epochs=4):
    torch.manual_seed(seed); torch.set_num_threads(threads); rng = np.random.default_rng(seed)
    Xtr = np.concatenate([x.reshape(-1, DIM) for x in R['train']]); Ytr = np.concatenate([y.reshape(-1) for y in T['train']])
    mu, sd = Xtr.mean(0), Xtr.std(0) + 1e-6
    Xs = np.concatenate([x.reshape(-1, DIM) for x in R['select']]); Ys = np.concatenate([y.reshape(-1) for y in T['select']])
    net = RespNet(); opt = torch.optim.Adam(net.parameters(), lr=1e-3); best, saved = np.inf, None
    Xt, Yt = torch.as_tensor((Xtr - mu) / sd), torch.as_tensor(Ytr); Xst, Yst = torch.as_tensor((Xs - mu) / sd), torch.as_tensor(Ys)
    for ep in range(epochs):
        for b in torch.as_tensor(rng.permutation(len(Ytr))).split(4096):
            loss = nn.functional.binary_cross_entropy_with_logits(net(Xt[b]), Yt[b]); opt.zero_grad(); loss.backward(); opt.step()
        with torch.no_grad():
            ll = float(nn.functional.binary_cross_entropy_with_logits(net(Xst), Yst))
        if ll < best:
            best, saved = ll, {k: v.clone() for k, v in net.state_dict().items()}
    net.load_state_dict(saved); net.eval()
    return net, mu, sd, best


def head_probs(net, mu, sd, X):
    with torch.no_grad():
        return torch.sigmoid(net(torch.as_tensor((X - mu) / sd))).numpy()


def head_metrics(P, T):
    p = np.concatenate([x.reshape(-1) for x in P]) > 0.5; y = np.concatenate([x.reshape(-1) for x in T]) > 0.5
    return dict(accuracy=float((p == y).mean()), base_rate=float(y.mean()), always_no_change=float((~y).mean()),
                precision=float((p & y).sum() / max(p.sum(), 1)), recall=float((p & y).sum() / max(y.sum(), 1)))


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    data, ck = {}, set()
    for sp, dirs in (('train', a.train), ('select', a.select), ('dev', a.dev)):
        data[sp], c = load([x for d in dirs for x in sorted(glob.glob(d)) if Path(x).is_dir()]); ck |= c
    if len(ck) != 1:
        raise SystemExit(f'labels come from different actor checkpoints: {ck}')
    gap_thr = np.quantile([b['gap'] for st in data['train'] for b in st['bid']], [0.25, 0.5, 0.75]).tolist()
    F = {sp: [featurize(st, a.bid, gap_thr) for st in data[sp]] for sp in data}
    head = None; hm = None
    if a.resp:
        R = {sp: [resp_features(st, a.bid, gap_thr) for st in data[sp]] for sp in data}
        T = {sp: [change_targets(st) for st in data[sp]] for sp in data}
        net_h, mu, sd, ll = train_head(F, R, T, a.seed, a.threads)
        P = {sp: [head_probs(net_h, mu, sd, x) for x in R[sp]] for sp in data}
        hm = dict(select_logloss=ll, dev=head_metrics(P['dev'], T['dev']))
        F = {sp: [(f[0], np.concatenate([f[1], p, p.sum(1, keepdims=True)], 1).astype(np.float32), f[2], f[3], f[4])
                  for f, p in zip(F[sp], P[sp])] for sp in data}
        head = dict(state=net_h.state_dict(), mu=mu, sd=sd)
        print(f'{a.name} s{a.seed}: head dev {hm["dev"]}', flush=True)
    C = np.stack([f[0] for f in F['train']]); cm, cs = C.mean(0), C.std(0) + 1e-6
    ys = float(np.std(np.concatenate([f[2] for f in F['train']])) + 1e-6)
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    net = Net(C.shape[1], F['train'][0][1].shape[1], a.hidden); opt = torch.optim.Adam(net.parameters(), lr=a.lr, weight_decay=1e-5)
    T_ = lambda f: (torch.as_tensor((f[0] - cm) / cs)[None], torch.as_tensor(f[1]))

    def anchored(sp):
        with torch.no_grad():
            return [(lambda p: p - p[0])(net(*T_(f)).numpy() * ys) for f in F[sp]]

    def pick_tau(pol):
        an = anchored('select'); grid = [-np.inf, 0.0] + sorted({float(x) for v in an for x in np.quantile(v[1:], [0.9, 0.99])})
        sc = [(np.mean([float(f[2][choose(v, f[3], f[4] if pol == 'R1' else np.ones_like(f[4]), t)]) for f, v in zip(F['select'], an)]), t) for t in grid]
        b = max(sc, key=lambda x: x[0]); return b[1], b[0]

    best, saved, best_ep = -np.inf, None, None; t0 = time.perf_counter()
    for ep in range(a.epochs):
        for k in rng.permutation(len(F['train'])):
            c, d = T_(F['train'][k]); loss = ((net(c, d) - torch.as_tensor(F['train'][k][2] / ys)) ** 2).mean()
            opt.zero_grad(); loss.backward(); opt.step()
        if ep % 4 == 3 or ep == a.epochs - 1:
            tau, metric = pick_tau('direct')
            if metric > best:
                best, saved, best_ep = metric, {k: v.clone() for k, v in net.state_dict().items()}, ep
            print(f'[{time.perf_counter() - t0:.0f}s] {a.name} s{a.seed} ep {ep}: select direct {metric:+.2f}', flush=True)
    net.load_state_dict(saved); res = {}
    for pol in ('direct', 'R1'):
        tau, sel = pick_tau(pol); an = anchored('dev')
        g = [float(f[2][choose(v, f[3], f[4] if pol == 'R1' else np.ones_like(f[4]), tau)]) for f, v in zip(F['dev'], an)]
        orc = [float(np.max(np.where(f[3] & (f[4] if pol == 'R1' else True), f[2], -np.inf))) for f in F['dev']]
        res[pol] = dict(tau=None if np.isinf(tau) else tau, select_metric=sel, dev_gain_mean=float(np.mean(g)), dev_gains=g,
                        dev_oracle_mean=float(np.mean(orc)), dev_oracle=orc, eps=[st['episode_id'] for st in data['dev']],
                        edit_rate=float(np.mean([x != 0 for x in g])))
    blob = dict(name=a.name, seed=a.seed, bid=a.bid, resp=a.resp, head=hm, best_epoch=best_ep, select_metric=best, gap_thresholds=gap_thr,
                actor_ckpt=ck.pop(), n_states={sp: len(F[sp]) for sp in F}, results=res, source_hashes=h0)
    (out / f'job_{a.name}_s{a.seed}.json').write_text(json.dumps(blob))
    torch.save(dict(state=saved, cm=cm, cs=cs, ys=ys, gap_thr=gap_thr, bid=a.bid, resp=a.resp, head=head, hidden=a.hidden,
                    dims=(C.shape[1], F['train'][0][1].shape[1]), tau={p: res[p]['tau'] for p in res}), out / f'model_{a.name}_s{a.seed}.pt')
    print(f'{a.name} s{a.seed}: dev direct {res["direct"]["dev_gain_mean"]:+.2f} (oracle {res["direct"]["dev_oracle_mean"]:+.2f}), '
          f'R1 {res["R1"]["dev_gain_mean"]:+.2f}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--train', nargs='+', required=True); p.add_argument('--select', nargs='+', required=True); p.add_argument('--dev', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--name', required=True); p.add_argument('--bid', action='store_true'); p.add_argument('--resp', action='store_true')
    p.add_argument('--seed', type=int, default=0); p.add_argument('--epochs', type=int, default=40); p.add_argument('--lr', type=float, default=1e-3)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
