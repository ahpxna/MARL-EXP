#!/usr/bin/env python3
"""E3 selector v6 (28/09 19:3x, PROTOCOL_E3_DFL_20260928.md): v3 with ONE change available, the training objective.

  --loss mse       v3's value regression, unchanged (per-state mean of (score - gain/ys)^2 over EVERY candidate);
  --loss mse_feas  the same MSE over the FEASIBLE set only (prefix always included): isolates the candidate set;
  --loss dfl       decision loss: the expected gain of the scorer's own softmax choice over the FEASIBLE set (prefix
                   always included), L_s = - sum_c softmax(u/T)_c * gain_c / ys.
Tuning (Amendment 1 of the protocol, 20:08): every configuration in --lrs x --temps (T only for dfl; the primary
round uses T = 1 fixed) is trained with the same seed and permutation order; the configuration, epoch and tau are
chosen on SELECT by the same metric as v3 (ties: the first configuration in the given order).
Everything else is v3's legal_bid_resp path: features, bid, response head (v3's train_head on TRAIN, epoch on SELECT
log-loss), Net, Adam (lr, weight decay), epochs, one step per train state per epoch in the same permutation order,
evaluation every 4 epochs, the tau grid with +/-inf, the saved checkpoint format (so closed loop v5, paired eval and
diagnostic v3 read it unchanged).  No privileged inputs (--priv-joint is not offered).
Per-configuration results (SELECT metric, epoch, tau, and DEV of that configuration's own best checkpoint including
dev_chosen, used by the runner's v3-reproduction self-check) are saved as a description only; the arm is the SELECT
choice.  Self-test before any data (abort on failure): the decision loss equals -sum p*y, ignores
infeasible candidates (zero gradient), and a few gradient steps raise the probability of the best feasible
candidate; the feasible MSE ignores infeasible candidates.  v3 is unchanged; with --loss mse at lr 1e-3 this trainer
must reproduce a v3 job (checked by RUN_marl_e3_dfl.sh).
"""
from __future__ import annotations
import argparse, glob, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, featurize, Net, choose
from scripts.MARL_e3_selector_train_v3 import train_head, head_probs, head_metrics
from models.marl_e3_response import resp_features, change_targets

SOURCES = ['scripts/MARL_e3_selector_train_v6.py', 'scripts/MARL_e3_selector_train_v3.py', 'scripts/MARL_e3_selector_train_v2.py',
           'scripts/MARL_e3_selector_train.py', 'models/marl_e3_response.py']


def dfl_loss(u, y, ok, temp):
    """u: scores (n,), y: gains/ys (n,), ok: feasible mask with ok[0] = True; returns -sum_c p_c y_c over ok."""
    p = torch.softmax(u[ok] / temp, 0)
    return -(p * y[ok]).sum()


def mse_feas_loss(u, y, ok):
    return ((u[ok] - y[ok]) ** 2).mean()


def selftest():
    y = torch.tensor([0.0, 1.0, -1.0, 5.0]); ok = torch.tensor([True, True, True, False])
    u = torch.tensor([0.2, -0.1, 0.4, 3.0], requires_grad=True)
    L = dfl_loss(u, y, ok, 1.0); p = torch.softmax(u[:3].detach(), 0)
    assert abs(float(L.detach()) + float((p * y[:3]).sum())) < 1e-6, 'loss != -sum p y'
    L.backward(); assert float(u.grad[3]) == 0.0, 'infeasible candidate received gradient'
    w = torch.zeros(4, requires_grad=True); opt = torch.optim.SGD([w], lr=0.5)
    for _ in range(50):
        opt.zero_grad(); dfl_loss(w, y, ok, 1.0).backward(); opt.step()
    q = torch.softmax(w[:3].detach(), 0)
    assert float(q[1]) > 0.9, f'best feasible candidate not favoured: {q.tolist()}'
    v = torch.tensor([0.1, 0.2, 0.3, 9.0], requires_grad=True); mse_feas_loss(v, y, ok).backward()
    assert float(v.grad[3]) == 0.0, 'feasible MSE gave gradient to an infeasible candidate'
    print('selftest PASS (loss = -sum p y; infeasible candidates get no gradient in DFL or feasible MSE; gradient steps favour the best feasible candidate)', flush=True)


def main(a):
    selftest()
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
    T_ = lambda f: (torch.as_tensor((f[0] - cm) / cs)[None], torch.as_tensor(f[1]))
    OK = [torch.as_tensor(np.concatenate([[True], f[3][1:]])) for f in F['train']]       # feasible, prefix always in
    YT = [torch.as_tensor(f[2] / ys) for f in F['train']]

    def run(lr, temp):
        """One training run (v3's loop at learning rate lr; the loss is a.loss, at temperature temp for dfl)."""
        torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
        net = Net(C.shape[1], F['train'][0][1].shape[1], a.hidden); opt = torch.optim.Adam(net.parameters(), lr=lr, weight_decay=1e-5)

        def anchored(sp):
            with torch.no_grad():
                return [(lambda p: p - p[0])(net(*T_(f)).numpy() * ys) for f in F[sp]]

        def pick_tau(pol):
            an = anchored('select'); grid = [-np.inf, 0.0] + sorted({float(x) for v in an for x in np.quantile(v[1:], [0.9, 0.99])}) + [np.inf]
            sc = [(np.mean([float(f[2][choose(v, f[3], f[4] if pol == 'R1' else np.ones_like(f[4]), t)]) for f, v in zip(F['select'], an)]), t) for t in grid]
            b = max(sc, key=lambda x: x[0]); return b[1], b[0]

        best, saved, best_ep = -np.inf, None, None; t0 = time.perf_counter()
        for ep in range(a.epochs):
            for k in rng.permutation(len(F['train'])):
                c, d = T_(F['train'][k]); u = net(c, d)
                if a.loss == 'mse':
                    loss = ((u - torch.as_tensor(F['train'][k][2] / ys)) ** 2).mean()
                elif a.loss == 'mse_feas':
                    loss = mse_feas_loss(u, YT[k], OK[k])
                else:
                    loss = dfl_loss(u, YT[k], OK[k], temp)
                opt.zero_grad(); loss.backward(); opt.step()
            if ep % 4 == 3 or ep == a.epochs - 1:
                tau, metric = pick_tau('direct')
                if metric > best:
                    best, saved, best_ep = metric, {k: v.clone() for k, v in net.state_dict().items()}, ep
                print(f'[{time.perf_counter() - t0:.0f}s] {a.name} s{a.seed} lr {lr} T {temp} ep {ep}: select direct {metric:+.2f}', flush=True)
        net.load_state_dict(saved); res = {}
        for pol in ('direct', 'R1'):
            tau, sel = pick_tau(pol); an = anchored('dev')
            ch = [choose(v, f[3], f[4] if pol == 'R1' else np.ones_like(f[4]), tau) for f, v in zip(F['dev'], an)]
            g = [float(f[2][j]) for f, j in zip(F['dev'], ch)]
            orc = [float(np.max(np.where(f[3] & (f[4] if pol == 'R1' else True), f[2], -np.inf))) for f in F['dev']]
            ed = [j != 0 for j in ch]; harm = [x < 0 for x, e in zip(g, ed) if e]
            res[pol] = dict(tau=('+inf' if tau > 0 else '-inf') if np.isinf(tau) else float(tau), select_metric=sel, dev_gain_mean=float(np.mean(g)),
                            dev_gains=g, dev_chosen=[int(j) for j in ch], dev_oracle_mean=float(np.mean(orc)), dev_oracle=orc,
                            eps=[st['episode_id'] for st in data['dev']], edit_rate=float(np.mean(ed)),
                            harmful_edit_rate=float(np.mean(harm)) if harm else None,
                            gain_given_edit=float(np.mean([x for x, e in zip(g, ed) if e])) if any(ed) else None)
        return dict(select_metric=best, best_epoch=best_ep, state=saved, results=res)

    temps = [None] if a.loss != 'dfl' else a.temps
    configs = [(lr, t) for lr in a.lrs for t in temps]
    runs = [run(lr, t) for lr, t in configs]
    best_i = max(range(len(configs)), key=lambda q: (runs[q]['select_metric'], -q))   # SELECT only; ties -> the first configuration
    (lr_best, t_best), R_ = configs[best_i], runs[best_i]
    per_c = {f'lr={lr}' + ('' if t is None else f',T={t}'): dict(lr=lr, temperature=t, select_metric=r['select_metric'], best_epoch=r['best_epoch'],
                 dev_gain_mean_description_only=r['results']['direct']['dev_gain_mean'], tau=r['results']['direct']['tau'],
                 edit_rate=r['results']['direct']['edit_rate'], dev_chosen=r['results']['direct']['dev_chosen']) for (lr, t), r in zip(configs, runs)}
    blob = dict(name=a.name, seed=a.seed, bid=a.bid, resp=a.resp, priv_joint=False, loss=a.loss, lr=lr_best, temperature=t_best, lrs=a.lrs, temps=temps,
                per_config=per_c,
                head=hm, best_epoch=R_['best_epoch'], select_metric=R_['select_metric'], gap_thresholds=gap_thr,
                actor_ckpt=ck.pop(), n_states={sp: len(F[sp]) for sp in F}, results=R_['results'], source_hashes=h0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / f'job_{a.name}_s{a.seed}.json').write_text(json.dumps(blob))
    torch.save(dict(state=R_['state'], cm=cm, cs=cs, ys=ys, gap_thr=gap_thr, bid=a.bid, resp=a.resp, priv_joint=False, tau_format='v3 strings', head=head, hidden=a.hidden,
                    dims=(C.shape[1], F['train'][0][1].shape[1]), tau={p: R_['results'][p]['tau'] for p in R_['results']}, loss=a.loss, lr=lr_best, temperature=t_best),
               out / f'model_{a.name}_s{a.seed}.pt')
    r = R_['results']['direct']; print(f'{a.name} s{a.seed} ({a.loss}, lr {lr_best}, T {t_best}): dev direct {r["dev_gain_mean"]:+.2f} (oracle {r["dev_oracle_mean"]:+.2f}) '
                                      f'edit {r["edit_rate"]:.2f} harm|edit {r["harmful_edit_rate"]} tau {r["tau"]} | R1 {R_["results"]["R1"]["dev_gain_mean"]:+.2f}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--train', nargs='+', required=True); p.add_argument('--select', nargs='+', required=True); p.add_argument('--dev', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--name', required=True); p.add_argument('--bid', action='store_true'); p.add_argument('--resp', action='store_true')
    p.add_argument('--loss', choices=['mse', 'mse_feas', 'dfl'], required=True); p.add_argument('--temps', type=float, nargs='+', default=[1.0])
    p.add_argument('--seed', type=int, default=0); p.add_argument('--epochs', type=int, default=40); p.add_argument('--lrs', type=float, nargs='+', default=[1e-3])
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
