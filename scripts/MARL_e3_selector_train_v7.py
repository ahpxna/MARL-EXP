#!/usr/bin/env python3
"""E3 critic v7 (29/09): OFFLINE LEARNABILITY DIAGNOSTIC for the auditor's test 2, not a deployable selector.
Which component of the 3-step label can the legal critic learn: the immediate gain g1 = cont_1 - cont_1(prefix), the
delayed part g3 - g1, or g3 itself?

Identical to v6 --loss mse (v3's legal_bid_resp path: features, bid, response head, Net, Adam lr 1e-3 wd 1e-5, 40
epochs, one step per train state per epoch in the same permutation order, MSE over every candidate), except:
  --target {g3,g1,delayed}  the regression target (and its scale ys, the train std of that target);
  SAFE NORMALISER (ledger L-65): every feature whose train std is < 1e-6 is centred but not scaled (std set to 1), in
                  the critic context AND the response head input (v3 divides by std + 1e-6, which maps a changed
                  constant feature to ~1e6).  The same cm/cs are saved with the weights.
  epoch selection:  every 4 epochs, by the SELECT mean tie-half pair accuracy against the model's OWN target over the
                  feasible set (+74 B, prefix included); no tau, no choice rule.
Reported (description, not a method claim): per evaluation epoch the TRAIN / SELECT / DEV pair accuracy against the own
target; at the chosen epoch the DEV per-state pair accuracy against g3, g1 and delayed, and the within-state Spearman.
Self-test before any data (abort on failure): the safe normaliser leaves a constant feature finite (|z| = |x - mean|)
and matches v3 on non-constant features; the three targets satisfy g3 = g1 + delayed on a real state.
"""
from __future__ import annotations
import argparse, glob, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, featurize, Net
from scripts.MARL_e3_selector_train_v3 import head_probs, head_metrics, DIM
from scripts.MARL_e3_ranking_diag_v2 import pair_acc
from models.marl_e3_response import resp_features, change_targets, RespNet

SOURCES = ['scripts/MARL_e3_selector_train_v7.py', 'scripts/MARL_e3_selector_train_v3.py', 'scripts/MARL_e3_selector_train.py',
           'scripts/MARL_e3_ranking_diag_v2.py', 'models/marl_e3_response.py']


def safe_scale(X):
    mu, sd = X.mean(0), X.std(0)
    return mu, np.where(sd < 1e-6, 1.0, sd).astype(X.dtype)


def targets(st):
    c0 = st['cands'][0]
    g3 = np.array([c['cont'] - c0['cont'] for c in st['cands']], np.float32)
    g1 = np.array([c['cont_1'] - c0['cont_1'] for c in st['cands']], np.float32)
    return dict(g3=g3, g1=g1, delayed=g3 - g1)


def train_head_safe(R, T, seed, threads, epochs=4):
    """v3's train_head with the safe normaliser (the only change)."""
    torch.manual_seed(seed); torch.set_num_threads(threads); rng = np.random.default_rng(seed)
    Xtr = np.concatenate([x.reshape(-1, DIM) for x in R['train']]); Ytr = np.concatenate([y.reshape(-1) for y in T['train']])
    mu, sd = safe_scale(Xtr)
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


def selftest(st):
    X = np.array([[0.0, 1.0], [0.0, 3.0], [0.0, 5.0]], np.float32); mu, sd = safe_scale(X)
    z = (np.array([1.0, 3.0], np.float32) - mu) / sd
    assert abs(z[0] - 1.0) < 1e-6, f'constant feature not left unscaled: {z}'
    assert abs(sd[1] - X[:, 1].std()) < 1e-6, 'non-constant feature scaled differently from v3'
    g = targets(st); assert np.allclose(g['g3'], g['g1'] + g['delayed']) and g['g3'][0] == 0 and g['g1'][0] == 0, 'target split broken'
    print('selftest PASS (safe normaliser finite on a changed constant feature, v3 scale otherwise; g3 = g1 + delayed, prefix gain 0)', flush=True)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    data, ck = {}, set()
    for sp, dirs in (('train', a.train), ('select', a.select), ('dev', a.dev)):
        data[sp], c = load([x for d in dirs for x in sorted(glob.glob(d)) if Path(x).is_dir()]); ck |= c
    if len(ck) != 1:
        raise SystemExit(f'labels come from different actor checkpoints: {ck}')
    selftest(data['train'][0])
    gap_thr = np.quantile([b['gap'] for st in data['train'] for b in st['bid']], [0.25, 0.5, 0.75]).tolist()
    F = {sp: [featurize(st, a.bid, gap_thr) for st in data[sp]] for sp in data}
    TG = {sp: [targets(st) for st in data[sp]] for sp in data}
    OKs = {sp: [np.concatenate([[True], f[3][1:]]) for f in F[sp]] for sp in data}
    head = None; hm = None
    if a.resp:
        R = {sp: [resp_features(st, a.bid, gap_thr) for st in data[sp]] for sp in data}
        T = {sp: [change_targets(st) for st in data[sp]] for sp in data}
        net_h, mu, sd, ll = train_head_safe(R, T, a.seed, a.threads)
        P = {sp: [head_probs(net_h, mu, sd, x) for x in R[sp]] for sp in data}
        hm = dict(select_logloss=ll, dev=head_metrics(P['dev'], T['dev']))
        F = {sp: [(f[0], np.concatenate([f[1], p, p.sum(1, keepdims=True)], 1).astype(np.float32), f[2], f[3], f[4])
                  for f, p in zip(F[sp], P[sp])] for sp in data}
        head = dict(state=net_h.state_dict(), mu=mu, sd=sd)
        print(f'{a.name} s{a.seed}: head dev {hm["dev"]}', flush=True)
    C = np.stack([f[0] for f in F['train']]); cm, cs = safe_scale(C)
    Y = {sp: [tg[a.target] for tg in TG[sp]] for sp in data}
    ys = float(np.std(np.concatenate(Y['train'])) + 1e-6)
    T_ = lambda f: (torch.as_tensor((f[0] - cm) / cs)[None], torch.as_tensor(f[1]))
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    net = Net(C.shape[1], F['train'][0][1].shape[1], a.hidden); opt = torch.optim.Adam(net.parameters(), lr=a.lr, weight_decay=1e-5)

    def scores(sp):
        with torch.no_grad():
            return [net(*T_(f)).numpy() for f in F[sp]]

    def pa(sp, sc, tgt):
        return [pair_acc(s[ok], TG[sp][k][tgt][ok])[0] for k, (s, ok) in enumerate(zip(sc, OKs[sp]))]

    curve = []; best, saved, best_ep = -np.inf, None, None; t0 = time.perf_counter()
    tr_sub = np.random.default_rng(1234).choice(len(F['train']), size=min(200, len(F['train'])), replace=False)
    for ep in range(a.epochs):
        for k in rng.permutation(len(F['train'])):
            c, d = T_(F['train'][k]); u = net(c, d)
            loss = ((u - torch.as_tensor(Y['train'][k] / ys)) ** 2).mean(); opt.zero_grad(); loss.backward(); opt.step()
        if ep % 4 == 3 or ep == a.epochs - 1:
            s_sel, s_dev = scores('select'), scores('dev')
            with torch.no_grad():
                s_tr = [net(*T_(F['train'][k])).numpy() for k in tr_sub]
            tr = float(np.nanmean([pair_acc(s[OKs['train'][k]], TG['train'][k][a.target][OKs['train'][k]])[0] for s, k in zip(s_tr, tr_sub)]))
            sel = float(np.nanmean(pa('select', s_sel, a.target))); dev = float(np.nanmean(pa('dev', s_dev, a.target)))
            curve.append(dict(epoch=ep, train_pa=tr, select_pa=sel, dev_pa_description_only=dev))
            if sel > best:
                best, saved, best_ep = sel, {k: v.clone() for k, v in net.state_dict().items()}, ep
            print(f'[{time.perf_counter() - t0:.0f}s] {a.name} s{a.seed} target {a.target} ep {ep}: pair acc train {tr:.4f} select {sel:.4f} dev {dev:.4f}', flush=True)
    net.load_state_dict(saved); s_dev = scores('dev')
    dev = {tgt: pa('dev', s_dev, tgt) for tgt in ('g3', 'g1', 'delayed')}
    rho = {tgt: [float(spearmanr(s[ok], TG['dev'][k][tgt][ok]).correlation) if np.ptp(TG['dev'][k][tgt][ok]) > 0 and np.ptp(s[ok]) > 0 else None
                 for k, (s, ok) in enumerate(zip(s_dev, OKs['dev']))] for tgt in dev}
    blob = dict(name=a.name, seed=a.seed, target=a.target, bid=a.bid, resp=a.resp, normaliser='safe (std < 1e-6 -> 1)', lr=a.lr, head=hm,
                best_epoch=best_ep, select_pa=best, curve=curve, dev_pa=dev, dev_spearman=rho,
                dev_episodes=[st['episode_id'] for st in data['dev']], dev_traffic_seeds=[st['traffic_seed'] for st in data['dev']],
                actor_ckpt=ck.pop(), n_states={sp: len(F[sp]) for sp in F}, evidence_class='offline learnability diagnostic (not a selector)',
                source_hashes=h0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / f'job_{a.name}_{a.target}_s{a.seed}.json').write_text(json.dumps(blob))
    torch.save(dict(state=saved, cm=cm, cs=cs, ys=ys, gap_thr=gap_thr, bid=a.bid, resp=a.resp, head=head, hidden=a.hidden, target=a.target,
                    normaliser='safe', dims=(C.shape[1], F['train'][0][1].shape[1])), out / f'model_{a.name}_{a.target}_s{a.seed}.pt')
    print(f'{a.name} s{a.seed} target {a.target}: select pa {best:.4f} (ep {best_ep}) | DEV pa g3 {np.nanmean(dev["g3"]):.4f} g1 {np.nanmean(dev["g1"]):.4f} '
          f'delayed {np.nanmean(dev["delayed"]):.4f}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--train', nargs='+', required=True); p.add_argument('--select', nargs='+', required=True); p.add_argument('--dev', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--name', required=True); p.add_argument('--bid', action='store_true'); p.add_argument('--resp', action='store_true')
    p.add_argument('--target', choices=['g3', 'g1', 'delayed'], required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--epochs', type=int, default=40); p.add_argument('--lr', type=float, default=1e-3)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
