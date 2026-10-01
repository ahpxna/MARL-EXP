#!/usr/bin/env python3
"""Route 3 (MARL_DEEP_RESEARCH_20260929.md): a STRUCTURED scheduler critic on the existing E3 labels.  Offline only.

Every E3 critic so far (v1-v8, legal and privileged) concatenates a global context embedding with a state-independent
candidate matrix, so the value of one edit (receiver r adds sender j, drops sender k) must be learned from a flat
1,180-dim context (ledger L-82 item 3).  The literature (McClellan et al. NeurIPS 2024; Weltevrede et al. 2026) says
value generalisation depends on respecting the task's symmetries.  This critic is PAIR-SHARED: a candidate's score is
the sum over its edits of ONE function phi of the edit's own features,

    edit (r, +j, -k) -> [z_j, z_k, mirror(r<-j), mirror(r<-k), z_r (the scheduler's last packet of r), static(r,j),
                         static(r,k) (the actor adapter's down/upstream slots), K_r/m, bid_r (p1, p2, gap bin), time]

(adds and drops of a receiver paired in sorted order), prefix = no edits = 0.  The same weights serve every receiver and
sender; geometry enters only through the static slots.  Inputs are the scheduler's legal inputs (the same ones v3 uses);
with --priv the edit also gets the receiver's induced action at t (one-hot) and a changed flag: a DIAGNOSTIC arm.
Normaliser: v8's floored scale (std < 1e-6 -> 1, else max(std, 0.05)).  Loss: v3's MSE on gain / ys over every
candidate.  Epoch chosen on SELECT tie-half pair accuracy over the feasible (+74 B) set; tau for the DEV decision chosen
on SELECT by mean realised gain over the grid {-inf, 0, q90, q99, +inf} (v3's rule, +inf included).
Reported: TRAIN / SELECT / DEV pair accuracy, DEV Spearman, DEV realised gain and edit rate of the tau rule and of the
argmax.  Self-test: the edit decomposition of every candidate reproduces its delivery sets exactly.
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
from scripts.MARL_e3_selector_train import load, CAP, BID_BYTES
from scripts.MARL_e3_ranking_diag_v2 import pair_acc

SOURCES = ['scripts/MARL_e3_pair_critic_train.py', 'scripts/MARL_e3_selector_train.py', 'scripts/MARL_e3_ranking_diag_v2.py']
FLOOR = 0.05


def static_table(scratch):
    from scripts.MARL_e3_actor_train import Scenarios
    from models.marl_comm_actor import CommAdapter
    from scripts.MARL_hetero_pilot_collect import N_DEC
    sc = Scenarios(Path(scratch)); env, topo, _, _ = sc.env(501, 8.0); ad = CommAdapter(topo, N_DEC, env.action_interval)
    m = env.n_agents; T = np.zeros((m, m, 8), np.float32)
    for (i, j), f in ad.static.items():
        T[i, j] = f
    return T


def zblk(st, j):
    return np.asarray(st['z'][1 + 12 * j: 1 + 12 * (j + 1)], np.float32)


def mblk(st, i, j):
    m = st['m']; k = i * (m - 1) + (j if j < i else j - 1)
    return np.asarray(st['mirror'][12 * k: 12 * (k + 1)], np.float32)


def edits(P, S):
    """Per receiver: sorted added and dropped senders, paired in order; returns [(r, j_add, k_drop)]."""
    out = []
    for r, (p, s) in enumerate(zip(P, S)):
        add = sorted(set(s) - set(p)); drop = sorted(set(p) - set(s))
        if len(add) != len(drop):
            raise ValueError('a candidate changes a receiver set size')
        out += [(r, j, k) for j, k in zip(add, drop)]
    return out


def edit_feat(st, T, gap_thr, r, j, k, priv=None):
    b = st['bid'][r]; gb = int(np.searchsorted(gap_thr, b['gap']))
    f = [zblk(st, j), zblk(st, k), mblk(st, r, j), mblk(st, r, k), zblk(st, r), T[r, j], T[r, k], [st['K'][r] / st['m']],
         np.eye(9, dtype=np.float32)[b['p1']], np.eye(9, dtype=np.float32)[b['p2']], np.eye(4, dtype=np.float32)[gb], [st['z'][0]]]
    if priv is not None:
        f += [np.eye(9, dtype=np.float32)[priv[0]], [float(priv[0] != priv[1])]]
    return np.concatenate([np.asarray(x, np.float32) for x in f])


def featurize(st, T, gap_thr, priv):
    P = st['cands'][0]['sets']; j0 = st['cands'][0]['joint']; rows, owner = [], []
    for ci, c in enumerate(st['cands']):
        for (r, j, k) in edits(P, c['sets']):
            rows.append(edit_feat(st, T, gap_thr, r, j, k, (c['joint'][r], j0[r]) if priv else None)); owner.append(ci)
    n = len(st['cands']); y = np.array([c['cont'] for c in st['cands']], np.float32) - st['cands'][0]['cont']
    feas = np.array([ci == 0 or c['bytes'] <= st['b0'] + CAP - BID_BYTES for ci, c in enumerate(st['cands'])])
    X = np.stack(rows) if rows else np.zeros((0, 1), np.float32)
    return X, np.array(owner, np.int64), n, y, feas


def selftest(st):
    P = st['cands'][0]['sets']
    for c in st['cands']:
        S = [set(p) for p in P]
        for r, j, k in edits(P, c['sets']):
            S[r].discard(k); S[r].add(j)
        if [sorted(s) for s in S] != [sorted(s) for s in c['sets']]:
            raise SystemExit('SELF-TEST FAIL: the edit decomposition does not reproduce a candidate')
    print('selftest PASS (edit decomposition reproduces every candidate of the first train state)', flush=True)


class Phi(nn.Module):
    def __init__(self, d, h=128):
        super().__init__()
        self.f = nn.Sequential(nn.Linear(d, h), nn.ReLU(), nn.Linear(h, h), nn.ReLU(), nn.Linear(h, 1))

    def forward(self, X, owner, n):
        e = self.f(X).squeeze(-1)
        return torch.zeros(n).index_add(0, owner, e)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    data, ck = {}, set()
    for sp, dirs in (('train', a.train), ('select', a.select), ('dev', a.dev)):
        data[sp], c = load([x for d in dirs for x in sorted(glob.glob(d)) if Path(x).is_dir()]); ck |= c
    if len(ck) != 1:
        raise SystemExit(f'labels come from different actor checkpoints: {ck}')
    selftest(data['train'][0])
    T = static_table(a.scratch)
    gap_thr = np.quantile([b['gap'] for st in data['train'] for b in st['bid']], [0.25, 0.5, 0.75]).tolist()
    F = {sp: [featurize(st, T, gap_thr, a.priv) for st in data[sp]] for sp in data}
    Xall = np.concatenate([f[0] for f in F['train'] if len(f[0])]); mu = Xall.mean(0); sd = Xall.std(0)
    sd = np.where(sd < 1e-6, 1.0, np.maximum(sd, FLOOR)).astype(np.float32)
    ys = float(np.std(np.concatenate([f[3] for f in F['train']])) + 1e-6)
    TT = lambda f: (torch.as_tensor((f[0] - mu) / sd), torch.as_tensor(f[1]), f[2])
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    net = Phi(Xall.shape[1], a.hidden); opt = torch.optim.Adam(net.parameters(), lr=a.lr, weight_decay=1e-5)

    def scores(sp):
        with torch.no_grad():
            return [net(*TT(f)).numpy() * ys for f in F[sp]]

    def pa(sp, sc):
        return [pair_acc(s[f[4]], f[3][f[4]])[0] for s, f in zip(sc, F[sp])]

    def decide(sp, sc, tau):
        g = []; e = []
        for s, f in zip(sc, F[sp]):
            v = np.where(f[4], s, -np.inf); v[0] = 0.0; j = int(np.argmax(v)); j = j if v[j] > tau else 0
            g.append(float(f[3][j])); e.append(j != 0)
        return float(np.mean(g)), float(np.mean(e))

    curve = []; best, saved, best_ep = -np.inf, None, None; t0 = time.perf_counter()
    sub = np.random.default_rng(1234).choice(len(F['train']), size=min(200, len(F['train'])), replace=False)
    for ep in range(a.epochs):
        for k in rng.permutation(len(F['train'])):
            X, o, n = TT(F['train'][k])
            u = net(X, o, n); loss = ((u - torch.as_tensor(F['train'][k][3] / ys)) ** 2).mean()
            opt.zero_grad(); loss.backward(); opt.step()
        if ep % 4 == 3 or ep == a.epochs - 1:
            ssel, sdev = scores('select'), scores('dev')
            with torch.no_grad():
                str_ = [net(*TT(F['train'][k])).numpy() for k in sub]
            tr = float(np.nanmean([pair_acc(s[F['train'][k][4]], F['train'][k][3][F['train'][k][4]])[0] for s, k in zip(str_, sub)]))
            sel = float(np.nanmean(pa('select', ssel))); dev = float(np.nanmean(pa('dev', sdev)))
            curve.append(dict(epoch=ep, train_pa=tr, select_pa=sel, dev_pa_description_only=dev))
            if sel > best:
                best, saved, best_ep = sel, {k: v.clone() for k, v in net.state_dict().items()}, ep
            print(f'[{time.perf_counter() - t0:.0f}s] pair critic s{a.seed} priv={a.priv} ep {ep}: pair acc train {tr:.4f} select {sel:.4f} dev {dev:.4f}', flush=True)
    net.load_state_dict(saved); ssel, sdev = scores('select'), scores('dev')
    grid = [-np.inf, 0.0] + sorted({float(x) for s in ssel for x in np.quantile(s[1:], [0.9, 0.99])}) + [np.inf]
    tau = max(grid, key=lambda t: (decide('select', ssel, t)[0], -abs(t) if np.isfinite(t) else -1e9))
    dev_pa = pa('dev', sdev)
    rho = [spearmanr(s[f[4]], f[3][f[4]]).correlation for s, f in zip(sdev, F['dev']) if np.ptp(f[3][f[4]]) > 0 and np.ptp(s[f[4]]) > 0]
    g_tau, e_tau = decide('dev', sdev, tau); g_arg, _ = decide('dev', sdev, -np.inf)
    orc = float(np.mean([np.max(f[3][f[4]]) for f in F['dev']]))
    blob = dict(seed=a.seed, priv=a.priv, lr=a.lr, best_epoch=best_ep, select_pa=best, curve=curve, dev_pa=dev_pa, dev_pa_mean=float(np.nanmean(dev_pa)),
                dev_spearman_mean=float(np.nanmean(rho)), tau=('+inf' if tau > 0 else '-inf') if np.isinf(tau) else float(tau),
                dev_gain_tau=g_tau, dev_edit_rate_tau=e_tau, dev_gain_argmax=g_arg, dev_oracle=orc,
                dev_traffic_seeds=[st['traffic_seed'] for st in data['dev']], actor_ckpt=ck.pop(), n_states={sp: len(F[sp]) for sp in F},
                evidence_class='offline development diagnostic', source_hashes=h0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    tag = 'priv' if a.priv else 'legal'
    (out / f'job_pair_{tag}_s{a.seed}.json').write_text(json.dumps(blob))
    torch.save(dict(state=saved, mu=mu, sd=sd, ys=ys, gap_thr=gap_thr, priv=a.priv, hidden=a.hidden, dim=int(Xall.shape[1]), tau=blob['tau']),
               out / f'model_pair_{tag}_s{a.seed}.pt')
    print(f'pair critic {tag} s{a.seed}: select pa {best:.4f} (ep {best_ep}) | DEV pa {blob["dev_pa_mean"]:.4f} spearman {blob["dev_spearman_mean"]:+.3f} | '
          f'DEV gain tau {g_tau:+.2f} (edit {e_tau:.2f}, tau {blob["tau"]}) argmax {g_arg:+.2f} oracle {orc:+.2f}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--train', nargs='+', required=True); p.add_argument('--select', nargs='+', required=True); p.add_argument('--dev', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--scratch', required=True, help='a scratch dir for building the topology once')
    p.add_argument('--priv', action='store_true'); p.add_argument('--seed', type=int, default=0); p.add_argument('--epochs', type=int, default=40)
    p.add_argument('--lr', type=float, default=1e-3); p.add_argument('--hidden', type=int, default=128); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
