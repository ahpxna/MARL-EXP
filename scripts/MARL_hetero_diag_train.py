#!/usr/bin/env python3
"""One bounded learner diagnostic (MARL_SCOPE_AFTER_CHEAP_TESTS, "Bounded next decision").

Same labels, split, frozen actor and candidate budget as the Step 3 pilot; TRAIN/VAL only
(seeds 61-64 are not read).  Target: paired gain Delta(S;P) = f(S) - f(P) within each
(context, K) group.  Model/threshold selection uses an INNER split of the training seeds
(fit 41-46, select 47-48); validation seeds 51-52 are used only for the final comparison.

Predictors, each producing a predicted gain for every labelled candidate:
  mlp_public      MLP on [z, K/m, M(S)]                      (the pilot critic's inputs)
  mlp_history     MLP on [z, legal receiver mirror, K/m, M(S)]
  ridge_edge_*    context-by-profile interaction model, ridge:
                  Delta ~ sum_ij (M_ij(S) - M_ij(P)) * (beta_ij + theta . c_ij(z)),
                  c_ij = [scheduler's latest packet of j, K_i/m, time] (+ mirror pair (i,j))
  mlp_joint_priv  PRIVILEGED CONTROL: [z, current summaries, one-hot joint action of S and of P]
Selection among labelled candidates under each cap (+0, +28, +56 bytes over the prefix, none):
  repair_R1  argmax predicted gain over R<=1 candidates, KEEP THE PREFIX unless it is > 0
  direct     same predictor over ALL labelled candidates, same rule
  oracle_*   true argmax (reference)
Reported per validation episode: realised gain, harmful-edit rate, edit rate, extra bytes.
"""
from __future__ import annotations
import argparse, copy, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import prefix_sets, profile_cost

SOURCES = ['scripts/MARL_hetero_diag_train.py', 'models/marl_hetero_selector.py']
CAPS = [0, 28, 56, None]
INNER_FIT = {41, 42, 43, 44, 45, 46}; INNER_SEL = {47, 48}


def unmask(x, m):
    return frozenset(j for j in range(m) if (x >> j) & 1)


def load(labels, mirror):
    L = [json.loads(l) for l in gzip.open(Path(labels) / 'labels.jsonl.gz', 'rt')]
    Mi = {(r['episode_id'], r['t']): r for r in (json.loads(l) for l in gzip.open(Path(mirror) / 'mirror_diag.jsonl.gz', 'rt'))}
    groups = []
    for r in L:
        mr = Mi[(r['episode_id'], r['t'])]
        m = r['m']; order = r['order']
        for gi, g in enumerate(r['groups']):
            K = g['K']; P = prefix_sets(order, K); Pm = [sum(1 << j for j in s) for s in P]
            profs = [[unmask(x, m) for x in pm] for pm in g['profiles']]
            ip = g['profiles'].index(Pm)
            vals = np.asarray(g['values'], float); delta = vals - vals[ip]
            cost = np.asarray([profile_cost(order, K, s)[0] for s in profs], float)
            r1 = np.asarray([all(len(s[i] - P[i]) <= 1 for i in range(m)) for s in profs])
            groups.append(dict(ep=r['episode_id'], seed=r['traffic_seed'], split=r['split'], m=m, z=r['z'],
                               priv=r['privileged'], mirror=mr['mirror'], K=K, order=order, P=P, ip=ip,
                               profs=profs, delta=delta, cost=cost, b0=cost[ip], r1=r1,
                               joint=mr['joint'][gi], joint_P=mr['joint'][gi][ip]))
    return groups


def pmat(s, m):
    M = np.zeros((m, m), np.float32)
    for i, si in enumerate(s):
        for j in si:
            M[i, j] = 1
    return M


def onehot_joint(j, m):
    v = np.zeros(m * 8, np.float32)
    for i, a in enumerate(j):
        v[i * 8 + int(a) % 8] = 1
    return v


def mlp_features(g, kind):
    m = g['m']; base = list(g['z'])
    if kind == 'history':
        base += g['mirror']
    if kind == 'joint_priv':
        base += g['priv']
    ctx = np.asarray(base + [k / m for k in g['K']], np.float32)
    rows = []
    for s, jn in zip(g['profs'], g['joint']):
        if kind == 'joint_priv':
            rows.append(np.concatenate([ctx, onehot_joint(jn, m), onehot_joint(g['joint_P'], m)]))
        else:
            rows.append(np.concatenate([ctx, pmat(s, m).reshape(-1)]))
    return np.stack(rows)


def edge_context(g, history):
    m = g['m']; z = g['z']; t = z[0]
    C = {}
    for i in range(m):
        for j in range(m):
            if i == j:
                continue
            c = list(z[1 + 12 * j: 1 + 12 * (j + 1)]) + [g['K'][i] / m, t]
            if history:
                k = i * (m - 1) + (j if j < i else j - 1)
                c += g['mirror'][12 * k: 12 * (k + 1)]
            C[(i, j)] = np.asarray(c, np.float32)
    return C


def ridge_features(g, history):
    m = g['m']; C = edge_context(g, history); dc = len(next(iter(C.values())))
    MP = pmat(g['P'], m)
    rows = []
    for s in g['profs']:
        D = pmat(s, m) - MP
        beta = D.reshape(-1)
        theta = np.zeros(dc, np.float32)
        for (i, j), c in C.items():
            if D[i, j] != 0:
                theta += D[i, j] * c
        rows.append(np.concatenate([beta, theta]))
    return np.stack(rows)


def select_eval(groups, preds, cap_extra):
    out = {}
    for name in ('repair_R1', 'direct', 'oracle_R1', 'oracle_all'):
        res = []
        for g, p in zip(groups, preds):
            cap = np.inf if cap_extra is None else g['b0'] + cap_extra
            ok = g['cost'] <= cap + 1e-9
            if name in ('repair_R1', 'oracle_R1'):
                ok = ok & g['r1']
            ix = np.nonzero(ok)[0]
            score = g['delta'] if name.startswith('oracle') else p
            j = ix[int(np.argmax(score[ix]))]
            if score[j] <= 0 and not name.startswith('oracle'):
                j = g['ip']
            if name.startswith('oracle') and g['delta'][j] <= 0:
                j = g['ip']
            edit = j != g['ip']
            res.append(dict(ep=g['ep'], gain=g['delta'][j], edit=edit, harm=edit and g['delta'][j] < 0,
                            bytes=g['cost'][j] - g['b0']))
        out[name] = res
    return out


def per_episode(res, key):
    eps = {}
    for r in res:
        eps.setdefault(r['ep'], []).append(float(r[key]))
    return {e: float(np.mean(v)) for e, v in sorted(eps.items())}


def train_mlp(Xf, Yf, Xs, gs_sel, groups_sel, seed, epochs=150, hidden=128):
    torch.manual_seed(seed); rng = np.random.default_rng(seed)
    mean = Xf.mean(0); std = Xf.std(0); std[std < 1e-6] = 1
    scale = max(float(Yf.std()), 1e-6)
    net = nn.Sequential(nn.Linear(Xf.shape[1], hidden), nn.ReLU(), nn.Linear(hidden, hidden), nn.ReLU(), nn.Linear(hidden, 1))
    opt = torch.optim.Adam(net.parameters(), lr=1e-3, weight_decay=1e-4)
    xt = torch.as_tensor((Xf - mean) / std); yt = torch.as_tensor(Yf / scale)
    best, saved = -np.inf, None
    for ep in range(epochs):
        for b in np.array_split(rng.permutation(len(Yf)), max(1, len(Yf) // 256)):
            loss = ((net(xt[b]).squeeze(-1) - yt[b]) ** 2).mean()
            opt.zero_grad(); loss.backward(); opt.step()
        if ep % 10 == 0 or ep == epochs - 1:
            with torch.no_grad():
                preds = [net(torch.as_tensor((x - mean) / std)).squeeze(-1).numpy() for x in Xs]
            metric = np.mean([r['gain'] for r in select_eval(groups_sel, preds, None)['repair_R1']])
            if metric > best:
                best, saved = metric, copy.deepcopy(net.state_dict())
    net.load_state_dict(saved); net.eval()
    return lambda x: net(torch.as_tensor((x - mean) / std)).detach().squeeze(-1).numpy()


def fit_ridge(Xf, Yf, Xs, groups_sel):
    mean = Xf.mean(0); std = Xf.std(0); std[std < 1e-6] = 1
    A = (Xf - mean) / std; best, W = -np.inf, None
    for lam in [1e-2, 1e-1, 1, 10, 100, 1000, 1e4]:
        w = np.linalg.solve(A.T @ A + lam * np.eye(A.shape[1]), A.T @ Yf)
        preds = [((x - mean) / std) @ w for x in Xs]
        metric = np.mean([r['gain'] for r in select_eval(groups_sel, preds, None)['repair_R1']])
        if metric > best:
            best, W, L = metric, w, lam
    return (lambda x: ((x - mean) / std) @ W), L


def main(a):
    groups = load(a.labels, a.mirror)
    if any(g['split'] == 'test' for g in groups):
        raise ValueError('test data must not be present')
    fit = [g for g in groups if g['split'] == 'train' and g['seed'] in INNER_FIT]
    sel = [g for g in groups if g['split'] == 'train' and g['seed'] in INNER_SEL]
    val = [g for g in groups if g['split'] == 'val']
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    report = dict(status='RUNNING', groups=dict(fit=len(fit), select=len(sel), val=len(val)), source_hashes=hashes,
                  note='train/val only; inner selection on seeds 47-48; val 51-52 for the comparison', results={})
    t0 = time.perf_counter()

    def record(name, predict_val):
        res = {}
        for cap in CAPS:
            ev = select_eval(val, predict_val, cap)
            res['none' if cap is None else f'+{cap}'] = {
                k: dict(gain=per_episode(v, 'gain'), harm=per_episode(v, 'harm'), edit=per_episode(v, 'edit'),
                        bytes=per_episode(v, 'bytes')) for k, v in ev.items()}
        report['results'][name] = res

    for kind in ('public', 'history', 'joint_priv'):
        Xf = np.concatenate([mlp_features(g, kind) for g in fit]); Yf = np.concatenate([g['delta'] for g in fit])
        Xs = [mlp_features(g, kind) for g in sel]; Xv = [mlp_features(g, kind) for g in val]
        for seed in a.seeds:
            f = train_mlp(Xf.astype(np.float32), Yf.astype(np.float32), [x.astype(np.float32) for x in Xs], None, sel, seed)
            record(f'mlp_{kind}/seed{seed}', [f(x.astype(np.float32)) for x in Xv])
            print(f'[{time.perf_counter() - t0:.0f}s] mlp_{kind} seed {seed} done', flush=True)
    for history in (False, True):
        name = 'ridge_edge_history' if history else 'ridge_edge_public'
        Xf = np.concatenate([ridge_features(g, history) for g in fit]); Yf = np.concatenate([g['delta'] for g in fit])
        Xs = [ridge_features(g, history) for g in sel]; Xv = [ridge_features(g, history) for g in val]
        f, lam = fit_ridge(Xf, Yf, Xs, sel)
        record(name, [f(x) for x in Xv]); report['results'][name]['lambda'] = lam
        print(f'[{time.perf_counter() - t0:.0f}s] {name} lambda {lam}', flush=True)
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    report.update(status='COMPLETE', seconds=time.perf_counter() - t0)
    (out / 'report.json').write_text(json.dumps(report, indent=1, default=float))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', required=True); p.add_argument('--mirror', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    main(p.parse_args())
