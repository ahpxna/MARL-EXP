#!/usr/bin/env python3
"""Selective-revision diagnostic v2 (MARL_HETERO_DIAGNOSTIC_INDEPENDENT_AUDIT, "Minimal worker task").

v1 (MARL_hetero_diag_train.py) and its report are kept unchanged.  Changes, each from the audit:
  * ANCHORED scores: s(S) = pred(S) - pred(P), so the prefix scores exactly 0; argmax ties and
    improvements within TOL go to the prefix, deterministically                        [§1]
  * a no-edit threshold tau is SELECTED on the inner split (seeds 47-48) from a grid that
    includes never-edit; epoch / lambda / tau all target the DECLARED operating point
    cap = prefix bytes + 28; the same procedure is applied to repair and to direct     [§2]
  * ridge: wider lambda grid; coefficients and anchored-score margins saved              [§3]
  * saved: selected model/normalisation, epoch/lambda/tau, anchored candidate predictions
    and chosen indices for every validation group and cap                                [task]
  * two OPTIONAL ablations of the privileged control, clearly labelled: summaries only,
    joint actions only                                                                    [§4]
TRAIN/VAL only (fit 41-46, select 47-48, compare on 51-52); seeds 61-64 are not read.
Candidate-set argmax over the stored ~181 candidates per group, not the deployed coordinate search.
"""
from __future__ import annotations
import argparse, copy, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_hetero_diag_train import (load, mlp_features, ridge_features, onehot_joint, INNER_FIT,
                                            INNER_SEL, CAPS)

SOURCES = ['scripts/MARL_hetero_diag_train_v2.py', 'scripts/MARL_hetero_diag_train.py',
           'models/marl_hetero_selector.py']
OPERATING_CAP = 28
TOL = 1e-9


def feats(g, kind):
    m = g['m']
    if kind in ('public', 'history', 'joint_priv'):
        return mlp_features(g, kind)
    ctx = list(g['z']) + [k / m for k in g['K']]
    if kind == 'summaries_only':
        ctx = ctx + list(g['priv'])
        base = mlp_features(g, 'public')                      # [z, K, M(S)] plus current summaries
        return np.concatenate([base, np.tile(np.asarray(g['priv'], np.float32), (len(base), 1))], 1)
    if kind == 'joint_only':
        c = np.asarray(ctx, np.float32)
        return np.stack([np.concatenate([c, onehot_joint(j, m), onehot_joint(g['joint_P'], m)]) for j in g['joint']])
    raise ValueError(kind)


def choose(g, anchored, cap_extra, restrict_r1, tau):
    """Index chosen by the anchored rule; the prefix wins ties and anything <= tau."""
    cap = np.inf if cap_extra is None else g['b0'] + cap_extra
    ok = g['cost'] <= cap + 1e-9
    if restrict_r1:
        ok = ok & g['r1']
    ix = np.nonzero(ok)[0]
    s = anchored[ix]
    j = ix[int(np.argmax(s))]
    if anchored[j] <= tau + TOL:
        return g['ip']
    return j


def outcome(g, j):
    edit = j != g['ip']
    act_change = edit and g['joint'][j] != g['joint_P']
    return dict(ep=g['ep'], headway=g['ep'].split('load')[1], gain=float(g['delta'][j]), edit=edit,
                harm=bool(edit and g['delta'][j] < 0), act_change=bool(act_change),
                bytes=float(g['cost'][j] - g['b0']), chosen=int(j))


def anchor(g, pred):
    a = np.asarray(pred, float) - float(pred[g['ip']])
    a[g['ip']] = 0.0
    return a


def tau_grid(groups, anchored_list):
    pos = np.concatenate([a[a > 0] for a in anchored_list]) if anchored_list else np.array([])
    grid = [0.0] + (list(np.quantile(pos, [0.1, 0.25, 0.5, 0.75, 0.9])) if len(pos) else [])
    return grid + [np.inf]                                  # inf = never edit


def select_tau(groups, anchored_list, restrict_r1):
    best_t, best_v = None, -np.inf
    for t in tau_grid(groups, anchored_list):
        v = np.mean([outcome(g, choose(g, a, OPERATING_CAP, restrict_r1, t))['gain'] for g, a in zip(groups, anchored_list)])
        if v > best_v + 1e-12:
            best_t, best_v = t, v
    return best_t, best_v


def inner_metric(groups, anchored_list):
    """Operating-point objective with tau selected for repair_R1 (the method under study)."""
    return select_tau(groups, anchored_list, True)[1]


def train_mlp(Xf, Yf, Xs, sel, seed, epochs=150, hidden=128):
    torch.manual_seed(seed); rng = np.random.default_rng(seed)
    mean = Xf.mean(0); std = Xf.std(0); std[std < 1e-6] = 1
    scale = max(float(Yf.std()), 1e-6)
    net = nn.Sequential(nn.Linear(Xf.shape[1], hidden), nn.ReLU(), nn.Linear(hidden, hidden), nn.ReLU(), nn.Linear(hidden, 1))
    opt = torch.optim.Adam(net.parameters(), lr=1e-3, weight_decay=1e-4)
    xt = torch.as_tensor((Xf - mean) / std); yt = torch.as_tensor(Yf / scale)
    best, saved, best_ep = -np.inf, None, None
    for ep in range(epochs):
        for b in np.array_split(rng.permutation(len(Yf)), max(1, len(Yf) // 256)):
            loss = ((net(xt[b]).squeeze(-1) - yt[b]) ** 2).mean()
            opt.zero_grad(); loss.backward(); opt.step()
        if ep % 10 == 0 or ep == epochs - 1:
            with torch.no_grad():
                preds = [net(torch.as_tensor((x - mean) / std)).squeeze(-1).numpy() for x in Xs]
            metric = inner_metric(sel, [anchor(g, p) for g, p in zip(sel, preds)])
            if metric > best + 1e-12:
                best, saved, best_ep = metric, copy.deepcopy(net.state_dict()), ep
    net.load_state_dict(saved); net.eval()
    f = lambda x: net(torch.as_tensor((x - mean) / std)).detach().squeeze(-1).numpy()
    return f, dict(epoch=best_ep, inner_metric=best), dict(state=saved, mean=mean, std=std, scale=scale, hidden=hidden)


def fit_ridge(Xf, Yf, Xs, sel):
    mean = Xf.mean(0); std = Xf.std(0); std[std < 1e-6] = 1
    A = (Xf - mean) / std; best = (-np.inf, None, None)
    for lam in [1e-2, 1e-1, 1, 10, 100, 1e3, 1e4, 1e5, 1e6, 1e7]:
        w = np.linalg.solve(A.T @ A + lam * np.eye(A.shape[1]), A.T @ Yf)
        preds = [((x - mean) / std) @ w for x in Xs]
        metric = inner_metric(sel, [anchor(g, p) for g, p in zip(sel, preds)])
        if metric > best[0] + 1e-12:
            best = (metric, w, lam)
    _, W, L = best
    return (lambda x: ((x - mean) / std) @ W), dict(lam=L, inner_metric=best[0]), dict(w=W, mean=mean, std=std)


def evaluate(val, sel, f_sel_preds, f_val_preds):
    sel_anch = [anchor(g, p) for g, p in zip(sel, f_sel_preds)]
    val_anch = [anchor(g, p) for g, p in zip(val, f_val_preds)]
    taus = {pol: select_tau(sel, sel_anch, pol == 'repair_R1')[0] for pol in ('repair_R1', 'direct')}
    res, chosen = {}, {}
    for cap in CAPS:
        key = 'none' if cap is None else f'+{cap}'
        res[key] = {}
        for pol in ('repair_R1', 'direct'):
            outs = [outcome(g, choose(g, a, cap, pol == 'repair_R1', taus[pol])) for g, a in zip(val, val_anch)]
            res[key][pol] = outs; chosen[(key, pol)] = [o['chosen'] for o in outs]
        for pol in ('oracle_R1', 'oracle_all'):
            outs = [outcome(g, choose(g, g['delta'].astype(float), cap, pol == 'oracle_R1', 0.0)) for g in val]
            res[key][pol] = outs
    margins = np.concatenate([a[np.arange(len(a)) != g['ip']] for g, a in zip(val, val_anch)])
    return res, taus, val_anch, chosen, dict(anchored_margin_quantiles=np.quantile(margins, [0, .1, .5, .9, 1]).tolist(),
                                             frac_nonprefix_positive=float((margins > TOL).mean()))


def summarise(outs):
    by = lambda key, filt=None: {e: float(np.mean([o[key] for o in outs if o['ep'] == e and (filt is None or filt(o))]))
                                 for e in sorted({o['ep'] for o in outs})}
    n = len(outs); edits = sum(o['edit'] for o in outs)
    return dict(gain_by_episode=by('gain'), gain=float(np.mean([o['gain'] for o in outs])),
                gain_by_headway={h: float(np.mean([o['gain'] for o in outs if o['headway'] == h])) for h in sorted({o['headway'] for o in outs})},
                edit_rate=edits / n, harm_rate_over_groups=sum(o['harm'] for o in outs) / n,
                harm_over_edits=(sum(o['harm'] for o in outs) / edits) if edits else 0.0,
                action_change_rate=sum(o['act_change'] for o in outs) / n,
                extra_bytes=float(np.mean([o['bytes'] for o in outs])), groups=n)


def main(a):
    groups = load(a.labels, a.mirror)
    if any(g['split'] == 'test' for g in groups):
        raise ValueError('test data must not be present')
    fit = [g for g in groups if g['split'] == 'train' and g['seed'] in INNER_FIT]
    sel = [g for g in groups if g['split'] == 'train' and g['seed'] in INNER_SEL]
    val = [g for g in groups if g['split'] == 'val']
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    report = dict(status='RUNNING', version='v2 anchored + inner-selected tau', operating_cap=OPERATING_CAP,
                  groups=dict(fit=len(fit), select=len(sel), val=len(val)), source_hashes=hashes, results={})
    dec = gzip.open(out / 'decisions.jsonl.gz', 'wt'); t0 = time.perf_counter()

    def record(name, sel_preds, val_preds, sel_info, model_blob):
        res, taus, val_anch, chosen, marg = evaluate(val, sel, sel_preds, val_preds)
        report['results'][name] = dict(selection=sel_info, tau={k: (None if np.isinf(v) else float(v)) for k, v in taus.items()},
                                       never_edit_selected={k: bool(np.isinf(v)) for k, v in taus.items()}, margins=marg,
                                       caps={cap: {pol: summarise(o) for pol, o in d.items()} for cap, d in res.items()})
        torch.save(model_blob, out / f'model_{name.replace("/", "_")}.pt')
        for gi, (g, an) in enumerate(zip(val, val_anch)):
            dec.write(json.dumps(dict(model=name, ep=g['ep'], group=gi, anchored=[round(float(x), 5) for x in an],
                                      chosen={f'{k[0]}|{k[1]}': v[gi] for k, v in chosen.items()})) + '\n')

    kinds = ['public', 'history', 'joint_priv'] + (['summaries_only', 'joint_only'] if a.ablations else [])
    for kind in kinds:
        Xf = np.concatenate([feats(g, kind) for g in fit]).astype(np.float32)
        Yf = np.concatenate([g['delta'] for g in fit]).astype(np.float32)
        Xs = [feats(g, kind).astype(np.float32) for g in sel]; Xv = [feats(g, kind).astype(np.float32) for g in val]
        for seed in a.seeds:
            f, info, blob = train_mlp(Xf, Yf, Xs, sel, seed)
            record(f'mlp_{kind}/seed{seed}', [f(x) for x in Xs], [f(x) for x in Xv], info, blob)
            print(f'[{time.perf_counter() - t0:.0f}s] mlp_{kind} seed {seed}: epoch {info["epoch"]}', flush=True)
    for history in (False, True):
        name = 'ridge_edge_history' if history else 'ridge_edge_public'
        Xf = np.concatenate([ridge_features(g, history) for g in fit]); Yf = np.concatenate([g['delta'] for g in fit])
        Xs = [ridge_features(g, history) for g in sel]; Xv = [ridge_features(g, history) for g in val]
        f, info, blob = fit_ridge(Xf, Yf, Xs, sel)
        record(name, [f(x) for x in Xs], [f(x) for x in Xv], info, blob)
        print(f'[{time.perf_counter() - t0:.0f}s] {name}: lambda {info["lam"]}', flush=True)
    dec.close()
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    report.update(status='COMPLETE', seconds=time.perf_counter() - t0,
                  decisions_sha256=hashlib.sha256((out / 'decisions.jsonl.gz').read_bytes()).hexdigest())
    (out / 'report.json').write_text(json.dumps(report, indent=1, default=float))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', required=True); p.add_argument('--mirror', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2]); p.add_argument('--ablations', action='store_true')
    main(p.parse_args())
