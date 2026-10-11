#!/usr/bin/env python3
"""CITY_n2_fit.py without the stored light one-hot (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010, MT-F resume, 11/10/2026).
Why: the original stores every row's light one-hot, so its feature matrix grows with rows x lights.  On the full Midtown map (511 AI
lights, 4 242 s per log, about 4.3 M rows per log) the six training logs alone need about 54 GB; the fit was SIGKILLed at an 80 GB peak
memory footprint.
What is the same: rows, the 12 state features and their order, the light one-hot as the last L inputs, QNet (same module, same
parameters, same checkpoint format), seeds and initialisation, minibatch permutation, pinball loss, Adam, early stopping, the offline
age-only comparison.  What changes: X holds the 12 state features and J the light index.  The first layer's output
W[:, :12] x + W[:, 12 + j] + b equals W [x; onehot_j] + b, so it is computed by a column lookup instead of a product with a one-hot
(same parameters and gradients; float summation order differs).  A self-check at start compares it with net(cat(x, onehot)).
The validation loss and predictions are computed in batches.  Equivalence with the original on the grid W19 data: KMT7 (protocol).
Usage: CITY_n2_fit_lowmem.py <k> <data dir> <out dir>"""
import json, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2_fit as N2  # noqa: E402  (hist_series, QNet, pinball, metrics, QS: reused unchanged)
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
QS = N2.QS
EVAL_BATCH = 65536


def build(files, greens):
    """N2.build without the stored one-hot: X (rows x 12 state features), J (light index of each row), L, Y, W, K, and M = rows of
    (file, i, j, g, phase, spent) for the age-only comparator as a float64 array."""
    X, J, Y, W, K, M, Ls = [], [], [], [], [], [], set()
    for fi, f in enumerate(files):
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S, H, V, Q = z['phases'], z['spent'], z['H'], z['V'], z['Q']; T = len(P); L = len(ids)
        Ls.add(L); I = np.arange(T)
        for j, tid in enumerate(ids):
            gs = greens[tid]; col = P[:, j].astype(int); n_ph = max(int(col.max()) + 1, max(gs) + 2)
            curpos = np.array([max([k for k, g in enumerate(gs) if g <= ph], default=len(gs) - 1) for ph in range(n_ph)])
            ci = curpos[col]; end = np.full(T, -1); nxt = {}
            for ph, st, ln, complete in FC.runs(col):
                if complete:
                    end[st:st + ln] = st + ln
            for g in gs:
                starts = np.r_[np.flatnonzero((col == g) & np.r_[True, col[:-1] != g]), T]; k_ = np.searchsorted(starts, I, side='left'); nx = starts[k_]
                nxt[g] = np.where(nx < T, nx, -1)
            hist = {g: N2.hist_series(col, g, T, 15.0) for g in gs}; oh = np.zeros((T, 4), np.float32); oh[I, np.clip(col, 0, 3)] = 1
            hc = np.stack([hist[g] for g in gs], 1)[I, ci]
            for gk, g in enumerate(gs):
                for kind in (0, 1):
                    if kind == 0:
                        m = (col == g) & (end >= 0); y = end - I; ti = np.full(T, 1 - gk)
                    else:
                        m = (col != g) & (nxt[g] >= 0); y = nxt[g] - I; ti = np.full(T, gk)
                    if not m.any():
                        continue
                    ii = I[m]; cc = ci[ii]; tt = ti[ii]
                    feat = np.column_stack([oh[ii], S[ii, j] / 60.0, np.full(len(ii), float(kind)), H[ii, j, cc] / 10.0, V[ii, j, cc] / 20.0,
                                            H[ii, j, tt] / 10.0, V[ii, j, tt] / 20.0, hc[ii] / 60.0, hist[g][ii] / 60.0]).astype(np.float32)
                    X.append(feat); J.append(np.full(len(ii), j, np.int64)); Y.append(y[ii].astype(np.float32)); W.append(0.25 + Q[ii, j].astype(np.float32))
                    K.append(np.full(len(ii), kind, np.int8))
                    M.append(np.column_stack([np.full(len(ii), fi, np.float64), ii, np.full(len(ii), j, np.float64), np.full(len(ii), g, np.float64),
                                              col[ii], S[ii, j].astype(np.float64)]))
    assert len(Ls) == 1, f'light count differs between logs: {Ls}'
    return np.concatenate(X), np.concatenate(J), Ls.pop(), np.concatenate(Y), np.concatenate(W), np.concatenate(K), np.concatenate(M)


def qforward(net, x, j, n):
    """QNet.forward on [x; onehot_j] (x has n columns), with the first layer as a column lookup."""
    lin = net.f[0]
    h = torch.nn.functional.linear(x, lin.weight[:, :n], lin.bias) + lin.weight[:, n:].t()[j]
    o = net.f[1:](h); q1 = torch.nn.functional.softplus(o[:, 0])
    return torch.stack([q1, q1 + torch.nn.functional.softplus(o[:, 1])], 1)


def predict(net, x, j, n):
    with torch.no_grad():
        return torch.cat([qforward(net, x[b:b + EVAL_BATCH], j[b:b + EVAL_BATCH], n) for b in range(0, len(x), EVAL_BATCH)])


def pinball_batched(net, x, j, n, y, w):
    """N2.pinball over the whole set, accumulated batch by batch: sum_k sum(w * rho_q(e)) / sum(w)."""
    num = [0.0 for _ in QS]
    with torch.no_grad():
        for b in range(0, len(x), EVAL_BATCH):
            pred = qforward(net, x[b:b + EVAL_BATCH], j[b:b + EVAL_BATCH], n); yy, ww = y[b:b + EVAL_BATCH], w[b:b + EVAL_BATCH]
            for k, q in enumerate(QS):
                e = yy - pred[:, k]; num[k] += float((ww * torch.maximum(q * e, (q - 1) * e)).sum())
    den = float(w.sum())
    return sum(nk / den for nk in num)


if __name__ == '__main__':
    k, D, O = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3]); O.mkdir(parents=True, exist_ok=True); torch.manual_seed(0); np.random.seed(0); torch.set_num_threads(1)
    tr = [D / f'feat_s{s}.npz' for s in range(6)]; va = [D / f'feat_s{s}.npz' for s in (6, 7)]
    import scripts.CITY_eval4 as E4
    info = E4.NetInfo(E4.Q7.NET_S); greens = {t: list(info.tls[t]['greens']) for t in info.tls}; t0 = time.time()
    Xt, Jt, L, Yt, Wt, Kt, _ = build(tr, greens); Xv, Jv, Lv, Yv, Wv, Kv, Mv = build(va, greens); assert L == Lv
    n = Xt.shape[1]; d = n + L; print(f'rows train {len(Yt)} val {len(Yv)} lights {L} d {d} ({time.time() - t0:.0f}s)', flush=True)
    net = N2.QNet(d); opt = torch.optim.Adam(net.parameters(), 1e-3)
    xt, jt, yt, wt = map(torch.as_tensor, (Xt, Jt, Yt, Wt)); xv, jv, yv, wv = map(torch.as_tensor, (Xv, Jv, Yv, Wv))
    with torch.no_grad():   # self-check: the lookup forward equals QNet on the explicit one-hot input
        ix = torch.arange(0, len(yv), max(1, len(yv) // 4096))
        dense = net(torch.cat([xv[ix], torch.nn.functional.one_hot(jv[ix], L).to(xv.dtype)], 1)); diff = float((qforward(net, xv[ix], jv[ix], n) - dense).abs().max())
    print(f'self-check lookup vs one-hot forward: max |diff| {diff:.2e} on {len(ix)} rows', flush=True); assert diff < 1e-4, 'lookup forward differs from QNet'
    best, bs, wait = 1e18, None, 0
    for ep in range(40):
        perm = torch.randperm(len(yt))
        for b in range(0, len(yt), 8192):
            ix = perm[b:b + 8192]; opt.zero_grad(); l = N2.pinball(qforward(net, xt[ix], jt[ix], n), yt[ix], wt[ix]); l.backward(); opt.step()
        lv = pinball_batched(net, xv, jv, n, yv, wv)
        print(f'epoch {ep} val pinball {lv:.4f} ({time.time() - t0:.0f}s)', flush=True)
        if lv < best - 1e-4:
            best, bs, wait = lv, {kk: v.clone() for kk, v in net.state_dict().items()}, 0
        else:
            wait += 1
            if wait >= 4:
                break
    net.load_state_dict(bs); torch.save(dict(state=bs, d=d, qs=QS, ids=sorted(info.tls), greens=greens, k=k, train=[str(f) for f in tr]), O / f'n2_k{k}.pt')
    print(f'saved {O / f"n2_k{k}.pt"} ({time.time() - t0:.0f}s)', flush=True)
    pv = predict(net, xv, jv, n).numpy()
    T_age = C2.augment(FC.fit([str(f) for f in tr])); res = {}; ids = sorted(info.tls)
    for qi, q in enumerate(QS):
        F = FK.ForecastK(T_age, q); ea = []
        for (fi, i, j, g, ph, s), kind in zip(Mv, Kv):
            tid = ids[int(j)]; ph = int(ph); g = int(g)
            fa = (F.rem(tid, ph, float(s)) + FK.OBS) if kind == 0 else F.ttg(tid, ph, float(s), {g})   # the published ttr is rem + OBS
            ea.append(fa)
        ea = np.array(ea); en = pv[:, qi] - Yv
        res[f'q{q}'] = dict(age_only=dict(all=N2.metrics(ea - Yv, np.ones_like(Wv)), query_weighted=N2.metrics(ea - Yv, Wv - 0.25 + 1e-9)),
                            state_model=dict(all=N2.metrics(en, np.ones_like(Wv)), query_weighted=N2.metrics(en, Wv - 0.25 + 1e-9)))
    json.dump(dict(k=k, rows_train=int(len(Yt)), rows_val=int(len(Yv)), best_val_pinball=best, compare=res, fit_impl='CITY_n2_fit_lowmem'),
              open(O / f'n2_k{k}_compare.json', 'w'), indent=1); print(json.dumps(res)); print(f'done ({time.time() - t0:.0f}s)', flush=True)
