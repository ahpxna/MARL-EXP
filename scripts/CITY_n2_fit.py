#!/usr/bin/env python3
"""N2 forecaster fit + offline comparison (PROTOCOL_CITY_N2_STATE_FORECAST_20261005).  Rows (per second i, light j, target green):
  ttr  light in green g: target = remaining seconds of the current green run (convention of CITY_spat_forecast_k_conv: st + ln - i)
  ttg  every green g not active: target = seconds to g's next onset (nxt - i); rows without an observed end / onset are censored (dropped)
Features (causal; available to the infrastructure at time i): phase position one-hot, spent / 60, target flag, halting / vehicles on the
current (or just-ended) green's lanes and on the target green's lanes, mean of the last two completed run lengths of both greens / 60,
light one-hot.  Model: MLP 64-64, two monotone quantiles (0.1, 0.5), pinball loss, rows weighted 0.25 + (fleet queries at (i, j)).
Train seeds 0-5, validation 6-7 (early stopping and the offline comparison).  Comparator on the SAME files: the age-only table
(CITY_spat_forecast.fit on the train files, served as provider c2 = CITY_spat_forecast_k on the augmented table).
Usage: CITY_n2_fit.py <k> <data dir> <out dir>"""
import json, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
QS = (0.1, 0.5)


def hist_series(col, g, T, default):
    """mean of the last two COMPLETED run lengths of phase g that ended at or before each index (default before any)."""
    out = np.full(T, default, np.float32); last = []
    for ph, st, ln, complete in FC.runs(col):
        if ph == g and complete:
            last = (last + [ln])[-2:]
            out[st + ln:] = float(np.mean(last))
    return out


def build(files, greens):
    """vectorised per (file, light, target green).  M rows: (file, i, j, g, phase, spent) for the age-only comparator."""
    X, Y, W, K, M = [], [], [], [], []
    for fi, f in enumerate(files):
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S, H, V, Q = z['phases'], z['spent'], z['H'], z['V'], z['Q']; T = len(P); L = len(ids)
        I = np.arange(T)
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
            hist = {g: hist_series(col, g, T, 15.0) for g in gs}; oh = np.zeros((T, 4), np.float32); oh[I, np.clip(col, 0, 3)] = 1
            hc = np.stack([hist[g] for g in gs], 1)[I, ci]; eye = np.zeros(L, np.float32); eye[j] = 1
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
                                            H[ii, j, tt] / 10.0, V[ii, j, tt] / 20.0, hc[ii] / 60.0, hist[g][ii] / 60.0, np.tile(eye, (len(ii), 1))]).astype(np.float32)
                    X.append(feat); Y.append(y[ii].astype(np.float32)); W.append(0.25 + Q[ii, j].astype(np.float32)); K.append(np.full(len(ii), kind))
                    M.extend((fi, int(i), j, g, int(col[i]), float(S[i, j])) for i in ii)
    return np.concatenate(X), np.concatenate(Y), np.concatenate(W), np.concatenate(K), M


class QNet(torch.nn.Module):
    def __init__(self, d):
        super().__init__(); self.f = torch.nn.Sequential(torch.nn.Linear(d, 64), torch.nn.ReLU(), torch.nn.Linear(64, 64), torch.nn.ReLU(), torch.nn.Linear(64, 2))

    def forward(self, x):
        o = self.f(x); q1 = torch.nn.functional.softplus(o[:, 0]); return torch.stack([q1, q1 + torch.nn.functional.softplus(o[:, 1])], 1)


def pinball(pred, y, w):
    l = 0.0
    for k, q in enumerate(QS):
        e = y - pred[:, k]; l = l + (w * torch.maximum(q * e, (q - 1) * e)).sum() / w.sum()
    return l


def metrics(err, w):
    e = np.asarray(err); w = np.asarray(w); a = np.abs(e)
    return dict(n=int(len(e)), bias=float(np.average(e, weights=w)), mae=float(np.average(a, weights=w)), within_1s=float(np.average(a <= 1, weights=w)),
                early_gt_1s=float(np.average(e < -1, weights=w)), late_gt_1s=float(np.average(e > 1, weights=w)))


if __name__ == '__main__':
    k, D, O = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3]); O.mkdir(parents=True, exist_ok=True); torch.manual_seed(0); np.random.seed(0); torch.set_num_threads(1)
    tr = [D / f'feat_s{s}.npz' for s in range(6)]; va = [D / f'feat_s{s}.npz' for s in (6, 7)]
    import scripts.CITY_eval4 as E4
    info = E4.NetInfo(E4.Q7.NET_S); greens = {t: list(info.tls[t]['greens']) for t in info.tls}; t0 = time.time()
    Xt, Yt, Wt, Kt, _ = build(tr, greens); Xv, Yv, Wv, Kv, Mv = build(va, greens); print(f'rows train {len(Yt)} val {len(Yv)} ({time.time() - t0:.0f}s)', flush=True)
    net = QNet(Xt.shape[1]); opt = torch.optim.Adam(net.parameters(), 1e-3); xt, yt, wt = map(torch.as_tensor, (Xt, Yt, Wt)); xv, yv, wv = map(torch.as_tensor, (Xv, Yv, Wv))
    best, bs, wait = 1e18, None, 0
    for ep in range(40):
        perm = torch.randperm(len(yt))
        for b in range(0, len(yt), 8192):
            ix = perm[b:b + 8192]; opt.zero_grad(); l = pinball(net(xt[ix]), yt[ix], wt[ix]); l.backward(); opt.step()
        with torch.no_grad():
            lv = float(pinball(net(xv), yv, wv))
        print(f'epoch {ep} val pinball {lv:.4f}', flush=True)
        if lv < best - 1e-4:
            best, bs, wait = lv, {kk: v.clone() for kk, v in net.state_dict().items()}, 0
        else:
            wait += 1
            if wait >= 4:
                break
    net.load_state_dict(bs); torch.save(dict(state=bs, d=Xt.shape[1], qs=QS, ids=sorted(info.tls), greens=greens, k=k, train=[str(f) for f in tr]), O / f'n2_k{k}.pt')
    with torch.no_grad():
        pv = net(xv).numpy()
    T_age = C2.augment(FC.fit([str(f) for f in tr])); res = {}
    for qi, q in enumerate(QS):
        F = FK.ForecastK(T_age, q); ea = []
        ids = sorted(info.tls)
        for (fi, i, j, g, ph, s), kind in zip(Mv, Kv):
            tid = ids[j]
            fa = (F.rem(tid, ph, s) + FK.OBS) if kind == 0 else F.ttg(tid, ph, s, {g})   # the published ttr is rem + OBS; target y uses the same convention
            ea.append(fa)
        ea = np.array(ea); en = pv[:, qi] - Yv
        res[f'q{q}'] = dict(age_only=dict(all=metrics(ea - Yv, np.ones_like(Wv)), query_weighted=metrics(ea - Yv, Wv - 0.25 + 1e-9)),
                            state_model=dict(all=metrics(en, np.ones_like(Wv)), query_weighted=metrics(en, Wv - 0.25 + 1e-9)))
    json.dump(dict(k=k, rows_train=int(len(Yt)), rows_val=int(len(Yv)), best_val_pinball=best, compare=res), open(O / f'n2_k{k}_compare.json', 'w'), indent=1); print(json.dumps(res))
