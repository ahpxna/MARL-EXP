#!/usr/bin/env python3
"""N2K4 (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendment A5): CITY_n2k.py (copied, not edited) generalised to K in {2, 3, 4} greens:
KMAX = 4; r one-hot of length 4; the K==3 flag replaced by a K one-hot over {2, 3, 4}; halting / vehicles / history at relative cycle
positions 0..3 (zero beyond K); greens_of_net() reads the CURRENT Q7.NET_S (set by the runner) instead of importing the spider patch.
Original docstring: N2K: the state-conditioned quantile forecaster for lights with K in {2, 3} greens (PROTOCOL_CITY_SPIDER_TSI_20261005).
One feature function (feat) is shared by the offline builder and the online provider, so the parity check KS-1 compares like with like.
Feature vector (15 + L): [kind (0 ttr of the current green / 1 ttg of another green), yellow, r one-hot (3; greens to pass before the
target), spent / 60, K==3, halting / 10 and vehicles / 20 on the greens at relative cycle positions 0 / 1 / 2 (position 2 zero when K = 2),
mean of their last two completed runs / 60 (default 15 s), light one-hot].  Targets: end of the current green run - i (kind 0), next
onset of the target green - i (kind 1); censored rows dropped.  Model: CITY_n2_fit.QNet (MLP 64-64, quantiles 0.1 / 0.5).
CLI:  CITY_n2k.py fit <data dir> <out model.pt>        (train seeds 0-5, validation 6-7)
      CITY_n2k.py parity <featlog dir> <seed> <model>  (KS-1; exit 1 on failure)"""
import json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2_fit as NF  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
KMAX = 4


def cur_index(gs, ph):
    return (gs.index(ph), 0) if ph in gs else (max([k for k, g in enumerate(gs) if g <= ph], default=len(gs) - 1), 1)


def r_of(gs, ci, yellow, gk):
    K = len(gs)
    return ((gk - ci - 1) % K) if yellow else ((gk - ci) % K - 1)


def feat(kind, yellow, r, spent, gs, ci, H, V, hist, j, L):
    """H, V, hist: per GREEN INDEX (length K) at this second; returns the float32 vector."""
    K = len(gs); oh = [0.0] * KMAX; oh[r] = 1.0; hp, vp, mp = [], [], []
    for p in range(KMAX):
        if p < K:
            g = (ci + p) % K; hp.append(H[g] / 10.0); vp.append(V[g] / 20.0); mp.append(hist[g] / 60.0)
        else:
            hp.append(0.0); vp.append(0.0); mp.append(0.0)
    eye = [0.0] * L; eye[j] = 1.0; ko = [float(K == 2), float(K == 3), float(K == 4)]
    return np.array([float(kind), float(yellow)] + oh + [spent / 60.0] + ko + hp + vp + mp + eye, np.float32)


def build(files, greens):
    """greens: {tid: [green phase indices]}.  Returns X, Y, W, keys (file, i, tid, kind, r)."""
    X, Y, W, KEYS = [], [], [], []
    for fi, f in enumerate(files):
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S, H, V, Q = z['phases'], z['spent'], z['H'], z['V'], z['Q']; T, L = P.shape
        for j, tid in enumerate(ids):
            gs = greens[tid]; K = len(gs); col = P[:, j].astype(int); end = np.full(T, -1); I = np.arange(T)
            for ph, st, ln, complete in FC.runs(col):
                if complete:
                    end[st:st + ln] = st + ln
            nxt = {}
            for g in gs:
                starts = np.r_[np.flatnonzero((col == g) & np.r_[True, col[:-1] != g]), T]; nx = starts[np.searchsorted(starts, I, side='left')]; nxt[g] = np.where(nx < T, nx, -1)
            hist = {g: NF.hist_series(col, g, T, 15.0) for g in gs}
            for i in range(T):
                ph = int(col[i]); ci, yel = cur_index(gs, ph); Hg = H[i, j, :K]; Vg = V[i, j, :K]; hg = [hist[g][i] for g in gs]
                rows = []
                if not yel and end[i] >= 0:
                    rows.append((0, 0, end[i] - i))
                for gk, g in enumerate(gs):
                    if (not yel) and gk == ci:
                        continue
                    if nxt[g][i] >= 0:
                        rows.append((1, r_of(gs, ci, yel, gk), nxt[g][i] - i))
                for kind, r, y in rows:
                    X.append(feat(kind, yel, r, float(S[i, j]), gs, ci, Hg, Vg, hg, j, L)); Y.append(float(y)); W.append(0.25 + float(Q[i, j])); KEYS.append((fi, i, tid, kind, r))
    return np.stack(X), np.array(Y, np.float32), np.array(W, np.float32), KEYS


def greens_of_net():
    import scripts.CITY_q7_cross_version as Q7                      # N2K4: the runner's net (Salt Lake via CITY_sl_runw4)
    from scripts.CITY_lightk import NetInfoK
    info = NetInfoK(Q7.NET_S); return {t: list(info.tls[t]['greens']) for t in info.tls}, info


def fit(D, out):
    torch.manual_seed(0); np.random.seed(0); torch.set_num_threads(1); greens, _ = greens_of_net()
    fs = sorted(D.glob('feat_s*.npz'), key=lambda f: int(f.stem.split('_s')[1])); nv = max(1, len(fs) // 4); tr, va = fs[:-nv], fs[-nv:]   # N2K4: any day ids
    Xt, Yt, Wt, _ = build(tr, greens); Xv, Yv, Wv, _ = build(va, greens); print(f'rows train {len(Yt)} val {len(Yv)}', flush=True)
    net = NF.QNet(Xt.shape[1]); opt = torch.optim.Adam(net.parameters(), 1e-3); xt, yt, wt = map(torch.as_tensor, (Xt, Yt, Wt)); xv, yv, wv = map(torch.as_tensor, (Xv, Yv, Wv))
    best, bs, wait = 1e18, None, 0
    for ep in range(40):
        perm = torch.randperm(len(yt))
        for b in range(0, len(yt), 8192):
            ix = perm[b:b + 8192]; opt.zero_grad(); l = NF.pinball(net(xt[ix]), yt[ix], wt[ix]); l.backward(); opt.step()
        with torch.no_grad():
            lv = float(NF.pinball(net(xv), yv, wv))
        print(f'epoch {ep} val pinball {lv:.4f}', flush=True)
        if lv < best - 1e-4:
            best, bs, wait = lv, {k: v.clone() for k, v in net.state_dict().items()}, 0
        else:
            wait += 1
            if wait >= 4:
                break
    net.load_state_dict(bs)
    with torch.no_grad():
        pv = net(xv).numpy()
    m = {f'q{q}': NF.metrics(pv[:, k] - Yv, Wv - 0.25 + 1e-9) for k, q in enumerate(NF.QS)}
    torch.save(dict(state=bs, d=Xt.shape[1], qs=NF.QS, ids=sorted(greens), greens=greens), out)
    json.dump(dict(rows_train=int(len(Yt)), rows_val=int(len(Yv)), best_val_pinball=best, val_query_weighted=m), open(str(out) + '.json', 'w'), indent=1); print(json.dumps(m))


def make_provider(model_path, q, info, tracker, fk_spat, debug=None):
    """Online N2K with the direct-only hybrid: yellow AND the next green serves the link -> fk_spat (exact there); a link served by the
    current AND the next green -> fk_spat; always-green -> ttg 0 / ttr 999; never-green -> invalid."""
    import scripts.CITY_env as CE
    d = torch.load(model_path, weights_only=False); net = NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval(); qi = list(d['qs']).index(q)
    ids = list(d['ids']); L = len(ids); cache = {}; stc = {}; stats = dict(valid=0, n2k=0, fk_direct=0, fk_multi=0, exc=0)

    def preds(tid, t):
        ls = CE.ls; dd = info.tls[tid]; gs = list(dd['greens']); K = len(gs); ph = ls.trafficlight.getPhase(tid); s = float(ls.trafficlight.getSpentDuration(tid))
        ci, yel = cur_index(gs, ph); H = [sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in dd['serve']]; V = [sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in dd['serve']]
        hist = [tracker.mean(tid, g, ph) for g in gs]; j = ids.index(tid); rows, keys = [], []
        if not yel:
            rows.append(feat(0, 0, 0, s, gs, ci, H, V, hist, j, L)); keys.append((0, 0))
        for gk in range(K):
            if (not yel) and gk == ci:
                continue
            r = r_of(gs, ci, yel, gk); rows.append(feat(1, yel, r, s, gs, ci, H, V, hist, j, L)); keys.append((1, gk))
        with torch.no_grad():
            pr = net(torch.as_tensor(np.stack(rows))).numpy()
        out = {k: float(v[qi]) for k, v in zip(keys, pr)}
        if debug is not None and len(debug) < 20000:
            for (kind, gk), row, v in zip(keys, rows, pr):
                debug.append((float(t), tid, kind, 0 if kind == 0 else r_of(gs, ci, yel, gk), row.tolist(), float(v[qi])))
        return out, ph, ci, yel, gs

    def spat(tid, link):
        try:
            return _spat(tid, link)
        except Exception:
            stats['exc'] += 1; raise

    def _spat(tid, link):
        if tid not in info.tls:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
        ls = CE.ls; t = ls.simulation.getTime()
        if tid not in stc:
            stc[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = stc[tid]; gs = list(info.tls[tid]['greens']); serve = [gk for gk, g in enumerate(gs) if st[g][link] in 'Gg']
        if len(serve) == len(gs):
            return dict(ttg=0.0, ttr=999.0, valid=True, source='n2k')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        ph = ls.trafficlight.getPhase(tid); ci, yel = cur_index(gs, ph); nx = (ci + 1) % len(gs); stats['valid'] += 1
        if yel and nx in serve:
            stats['fk_direct'] += 1; return fk_spat(tid, link)
        if (not yel) and ci in serve and nx in serve:
            stats['fk_multi'] += 1; return fk_spat(tid, link)
        if cache.get(tid, (None,))[0] != t:
            cache[tid] = (t,) + preds(tid, t)
        pr = cache[tid][1]; stats['n2k'] += 1
        if (not yel) and ci in serve:
            return dict(ttg=0.0, ttr=max(0.0, pr[(0, 0)]), valid=True, source='n2k')
        return dict(ttg=max(0.0, min(pr[(1, gk)] for gk in serve)), ttr=0.0, valid=True, source='n2k')
    spat.stats = stats
    return spat


def parity(Dlog, seed, model):
    greens, _ = greens_of_net(); X, Y, W, KEYS = build([Dlog / f'feat_s{seed}.npz'], greens)
    tm = np.load(Dlog / f'feat_s{seed}.npz', allow_pickle=True)['times']
    off = {(int(tm[i]), tid, kind, r): x for (fi, i, tid, kind, r), x in zip(KEYS, X)}
    d = torch.load(model, weights_only=False); net = NF.QNet(d['d']); net.load_state_dict(d['state']); net.eval()
    rows = json.load(open(Dlog / f'provider_rows_s{seed}.json')); fm = pm = n = cens = 0
    for t, tid, kind, r, row, v in rows:
        key = (int(t), tid, kind, r)
        if key not in off:
            cens += 1; continue
        n += 1; x = off[key]; fm += not np.allclose(x, np.array(row, np.float32), atol=1e-5)
        with torch.no_grad():
            pv = float(net(torch.as_tensor(x[None]))[0, 1])
        pm += abs(pv - v) > 1e-4
    ok = n > 100 and fm == 0 and pm == 0
    print(f'KS-1 compared {n} provider rows ({cens} not in offline: censored or end); feature mismatches {fm}; prediction mismatches {pm} -> {"PASS" if ok else "FAIL"}')
    return ok


if __name__ == '__main__':
    if sys.argv[1] == 'fit':
        fit(Path(sys.argv[2]), Path(sys.argv[3]))
    elif sys.argv[1] == 'parity':
        sys.exit(0 if parity(Path(sys.argv[2]), int(sys.argv[3]), sys.argv[4]) else 1)
