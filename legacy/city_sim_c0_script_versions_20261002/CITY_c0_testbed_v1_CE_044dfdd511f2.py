#!/usr/bin/env python3
"""C0 testbed (02/10/2026 18:0x EDT; research/city_sim/PROTOCOL_CITY_C0_20261002.md): learned cars under a light upgrade.
One approach, one stop line; the light's phase durations come from a light POLICY (FT = 30, ACT = U{20..40} the training
partner, EXT = U{20..70} an upgrade that extends phases, CUT = U{5..40} an upgrade that switches earlier inside the trained
range).  Teacher = exact DP with the whole future schedule; students = MLPs cloned from the teacher on noise-injected teacher
rollouts: Z (compiled silence: x, v, colour, time in phase) and M (plus the SPaT residual).  Primary metric: regret = cost −
teacher cost on a shared evaluation panel.  Variants of Z_ACT: CLIP, MONITOR + FALLBACK (rule car), RELABEL (quantile transport).
Self-check: replaying the teacher's own argmin actions through the rollout code reproduces the DP optimum exactly.
Usage: CITY_c0_testbed.py --out <dir> [--smoke] [--seeds 0 1 2 3 4]"""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ACC = np.array([-3, -2, -1, 0, 1, 2]); NA = len(ACC); VMAX = 14; XM = 250; T = 150
PV, IDLE, TIMEOUT = 20.0, 1.0, 50.0
POL = {'FT': (30, 30), 'ACT': (20, 40), 'EXT': (20, 70), 'CUT': (5, 40)}
LIGHTS = ['FT', 'ACT', 'EXT', 'CUT']; TRAIN_SETS = ['FT', 'ACT', 'EXT', 'CUT', 'MIX']; EPS = (0.0, 0.1, 0.3, 0.5)

VS = np.arange(VMAX + 1)
V2 = np.clip(VS[:, None] + ACC[None, :], 0, VMAX)                     # (V, A)
X2 = np.arange(-XM, 0)[:, None, None] + V2[None]                         # (X, V, A)
PASS = X2 >= 0
X2I = np.clip(X2 + XM, 0, XM - 1); V2B = np.broadcast_to(V2[None], X2.shape)
STEP = 1.0 + 0.05 * ACC.astype(float) ** 2                               # (A,)
CONT_C = STEP[None, None, :] + IDLE * (V2B == 0)                         # stage cost when not passing


def schedule(pol, rng):
    lo, hi = POL[pol]; col = bool(rng.random() < 0.5); dur = int(rng.integers(lo, hi + 1)); el = int(rng.integers(0, dur))
    green = np.zeros(T + 2, bool); tau = np.zeros(T + 2, np.int32); res = np.zeros(T + 2, np.int32)
    for t in range(T + 2):
        green[t], tau[t], res[t] = col, el, dur - el
        el += 1
        if el >= dur:
            col, dur, el = not col, int(rng.integers(lo, hi + 1)), 0
    return green, tau, res


def dp(green):
    """Q[t, x + XM, v, a] = optimal cost-to-go after taking a at (t, x, v) with the whole schedule known."""
    Q = np.empty((T, XM, VMAX + 1, NA)); Vn = np.full((XM, VMAX + 1), TIMEOUT)
    for t in range(T - 1, -1, -1):
        cont = CONT_C + Vn[X2I, V2B]
        pas = STEP[None, None, :] if green[t + 1] else STEP[None, None, :] + PV + IDLE + Vn[XM - 1, 0]
        q = np.where(PASS, pas, cont); Q[t] = q; Vn = q.min(-1)
    return Q, Vn


def dp_vtab(green):
    """Vtab[t, x + XM, v] = optimal cost-to-go at (t, x, v) (Vtab[T] = timeout), float32, for on-policy (DAgger) labels."""
    Vt = np.empty((T + 1, XM, VMAX + 1), np.float32); Vn = np.full((XM, VMAX + 1), TIMEOUT); Vt[T] = Vn
    for t in range(T - 1, -1, -1):
        cont = CONT_C + Vn[X2I, V2B]
        pas = STEP[None, None, :] if green[t + 1] else STEP[None, None, :] + PV + IDLE + Vn[XM - 1, 0]
        Vn = np.where(PASS, pas, cont).min(-1); Vt[t] = Vn
    return Vt


def dp_batch(greens, tab=True, dtype=np.float32):
    """Batched DP over episodes: Vtab (n, T+1, XM, V) if tab else V0 (n, XM, V); same recursion as dp()."""
    n = len(greens); Vn = np.full((n, XM, VMAX + 1), TIMEOUT, dtype)
    Vt = np.empty((n, T + 1, XM, VMAX + 1), dtype) if tab else None
    if tab:
        Vt[:, T] = Vn
    for t in range(T - 1, -1, -1):
        cont = CONT_C[None] + Vn[:, X2I, V2B]
        g = greens[:, t + 1][:, None, None, None]
        pas = np.where(g, STEP[None, None, None, :], STEP[None, None, None, :] + PV + IDLE + Vn[:, XM - 1, 0][:, None, None, None])
        Vn = np.where(PASS[None], pas, cont).min(-1).astype(dtype)
        if tab:
            Vt[:, t] = Vn
    return Vt if tab else Vn


def teacher_act(Vt1, gnext, x, v):
    """argmin_a of the teacher's Q at (x, v) given the next-step values Vt1 (n, XM, V) of each episode."""
    k = np.arange(len(x)); qs = []
    for j, a in enumerate(ACC):
        v2 = np.clip(v + a, 0, VMAX); x2 = x + v2; pas = x2 >= 0
        qp = np.where(gnext, STEP[j], STEP[j] + PV + IDLE + Vt1[k, XM - 1, 0])
        qc = STEP[j] + IDLE * (v2 == 0) + Vt1[k, np.clip(x2 + XM, 0, XM - 1), v2]
        qs.append(np.where(pas, qp, qc))
    return np.stack(qs, 1).argmin(1)


def dagger_data(net, msg, pols, n, rng, chunk=100):
    """Roll out the CURRENT student on fresh episodes and label every visited state with the teacher's action."""
    O, Y = [], []
    for c0 in range(0, n, chunk):
        m = min(chunk, n - c0); G, TA, RS, VT = [], [], [], []
        for _ in range(m):
            g, ta, rs = schedule(pols[int(rng.integers(len(pols)))], rng); G.append(g); TA.append(ta); RS.append(rs)
        G, TA, RS = np.array(G), np.array(TA), np.array(RS); VT = dp_batch(G)
        x = -rng.integers(150, 251, m); v = rng.integers(8, 13, m); alive = np.ones(m, bool)
        for t in range(T):
            idx = np.flatnonzero(alive)
            if len(idx) == 0:
                break
            lab = teacher_act(VT[idx, t + 1], G[idx, t + 1], x[idx], v[idx])
            O.append(np.stack([x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t]], 1).astype(np.float64)); Y.append(lab)
            with torch.no_grad():
                ai = net(torch.as_tensor(feats(x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t], msg))).argmax(1).numpy()
            x2, v2, _, passed, _ = step(x[idx], v[idx], ai, G[idx, t + 1]); x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    return np.concatenate(O), np.concatenate(Y)


def step(x, v, ai, green_next):
    a = ACC[ai]; v2 = np.clip(v + a, 0, VMAX); x2 = x + v2
    forced = (x2 >= 0) & ~green_next; passed = (x2 >= 0) & green_next
    x2 = np.where(forced, -1, x2); v2 = np.where(forced, 0, v2)
    cost = 1.0 + 0.05 * a ** 2 + PV * forced + IDLE * ((~passed) & (v2 == 0))
    return x2, v2, cost, passed, forced


def feats(x, v, g, tau, res, msg):
    f = [x / 200.0, v / 14.0, g.astype(np.float32), tau / 60.0] + ([res / 60.0] if msg else [])
    return np.stack(f, -1).astype(np.float32)


def gen_train(pol, n, rng):
    O, Y = [], []
    for _ in range(n):
        green, tau, res = schedule(pol, rng); Q, _ = dp(green)
        L0, v0 = int(rng.integers(150, 251)), int(rng.integers(8, 13))
        for eps in EPS:
            x, v = -L0, v0
            for t in range(T):
                ast = int(Q[t, x + XM, v].argmin()); O.append((x, v, green[t], tau[t], res[t])); Y.append(ast)
                ai = ast if rng.random() >= eps else int(rng.integers(NA))
                x2, v2, _, passed, _ = step(np.array([x]), np.array([v]), np.array([ai]), np.array([green[t + 1]]))
                if passed[0]:
                    break
                x, v = int(x2[0]), int(v2[0])
    O = np.array(O, np.float64); return O, np.array(Y, np.int64)


def gen_train_batch(pol, n, rng, chunk=100):
    O, Y = [], []
    for c0 in range(0, n, chunk):
        m = min(chunk, n - c0); S = [schedule(pol, rng) for _ in range(m)]
        G = np.array([q[0] for q in S]); TA = np.array([q[1] for q in S]); RS = np.array([q[2] for q in S]); VT = dp_batch(G)
        L0 = rng.integers(150, 251, m); V0 = rng.integers(8, 13, m)
        for eps in EPS:
            x = -L0.copy(); v = V0.copy(); alive = np.ones(m, bool)
            for t in range(T):
                idx = np.flatnonzero(alive)
                if len(idx) == 0:
                    break
                lab = teacher_act(VT[idx, t + 1], G[idx, t + 1], x[idx], v[idx])
                O.append(np.stack([x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t]], 1).astype(np.float64)); Y.append(lab)
                ai = np.where(rng.random(len(idx)) >= eps, lab, rng.integers(0, NA, len(idx)))
                x2, v2, _, passed, _ = step(x[idx], v[idx], ai, G[idx, t + 1]); x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    return np.concatenate(O), np.concatenate(Y)


def make_panel(pol, n, seed, with_q=0):
    rng = np.random.default_rng(seed); S = [schedule(pol, rng) for _ in range(n)]
    G = np.array([q[0] for q in S]); TA = np.array([q[1] for q in S]); R = np.array([q[2] for q in S])
    x0 = -rng.integers(150, 251, n); v0 = rng.integers(8, 13, n); topt = np.empty(n)
    for c0 in range(0, n, 200):
        V0 = dp_batch(G[c0:c0 + 200], tab=False, dtype=np.float64); k = np.arange(len(V0))
        topt[c0:c0 + 200] = V0[k, x0[c0:c0 + 200] + XM, v0[c0:c0 + 200]]
    Qs = [dp(G[i])[0] for i in range(min(with_q, n))]
    for i in range(len(Qs)):                         # self-check: batched DP = scalar DP
        assert abs(Qs[i][0, x0[i] + XM, v0[i]].min() - topt[i]) < 1e-9, (i, Qs[i][0, x0[i] + XM, v0[i]].min(), topt[i])
    return dict(green=G, tau=TA, res=R, x0=x0, v0=v0, topt=topt, Q=Qs)


def rollout(act_fn, P, n=None, record=False):
    N = len(P['x0']) if n is None else n; x = P['x0'][:N].copy(); v = P['v0'][:N].copy(); alive = np.ones(N, bool)
    cost = np.zeros(N); viol = np.zeros(N); stops = np.zeros(N); rec = []
    for t in range(T):
        idx = np.flatnonzero(alive)
        if len(idx) == 0:
            break
        g, ta, rs = P['green'][idx, t], P['tau'][idx, t], P['res'][idx, t]
        ai = act_fn(x[idx], v[idx], g, ta, rs, idx, t)
        if record:
            rec.append(np.stack([g.astype(np.int32), ta], 1))
        x2, v2, c, passed, forced = step(x[idx], v[idx], ai, P['green'][idx, t + 1])
        cost[idx] += c; viol[idx] += forced; stops[idx] += (v2 == 0) & ~passed
        x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    cost[alive] += TIMEOUT
    out = dict(regret=cost - P['topt'][:N], viol=viol, stops=stops, timeouts=alive.astype(float))
    if record:
        out['gt'] = np.concatenate(rec) if rec else np.zeros((0, 2), np.int32)
    return out


def train_net(O, Y, msg, seed, epochs, net=None):
    torch.manual_seed(seed); X = torch.as_tensor(feats(O[:, 0], O[:, 1], O[:, 2] > 0.5, O[:, 3], O[:, 4], msg)); Yt = torch.as_tensor(Y)
    if net is None:
        net = nn.Sequential(nn.Linear(X.shape[1], 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, NA))
    opt = torch.optim.Adam(net.parameters(), 1e-3); lf = nn.CrossEntropyLoss(); g = torch.Generator().manual_seed(seed); last = 0.0
    for _ in range(epochs):
        perm = torch.randperm(len(X), generator=g); tot = 0.0
        for i in range(0, len(X), 2048):
            b = perm[i:i + 2048]; loss = lf(net(X[b]), Yt[b]); opt.zero_grad(); loss.backward(); opt.step(); tot += loss.item() * len(b)
        last = tot / len(X)
    with torch.no_grad():
        acc = float((net(X).argmax(1) == Yt).float().mean())
    return net, last, acc


def net_policy(net, msg, tau_map=None, fallback=None, tmax=None):
    def f(x, v, g, ta, rs, idx, t):
        ta2 = ta if tau_map is None else tau_map(g, ta)
        with torch.no_grad():
            a = net(torch.as_tensor(feats(x, v, g, ta2, rs, msg))).argmax(1).numpy()
        if fallback is not None:
            oos = ta > np.where(g, tmax[1], tmax[0]); a = np.where(oos, fallback(x, v, g, ta, rs, idx, t), a)
        return a
    return f


def rule_policy(x, v, g, ta, rs, idx, t):
    dist = -x; sd = v * v / 6.0 + v
    a = np.where(v < 12, 2, np.where(v > 12, -1, 0))
    a = np.where((~g) & (dist <= 2 * sd + 20), -1, a); a = np.where((~g) & (dist <= sd + 6), -3, a)
    return np.searchsorted(ACC, a)


def quantile_map(dep_gt, tr_gt):
    """Per colour, τ → F_train^{-1}(F_dep(τ)) with mid-rank empirical CDFs."""
    maps = {}
    for c in (0, 1):
        d = np.sort(dep_gt[dep_gt[:, 0] == c, 1]); r = np.sort(tr_gt[tr_gt[:, 0] == c, 1]); maps[c] = (d, r)

    def m(g, ta):
        out = ta.astype(np.float64).copy()
        for c in (0, 1):
            d, r = maps[c]; sel = (g.astype(int) == c)
            if sel.any() and len(d) and len(r):
                q = (np.searchsorted(d, ta[sel], 'left') + np.searchsorted(d, ta[sel], 'right')) / (2.0 * len(d))
                out[sel] = np.quantile(r, np.clip(q, 0, 1))
        return out
    return m


def w1(a, b):
    qs = np.linspace(0.0005, 0.9995, 1000); return float(np.mean(np.abs(np.quantile(a, qs) - np.quantile(b, qs))))


def boot_diff(d, reps=2000, seed=0):
    """d: (S, E) paired differences; resample seeds and episodes."""
    rng = np.random.default_rng(seed); S, E = d.shape; m = []
    for _ in range(reps):
        ss = rng.integers(0, S, S); ee = rng.integers(0, E, E); m.append(d[np.ix_(ss, ee)].mean())
    return [float(np.percentile(m, 2.5)), float(np.percentile(m, 97.5))]


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); torch.set_num_threads(1)
    NTR, NEV, NCAL, EPO = (40, 80, 40, 2) if a.smoke else (3000, 3000, 1000, 8)
    if a.sizes:                                       # development override (not the protocol's sizes)
        NTR, NEV, NCAL, EPO = a.sizes
    DROUNDS, ND, EPD = (1, 20, 1) if a.smoke and not a.sizes else (2, NTR // 3, 4)
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); t0 = time.perf_counter()
    print(f'C0 start smoke={a.smoke} seeds={a.seeds} NTR={NTR} NEV={NEV}', flush=True)
    panels = {L: make_panel(L, NEV, 9000 + i, with_q=20) for i, L in enumerate(LIGHTS)}
    calib = {L: make_panel(L, NCAL, 9500 + i) for i, L in enumerate(LIGHTS)}
    # self-check: the teacher's own argmin actions through the rollout code reproduce the DP optimum
    chk = {}
    for L, P in panels.items():
        Qs = P['Q']; r = rollout(lambda x, v, g, ta, rs, idx, t: np.array([int(Qs[i][t, xx + XM, vv].argmin()) for i, xx, vv in zip(idx, x, v)]), P, n=len(Qs))
        chk[L] = float(np.abs(r['regret']).max())
    assert max(chk.values()) < 1e-9, chk
    print(f'self-check PASS (teacher replay max |regret| {max(chk.values()):.2e})  [{time.perf_counter() - t0:.0f}s]', flush=True)
    rule = {L: rollout(rule_policy, panels[L]) for L in LIGHTS}
    R = dict(source_sha256=src, protocol='research/city_sim/PROTOCOL_CITY_C0_20261002.md', smoke=a.smoke, sizes=dict(NTR=NTR, NEV=NEV, NCAL=NCAL, EPO=EPO),
             self_check=chk, rule={L: dict(regret=float(rule[L]['regret'].mean()), viol=float(rule[L]['viol'].mean())) for L in LIGHTS}, seeds={})
    REG = {}                                          # (seed, cell) -> per-episode regret, cell = (student, light, variant)
    for s in a.seeds:
        rng = np.random.default_rng(1000 + s); data = {L: gen_train_batch(L, NTR, rng) for L in ['FT', 'ACT', 'EXT', 'CUT']}
        k = len(data['ACT'][1]) // 3; mix_rng = np.random.default_rng(2000 + s)
        mO, mY = [], []
        for L in ('ACT', 'EXT', 'CUT'):
            O, Y = data[L]; i = mix_rng.choice(len(Y), k, replace=False); mO.append(O[i]); mY.append(Y[i])
        data['MIX'] = (np.concatenate(mO), np.concatenate(mY))
        tmax = {L: (int(data[L][0][data[L][0][:, 2] < 0.5, 3].max()), int(data[L][0][data[L][0][:, 2] > 0.5, 3].max())) for L in TRAIN_SETS}
        print(f'seed {s}: data {[len(data[L][1]) for L in TRAIN_SETS]} tmax ACT {tmax["ACT"]}  [{time.perf_counter() - t0:.0f}s]', flush=True)
        nets, info = {}, {}
        for L in TRAIN_SETS:
            for msg in (False, True):
                nm = ('M_' if msg else 'Z_') + L; sd = 100 * s + len(nets); net, loss, acc = train_net(*data[L], msg, sd, EPO)
                O, Y = data[L]; drng = np.random.default_rng(3000 + sd); pols = ['ACT', 'EXT', 'CUT'] if L == 'MIX' else [L]
                for r in range(DROUNDS):                  # Deviation 1: DAgger rounds after the noise-injected cloning
                    Od, Yd = dagger_data(net, msg, pols, ND, drng); O, Y = np.concatenate([O, Od]), np.concatenate([Y, Yd])
                    net, loss, acc = train_net(O, Y, msg, sd + 1 + r, EPD, net=net)
                nets[nm] = (net, msg); info[nm] = dict(loss=loss, train_acc=acc, n_samples=int(len(Y)))
        print(f'seed {s}: trained {len(nets)} students  [{time.perf_counter() - t0:.0f}s]', flush=True)
        cells = {}
        for nm, (net, msg) in nets.items():
            for L in LIGHTS:
                r = rollout(net_policy(net, msg), panels[L]); REG[(s, nm, L, 'plain')] = r['regret']
                cells[f'{nm}|{L}|plain'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()), stops=float(r['stops'].mean()), timeouts=float(r['timeouts'].mean()))
        zact = nets['Z_ACT'][0]; tm = tmax['ACT']
        tr_gt = rollout(net_policy(zact, False), calib['ACT'], record=True)['gt']
        for L in ('EXT', 'CUT', 'ACT'):
            rec = rollout(net_policy(zact, False), panels[L], record=True); gt = rec['gt']
            oos = float(np.mean(gt[:, 1] > np.where(gt[:, 0] == 1, tm[1], tm[0])))
            cells[f'Z_ACT|{L}|oos_mass'] = oos; cells[f'Z_ACT|{L}|w1_tau'] = w1(gt[:, 1], tr_gt[:, 1])
            variants = dict(clip=net_policy(zact, False, tau_map=lambda g, ta, tm=tm: np.minimum(ta, np.where(g, tm[1], tm[0]))),
                            fallback=net_policy(zact, False, fallback=rule_policy, tmax=tm))
            dep_gt = rollout(net_policy(zact, False), calib[L], record=True)['gt']
            variants['relabel'] = net_policy(zact, False, tau_map=quantile_map(dep_gt, tr_gt))
            for vn, pf in variants.items():
                r = rollout(pf, panels[L]); REG[(s, 'Z_ACT', L, vn)] = r['regret']
                cells[f'Z_ACT|{L}|{vn}'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()), stops=float(r['stops'].mean()))
        R['seeds'][str(s)] = dict(cells=cells, train=info, tmax=tmax)
        print(f'seed {s}: Z_ACT on EXT {cells["Z_ACT|EXT|plain"]["regret"]:.2f} (spec {cells["Z_EXT|EXT|plain"]["regret"]:.2f}, FB {cells["Z_ACT|EXT|fallback"]["regret"]:.2f}, '
              f'M_ACT {cells["M_ACT|EXT|plain"]["regret"]:.2f}); on CUT {cells["Z_ACT|CUT|plain"]["regret"]:.2f} (spec {cells["Z_CUT|CUT|plain"]["regret"]:.2f}, '
              f'M_ACT {cells["M_ACT|CUT|plain"]["regret"]:.2f}); oos EXT {cells["Z_ACT|EXT|oos_mass"]:.3f} CUT {cells["Z_ACT|CUT|oos_mass"]:.3f}  [{time.perf_counter() - t0:.0f}s]', flush=True)
    S = a.seeds

    def M(nm, L, vn='plain'):
        return np.array([REG[(s, nm, L, vn)] for s in S])

    def mean(nm, L, vn='plain'):
        return float(M(nm, L, vn).mean())
    pred = {}
    for P in ('EXT', 'CUT'):
        d = M('Z_ACT', P) - M(f'Z_{P}', P); dm = M('M_ACT', P) - M(f'M_{P}', P)
        pred[f'C0-1 Delta({P})'] = dict(mean=float(d.mean()), ci=boot_diff(d), pass_=bool(boot_diff(d)[0] > 0))
        pred[f'C0-3 DeltaM({P}) <= Delta/4'] = dict(deltaM=float(dm.mean()), delta=float(d.mean()), pass_=bool(dm.mean() <= d.mean() / 4))
        pred[f'C0-5 relabel worse on {P}'] = dict(relabel=mean('Z_ACT', P, 'relabel'), plain=mean('Z_ACT', P), pass_=bool(mean('Z_ACT', P, 'relabel') > mean('Z_ACT', P)))
    oosE = float(np.mean([R['seeds'][str(s)]['cells']['Z_ACT|EXT|oos_mass'] for s in S])); oosC = float(np.mean([R['seeds'][str(s)]['cells']['Z_ACT|CUT|oos_mass'] for s in S]))
    dE = pred['C0-1 Delta(EXT)']['mean']
    pred['C0-2 oos mass'] = dict(EXT=oosE, CUT=oosC, pass_=bool(oosE >= 0.10 and oosC == 0.0))
    pred['C0-2 fallback recovers half of Delta(EXT)'] = dict(fallback=mean('Z_ACT', 'EXT', 'fallback'), plain=mean('Z_ACT', 'EXT'), delta=dE,
                                                            pass_=bool(mean('Z_ACT', 'EXT', 'fallback') <= mean('Z_ACT', 'EXT') - 0.5 * dE))
    ft = abs(mean('Z_FT', 'FT') - mean('M_FT', 'FT'))
    pred['C0-3 FT compiled silence = message'] = dict(diff=ft, bound=0.05 * R['rule']['FT']['regret'], pass_=bool(ft <= 0.05 * R['rule']['FT']['regret']))
    worst = {nm: max(mean(nm, L) for L in ('ACT', 'EXT', 'CUT')) for nm in ('Z_MIX', 'Z_ACT', 'Z_EXT', 'Z_CUT')}
    pred['C0-4 mixture minimax'] = dict(worst=worst, pass_=bool(all(worst['Z_MIX'] <= worst[k] for k in ('Z_ACT', 'Z_EXT', 'Z_CUT'))))
    R['predictions'] = pred
    tab = {nm: {L: mean(nm, L) for L in LIGHTS} for nm in [('Z_' if z else 'M_') + L for z in (True, False) for L in TRAIN_SETS]}
    R['regret_table'] = tab; R['elapsed_s'] = time.perf_counter() - t0
    (out / 'result.json').write_text(json.dumps(R, indent=1))
    np.savez_compressed(out / 'regrets.npz', **{'|'.join(map(str, k)): v for k, v in REG.items()})
    L1 = ['C0 regret table (mean over seeds; rows = student, columns = deployment light)', 'student | ' + ' | '.join(LIGHTS)]
    L1 += [f'{nm} | ' + ' | '.join(f'{tab[nm][L]:.2f}' for L in LIGHTS) for nm in tab]
    L1 += ['rule car | ' + ' | '.join(f'{R["rule"][L]["regret"]:.2f}' for L in LIGHTS)]
    L1 += [f'Z_ACT variants: ' + '; '.join(f'{L}: plain {mean("Z_ACT", L):.2f} clip {mean("Z_ACT", L, "clip"):.2f} fallback {mean("Z_ACT", L, "fallback"):.2f} relabel {mean("Z_ACT", L, "relabel"):.2f}' for L in ('ACT', 'EXT', 'CUT'))]
    L1 += [f'W1(tau) EXT {np.mean([R["seeds"][str(s)]["cells"]["Z_ACT|EXT|w1_tau"] for s in S]):.2f} CUT {np.mean([R["seeds"][str(s)]["cells"]["Z_ACT|CUT|w1_tau"] for s in S]):.2f}']
    L1 += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L1); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4])
    ap.add_argument('--sizes', type=int, nargs=4, default=None, help='development override: NTR NEV NCAL EPOCHS')
    main(ap.parse_args())
