#!/usr/bin/env python3
"""C0 testbed v3 (02/10/2026; research/city_sim/PROTOCOL_CITY_C0_20261002.md with Deviations 1–3 and Addenda C0b, C0c): learned
cars under a light upgrade.  One approach, one stop line; the light's phase durations come from a light POLICY (FT = 30,
ACT = U{20..40} the training partner, EXT = U{20..70}, CUT = U{5..40}; Addendum lights A1–A6; PROBE = U{12..48}).  The light is
a stationary renewal process (first phase length-biased, Deviation 3).
Teachers (Deviation 3): exact Bayes-optimal action values of each information set, by value iteration on a finite stationary
MDP — Z* on (x, v, colour, τ) with the duration law's hazard; M* on (x, v, colour, r) with the next duration drawn from the law.
Students: MLPs regressing their own table's values at states visited by the ε-noisy table driver and by the student (2 DAgger
rounds); act by argmin.  Metric: regret = cost − PRIVILEGED teacher cost (exact DP with the whole schedule) on shared panels.
Variants of Z_ACT: CLIP, MONITOR + FALLBACK (rule car), RELABEL.  Exact references: Z*_L, M*_L tables (τ or r clipped).
Modes: --panels L [L ...] (panels + Bayes tables + self-checks) | --seed S [--extra] | --merge
Usage: CITY_c0_testbed.py --out DIR (--panels L.. | --seed S [--extra] | --merge) [--smoke] [--sizes NTR NEV NCAL EPO]"""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ACC = np.array([-3, -2, -1, 0, 1, 2]); NA = len(ACC); VMAX = 14; XM = 250; T = 150
PV, IDLE, TIMEOUT = 20.0, 1.0, 50.0
POL = {'FT': (30, 30), 'ACT': (20, 40), 'EXT': (20, 70), 'CUT': (5, 40),
       'A1': (10, 40), 'A2': (15, 35), 'A3': (20, 50), 'A4': (25, 45), 'A5': (30, 60), 'A6': (20, 30),
       'PROBE': (12, 48)}                                # Addendum C0c: the standard probe light (receiver fragility)
MAIN = ['FT', 'ACT', 'EXT', 'CUT']; EXTRA = ['A1', 'A2', 'A3', 'A4', 'A5', 'A6']; LIGHTS = MAIN + EXTRA
PANEL_SEED = {**{L: 9000 + i for i, L in enumerate(MAIN)}, **{L: 9100 + i for i, L in enumerate(EXTRA)}, 'PROBE': 9300}
LOG_SEED = {L: 7000 + i for i, L in enumerate(LIGHTS)}
EPS = (0.0, 0.1, 0.3, 0.5); QS = 10.0

VS = np.arange(VMAX + 1)
V2 = np.clip(VS[:, None] + ACC[None, :], 0, VMAX)                     # (V, A)
X2 = np.arange(-XM, 0)[:, None, None] + V2[None]                         # (X, V, A)
PASS = X2 >= 0
X2I = np.clip(X2 + XM, 0, XM - 1); V2B = np.broadcast_to(V2[None], X2.shape)
STEP = 1.0 + 0.05 * ACC.astype(float) ** 2
CONT_C = STEP[None, None, :] + IDLE * (V2B == 0)


def law(L):
    lo, hi = POL[L]; d = np.arange(lo, hi + 1); return d, np.full(len(d), 1.0 / len(d))


def schedule(pol, rng):
    """Stationary renewal light (Deviation 3): first phase length-biased, elapsed time uniform within it."""
    d, p = law(pol); col = bool(rng.random() < 0.5); w = d * p
    dur = int(rng.choice(d, p=w / w.sum())); el = int(rng.integers(0, dur))
    green = np.zeros(T + 2, bool); tau = np.zeros(T + 2, np.int32); res = np.zeros(T + 2, np.int32)
    for t in range(T + 2):
        green[t], tau[t], res[t] = col, el, dur - el
        el += 1
        if el >= dur:
            col, dur, el = not col, int(rng.choice(d, p=p)), 0
    return green, tau, res


# ---------------------------------------------------------------- privileged teacher (whole schedule known): the regret metric
def dp(green):
    Q = np.empty((T, XM, VMAX + 1, NA)); Vn = np.full((XM, VMAX + 1), TIMEOUT)
    for t in range(T - 1, -1, -1):
        cont = CONT_C + Vn[X2I, V2B]
        pas = STEP[None, None, :] if green[t + 1] else STEP[None, None, :] + PV + IDLE + Vn[XM - 1, 0]
        q = np.where(PASS, pas, cont); Q[t] = q; Vn = q.min(-1)
    return Q, Vn


def dp_batch(greens, tab=True, dtype=np.float32):
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


def teacher_q(Vt1, gnext, x, v):
    k = np.arange(len(x)); qs = []
    for j, a in enumerate(ACC):
        v2 = np.clip(v + a, 0, VMAX); x2 = x + v2; pas = x2 >= 0
        qp = np.where(gnext, STEP[j], STEP[j] + PV + IDLE + Vt1[k, XM - 1, 0])
        qc = STEP[j] + IDLE * (v2 == 0) + Vt1[k, np.clip(x2 + XM, 0, XM - 1), v2]
        qs.append(np.where(pas, qp, qc))
    return np.stack(qs, 1).astype(np.float32)


# ---------------------------------------------------------------- exact Bayes-optimal tables of the two information sets
def _backup_Z(V, h):
    """One Bellman backup of the Z MDP: V (X, V, 2, TM) -> Q (X, V, 2, TM, NA).  colour index 1 = green."""
    X, Vv, _, TM = V.shape; tn = np.minimum(np.arange(TM) + 1, TM - 1); gG = (np.arange(2) == 1)[None, None, :, None]
    Q = np.empty(V.shape + (NA,))
    for j in range(NA):
        G = V[X2I[:, :, j], V2[None, :, j]]                              # (X, V, 2, TM): value at the next (x, v), same colour
        ns, sw = G[..., tn], G[:, :, ::-1, :1]                           # no switch: τ+1, same colour; switch: other colour, τ 0
        fns, fsw = V[XM - 1, 0][:, tn][None, None], V[XM - 1, 0][::-1, :1][None, None]
        pas = PASS[:, :, j][:, :, None, None]; idle = IDLE * (V2[:, j] == 0)[None, :, None, None]
        Bns = np.where(pas, np.where(gG, STEP[j], STEP[j] + PV + IDLE + fns), STEP[j] + idle + ns)
        Bsw = np.where(pas, np.where(~gG, STEP[j], STEP[j] + PV + IDLE + fsw), STEP[j] + idle + sw)
        Q[..., j] = (1 - h) * Bns + h * Bsw
    return Q


def _backup_M(V, pD, dvals):
    """One Bellman backup of the M MDP: V (X, V, 2, RM) with index k = r − 1."""
    RM = V.shape[3]; Vexp = np.tensordot(V[..., dvals - 1], pD, axes=([3], [0]))      # (X, V, 2): value at the start of a phase
    gG = (np.arange(2) == 1)[None, None, :, None]; Q = np.empty(V.shape + (NA,))
    gnext = np.concatenate([~gG, np.broadcast_to(gG, (1, 1, 2, RM - 1))], axis=3) if RM > 1 else ~gG
    for j in range(NA):
        G = V[X2I[:, :, j], V2[None, :, j]]; Ge = Vexp[X2I[:, :, j], V2[None, :, j]]
        nxt = np.concatenate([Ge[:, :, ::-1, None], G[..., :-1]], axis=3)
        frc = np.concatenate([Vexp[XM - 1, 0][::-1, None], V[XM - 1, 0][:, :-1]], axis=1)[None, None]
        pas = PASS[:, :, j][:, :, None, None]; idle = IDLE * (V2[:, j] == 0)[None, :, None, None]
        Q[..., j] = np.where(pas, np.where(gnext, STEP[j], STEP[j] + PV + IDLE + frc), STEP[j] + idle + nxt)
    return Q


def bayes_tables(L, tol=1e-7, max_it=2000):
    d, p = law(L); hi = int(d.max())
    surv = np.array([p[d >= t + 1].sum() for t in range(hi)]); end = np.array([p[d == t + 1].sum() for t in range(hi)])
    h = np.where(surv > 0, end / np.maximum(surv, 1e-300), 1.0)
    out = {}
    for kind in ('Z', 'M'):
        V = np.zeros((XM, VMAX + 1, 2, hi))
        for it in range(max_it):
            Q = _backup_Z(V, h) if kind == 'Z' else _backup_M(V, p, d)
            Vn = Q.min(-1); delta = float(np.abs(Vn - V).max()); V = Vn
            if delta < tol:
                break
        out[kind] = V.astype(np.float32); out[kind + '_iters'] = it + 1; out[kind + '_delta'] = delta
    out['h'] = h
    return out


def table_q(V, kind, L, x, v, g, ta, rs):
    """Action values of the table V (Bayes-optimal of law L) at a batch of states (τ / r clipped to the table)."""
    d, p = law(L); hi = V.shape[3]
    if kind == 'Z':
        Q = _backup_Z_at(V, x, v, g, np.minimum(ta, hi - 1), d, p)
    else:
        Q = _backup_M_at(V, x, v, g, np.clip(rs, 1, hi), d, p)
    return Q


def _backup_Z_at(V, x, v, g, ta, d, p):
    hi = V.shape[3]; surv = np.array([p[d >= t + 1].sum() for t in range(hi)]); end = np.array([p[d == t + 1].sum() for t in range(hi)])
    h = np.where(surv > 0, end / np.maximum(surv, 1e-300), 1.0)[ta]; gi = g.astype(int); tn = np.minimum(ta + 1, hi - 1); qs = []
    for j, a in enumerate(ACC):
        v2 = np.clip(v + a, 0, VMAX); x2 = x + v2; pas = x2 >= 0; xi = np.clip(x2 + XM, 0, XM - 1); idle = IDLE * (v2 == 0)
        bns = np.where(pas, np.where(gi == 1, STEP[j], STEP[j] + PV + IDLE + V[XM - 1, 0, gi, tn]), STEP[j] + idle + V[xi, v2, gi, tn])
        bsw = np.where(pas, np.where(gi == 0, STEP[j], STEP[j] + PV + IDLE + V[XM - 1, 0, 1 - gi, 0]), STEP[j] + idle + V[xi, v2, 1 - gi, 0])
        qs.append((1 - h) * bns + h * bsw)
    return np.stack(qs, 1).astype(np.float32)


def _backup_M_at(V, x, v, g, rs, d, p):
    gi = g.astype(int); k = rs - 1; qs = []
    Vexp = np.tensordot(V[..., d - 1], p, axes=([3], [0]))
    for j, a in enumerate(ACC):
        v2 = np.clip(v + a, 0, VMAX); x2 = x + v2; pas = x2 >= 0; xi = np.clip(x2 + XM, 0, XM - 1); idle = IDLE * (v2 == 0)
        last = k == 0; gnext = np.where(last, 1 - gi, gi); km = np.maximum(k - 1, 0)
        nxt = np.where(last, Vexp[xi, v2, 1 - gi], V[xi, v2, gi, km]); frc = np.where(last, Vexp[XM - 1, 0, 1 - gi], V[XM - 1, 0, gi, km])
        qs.append(np.where(pas, np.where(gnext == 1, STEP[j], STEP[j] + PV + IDLE + frc), STEP[j] + idle + nxt))
    return np.stack(qs, 1).astype(np.float32)


# ---------------------------------------------------------------- environment, data, students
def step(x, v, ai, green_next):
    a = ACC[ai]; v2 = np.clip(v + a, 0, VMAX); x2 = x + v2
    forced = (x2 >= 0) & ~green_next; passed = (x2 >= 0) & green_next
    x2 = np.where(forced, -1, x2); v2 = np.where(forced, 0, v2)
    cost = 1.0 + 0.05 * a ** 2 + PV * forced + IDLE * ((~passed) & (v2 == 0))
    return x2, v2, cost, passed, forced


def feats(x, v, g, tau, res, msg):
    f = [x / 200.0, v / 14.0, np.asarray(g, np.float32), tau / 60.0] + ([res / 60.0] if msg else [])
    return np.stack(f, -1).astype(np.float32)


def episodes(pols, n, rng):
    li = rng.integers(0, len(pols), n); S = [schedule(pols[i], rng) for i in li]
    return (np.array([q[0] for q in S]), np.array([q[1] for q in S]), np.array([q[2] for q in S]),
            -rng.integers(150, 251, n), rng.integers(8, 13, n), li)


def collect(pols, tabs, kind, n, rng, drivers, chunk=500):
    """Visited states and Bayes-table labels of the episode's own law.  driver(q, x, v, g, ta, rs) -> actions."""
    O, Y = [], []
    for c0 in range(0, n, chunk):
        m = min(chunk, n - c0); G, TA, RS, X0, V0, LI = episodes(pols, m, rng)
        for drive in drivers:
            x, v, alive = X0.copy(), V0.copy(), np.ones(m, bool)
            for t in range(T):
                idx = np.flatnonzero(alive)
                if len(idx) == 0:
                    break
                q = np.empty((len(idx), NA), np.float32)
                for li in np.unique(LI[idx]):
                    s = idx[LI[idx] == li]; sel = LI[idx] == li
                    q[sel] = table_q(tabs[pols[li]][kind], kind, pols[li], x[s], v[s], G[s, t], TA[s, t], RS[s, t])
                O.append(np.stack([x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t]], 1).astype(np.float64)); Y.append(q)
                ai = drive(q, x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t])
                x2, v2, _, passed, _ = step(x[idx], v[idx], ai, G[idx, t + 1]); x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    return np.concatenate(O), np.concatenate(Y)


def noisy_teacher(eps, rng):
    def d(q, *_):
        a = q.argmin(1); return np.where(rng.random(len(a)) >= eps, a, rng.integers(0, NA, len(a)))
    return d


def student_driver(net, msg):
    def d(q, x, v, g, ta, rs):
        with torch.no_grad():
            return net(torch.as_tensor(feats(x, v, g, ta, rs, msg))).argmin(1).numpy()
    return d


def train_net(O, Y, msg, seed, epochs, net=None):
    torch.manual_seed(seed)
    X = torch.as_tensor(feats(O[:, 0], O[:, 1], O[:, 2] > 0.5, O[:, 3], O[:, 4], msg)); Yt = torch.as_tensor(Y / QS)
    if net is None:
        net = nn.Sequential(nn.Linear(X.shape[1], 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, NA))
    opt = torch.optim.Adam(net.parameters(), 1e-3); g = torch.Generator().manual_seed(seed); last = 0.0
    for _ in range(epochs):
        perm = torch.randperm(len(X), generator=g); tot = 0.0
        for i in range(0, len(X), 2048):
            b = perm[i:i + 2048]; loss = ((net(X[b]) - Yt[b]) ** 2).mean(); opt.zero_grad(); loss.backward(); opt.step(); tot += loss.item() * len(b)
        last = tot / len(X)
    with torch.no_grad():
        agree = float((net(X).argmin(1) == Yt.argmin(1)).float().mean())
    return net, last, agree


def make_panel(L, n, seed, with_q=20):
    rng = np.random.default_rng(seed); G, TA, R, x0, v0, _ = episodes([L], n, rng); topt = np.empty(n)
    for c0 in range(0, n, 200):
        V0 = dp_batch(G[c0:c0 + 200], tab=False, dtype=np.float64); k = np.arange(len(V0))
        topt[c0:c0 + 200] = V0[k, x0[c0:c0 + 200] + XM, v0[c0:c0 + 200]]
    for i in range(min(with_q, n)):
        Q, _ = dp(G[i]); assert abs(Q[0, x0[i] + XM, v0[i]].min() - topt[i]) < 1e-9, ('batched DP', i)
        Vt = dp_batch(G[i:i + 1], dtype=np.float64)[0]; x, v, cost = int(x0[i]), int(v0[i]), 0.0
        for t in range(T):
            qv = teacher_q(Vt[t + 1][None], G[i:i + 1, t + 1], np.array([x]), np.array([v]))[0]
            assert np.abs(qv - Q[t, x + XM, v]).max() < 1e-3, ('teacher_q', i, t)
            a = int(Q[t, x + XM, v].argmin()); x2, v2, c, passed, _ = step(np.array([x]), np.array([v]), np.array([a]), G[i:i + 1, t + 1])
            cost += float(c[0])
            if passed[0]:
                break
            x, v = int(x2[0]), int(v2[0])
        else:
            cost += TIMEOUT
        assert abs(cost - topt[i]) < 1e-9, ('teacher replay', i, cost, topt[i])
    return dict(green=G, tau=TA, res=R, x0=x0, v0=v0, topt=topt)


def rollout(act_fn, P, record=False):
    N = len(P['x0']); x = P['x0'].copy(); v = P['v0'].copy(); alive = np.ones(N, bool)
    cost = np.zeros(N); viol = np.zeros(N); stops = np.zeros(N); rec = []
    for t in range(T):
        idx = np.flatnonzero(alive)
        if len(idx) == 0:
            break
        g, ta, rs = P['green'][idx, t], P['tau'][idx, t], P['res'][idx, t]
        ai = act_fn(x[idx], v[idx], g, ta, rs)
        if record:
            rec.append(np.stack([g.astype(np.int32), ta], 1))
        x2, v2, c, passed, forced = step(x[idx], v[idx], ai, P['green'][idx, t + 1])
        cost[idx] += c; viol[idx] += forced; stops[idx] += (v2 == 0) & ~passed
        x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    cost[alive] += TIMEOUT
    out = dict(regret=cost - P['topt'], viol=viol, stops=stops, timeouts=alive.astype(float))
    if record:
        out['gt'] = np.concatenate(rec) if rec else np.zeros((0, 2), np.int32)
    return out


def net_policy(net, msg, tau_map=None, fallback=None, tmax=None):
    def f(x, v, g, ta, rs):
        ta2 = ta if tau_map is None else tau_map(g, ta)
        with torch.no_grad():
            a = net(torch.as_tensor(feats(x, v, g, ta2, rs, msg))).argmin(1).numpy()
        if fallback is not None:
            a = np.where(ta > np.where(g, tmax[1], tmax[0]), fallback(x, v, g, ta, rs), a)
        return a
    return f


def table_policy(V, kind, L):
    return lambda x, v, g, ta, rs: table_q(V, kind, L, x, v, g, ta, rs).argmin(1)


def rule_policy(x, v, g, ta, rs):
    dist = -x; sd = v * v / 6.0 + v
    a = np.where(v < 12, 2, np.where(v > 12, -1, 0))
    a = np.where((~g) & (dist <= 2 * sd + 20), -1, a); a = np.where((~g) & (dist <= sd + 6), -3, a)
    return np.searchsorted(ACC, a)


def quantile_map(dep_gt, tr_gt):
    maps = {c: (np.sort(dep_gt[dep_gt[:, 0] == c, 1]), np.sort(tr_gt[tr_gt[:, 0] == c, 1])) for c in (0, 1)}

    def m(g, ta):
        out = ta.astype(np.float64).copy()
        for c in (0, 1):
            d, r = maps[c]; sel = (np.asarray(g).astype(int) == c)
            if sel.any() and len(d) and len(r):
                q = (np.searchsorted(d, ta[sel], 'left') + np.searchsorted(d, ta[sel], 'right')) / (2.0 * len(d))
                out[sel] = np.quantile(r, np.clip(q, 0, 1))
        return out
    return m


def w1(a, b):
    qs = np.linspace(0.0005, 0.9995, 1000); return float(np.mean(np.abs(np.quantile(a, qs) - np.quantile(b, qs))))


def load_panel(out, L, kind):
    z = np.load(out / 'panels' / f'{L}_{kind}.npz'); return {k: z[k] for k in z.files}


def load_tables(out, L):
    z = np.load(out / 'panels' / f'{L}_tables.npz'); return {'Z': z['Z'].astype(np.float64), 'M': z['M'].astype(np.float64)}


def run_panels(a, out, sizes):
    NTR, NEV, NCAL, EPO = sizes; (out / 'panels').mkdir(parents=True, exist_ok=True)
    for L in a.panels:
        t0 = time.perf_counter(); tb = bayes_tables(L)
        np.savez_compressed(out / 'panels' / f'{L}_tables.npz', Z=tb['Z'], M=tb['M'], h=tb['h'])
        info = dict(Z_iters=tb['Z_iters'], Z_delta=tb['Z_delta'], M_iters=tb['M_iters'], M_delta=tb['M_delta'])
        for kind, n, sd, wq in (('eval', NEV, PANEL_SEED[L], 20), ('calib', NCAL, PANEL_SEED[L] + 500, 0)):
            np.savez_compressed(out / 'panels' / f'{L}_{kind}.npz', **make_panel(L, n, sd, with_q=wq))
        P = load_panel(out, L, 'eval'); T64 = {k: tb[k].astype(np.float64) for k in ('Z', 'M')}
        rz, rm, rr = (rollout(table_policy(T64['Z'], 'Z', L), P)['regret'].mean(), rollout(table_policy(T64['M'], 'M', L), P)['regret'].mean(),
                      rollout(rule_policy, P)['regret'].mean())
        assert rz <= rr + 0.3, ('Z* must not lose to the rule car on its own light', L, rz, rr)   # rule car uses a subset of Z's view
        assert rm <= rz + 0.3, ('M* must not lose to Z* on its own light', L, rm, rz)              # M sees more than Z
        if L == 'FT':                                                       # deterministic light: r = 30 − τ, Z* = M* exactly
            assert abs(rz - rm) < 1e-9, ('FT: Z* and M* must coincide', rz, rm)
        info.update(Zstar=float(rz), Mstar=float(rm), rule=float(rr))
        (out / 'panels' / f'{L}_info.json').write_text(json.dumps(info))
        print(f'panel {L}: tables Z {tb["Z_iters"]} it / M {tb["M_iters"]} it; regret Z* {rz:.2f} M* {rm:.2f} rule {rr:.2f}; self-checks PASS  '
              f'[{time.perf_counter() - t0:.0f}s]', flush=True)


def run_seed(a, out, sizes):
    NTR, NEV, NCAL, EPO = sizes
    DROUNDS, ND, EPD = (1, max(10, NTR // 3), 1) if (a.smoke and not a.sizes) else (2, NTR // 3, 4)
    s = a.seed; sd_dir = out / f'seed_{s}'; sd_dir.mkdir(parents=True, exist_ok=a.smoke); t0 = time.perf_counter()
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()          # provenance: the source that runs, read at the start
    lights = MAIN + (EXTRA if (a.extra and s <= 2) else [])
    panels = {L: load_panel(out, L, 'eval') for L in lights}; calib = {L: load_panel(out, L, 'calib') for L in ('ACT', 'EXT', 'CUT')}
    tabs = {L: load_tables(out, L) for L in lights}
    train_sets = list(lights) + ['MIX']; nets, info = {}, {}; tmax = {}
    for L in train_sets:
        pols = ['ACT', 'EXT', 'CUT'] if L == 'MIX' else [L]
        for msg in (False, True):
            kind = 'M' if msg else 'Z'; nm = kind + '_' + L; sdn = 100 * s + len(nets)
            rng = np.random.default_rng([1000 + s, sdn]); trng = np.random.default_rng([5000 + s, sdn])
            O, Y = collect(pols, tabs, kind, NTR, rng, [noisy_teacher(e, trng) for e in EPS])
            if not msg:
                tmax[L] = (int(O[O[:, 2] < 0.5, 3].max()), int(O[O[:, 2] > 0.5, 3].max()))
            net, loss, agree = train_net(O, Y, msg, sdn, EPO); drng = np.random.default_rng([3000 + s, sdn])
            for r in range(DROUNDS):                          # Deviation 1: DAgger rounds; Deviation 3: labels = own Bayes table
                Od, Yd = collect(pols, tabs, kind, ND, drng, [student_driver(net, msg)]); O, Y = np.concatenate([O, Od]), np.concatenate([Y, Yd])
                net, loss, agree = train_net(O, Y, msg, sdn + 1 + r, EPD, net=net)
            nets[nm] = (net, msg); info[nm] = dict(loss=loss, agree=agree, n_samples=int(len(Y)))
        print(f'seed {s}: trained {L}  [{time.perf_counter() - t0:.0f}s]', flush=True)
    cells, REG = {}, {}
    for nm, (net, msg) in nets.items():
        own = nm[2:]; evl = lights if own == 'ACT' else sorted(set(MAIN + ([own] if own in lights else [])))
        for L in evl:
            r = rollout(net_policy(net, msg), panels[L]); REG[f'{nm}|{L}|plain'] = r['regret']
            cells[f'{nm}|{L}|plain'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()),
                                            stops=float(r['stops'].mean()), timeouts=float(r['timeouts'].mean()))
    for L in lights:                                          # exact references: own tables everywhere, ACT tables on every light
        for kind in ('Z', 'M'):
            for src in sorted({L, 'ACT'}):
                r = rollout(table_policy(tabs[src][kind], kind, src), panels[L]); REG[f'{kind}*_{src}|{L}|plain'] = r['regret']
                cells[f'{kind}*_{src}|{L}|plain'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()))
    zact, tm = nets['Z_ACT'][0], tmax['ACT']
    tr_gt = rollout(net_policy(zact, False), calib['ACT'], record=True)['gt']
    for L in lights:
        gt = rollout(net_policy(zact, False), panels[L], record=True)['gt']
        cells[f'Z_ACT|{L}|oos_mass'] = float(np.mean(gt[:, 1] > np.where(gt[:, 0] == 1, tm[1], tm[0])))
        cells[f'Z_ACT|{L}|w1_tau'] = w1(gt[:, 1], tr_gt[:, 1])
    for L in ('ACT', 'EXT', 'CUT'):
        dep_gt = rollout(net_policy(zact, False), calib[L], record=True)['gt']
        variants = dict(clip=net_policy(zact, False, tau_map=lambda g, ta, tm=tm: np.minimum(ta, np.where(g, tm[1], tm[0]))),
                        fallback=net_policy(zact, False, fallback=rule_policy, tmax=tm),
                        relabel=net_policy(zact, False, tau_map=quantile_map(dep_gt, tr_gt)))
        for vn, pf in variants.items():
            r = rollout(pf, panels[L]); REG[f'Z_ACT|{L}|{vn}'] = r['regret']
            cells[f'Z_ACT|{L}|{vn}'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()), stops=float(r['stops'].mean()))
    if (out / 'panels' / 'PROBE_eval.npz').exists():             # Addendum C0c: fragility on the standard probe light
        PP = load_panel(out, 'PROBE', 'eval')
        for nm in ('Z_ACT', 'M_ACT'):
            net, msg = nets[nm]; r = rollout(net_policy(net, msg), PP); REG[f'{nm}|PROBE|plain'] = r['regret']
            cells[f'{nm}|PROBE|plain'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()))
    for L in lights:
        r = rollout(rule_policy, panels[L]); REG[f'rule|{L}|plain'] = r['regret']
        cells[f'rule|{L}|plain'] = dict(regret=float(r['regret'].mean()), viol=float(r['viol'].mean()))
    (sd_dir / 'cells.json').write_text(json.dumps(dict(source_sha256=src, seed=s, sizes=list(sizes), smoke=a.smoke, lights=lights, train=info,
                                                       tmax=tmax, cells=cells, elapsed_s=time.perf_counter() - t0), indent=1))
    np.savez_compressed(sd_dir / 'regrets.npz', **REG); torch.save({nm: n.state_dict() for nm, (n, _) in nets.items()}, sd_dir / 'nets.pt')
    c = cells
    print(f'seed {s}: Z_ACT EXT {c["Z_ACT|EXT|plain"]["regret"]:.2f} (spec {c["Z_EXT|EXT|plain"]["regret"]:.2f}, FB {c["Z_ACT|EXT|fallback"]["regret"]:.2f}) '
          f'CUT {c["Z_ACT|CUT|plain"]["regret"]:.2f} (spec {c["Z_CUT|CUT|plain"]["regret"]:.2f}); ACT Z {c["Z_ACT|ACT|plain"]["regret"]:.2f} '
          f'Z* {c["Z*_ACT|ACT|plain"]["regret"]:.2f} M {c["M_ACT|ACT|plain"]["regret"]:.2f} M* {c["M*_ACT|ACT|plain"]["regret"]:.2f} '
          f'rule {c["rule|ACT|plain"]["regret"]:.2f}  [{time.perf_counter() - t0:.0f}s]', flush=True)


def light_log_stats(L, ref='ACT', nph=20000):
    """Light-only logs: per light-second (colour, time in phase, the phase ends at the next second)."""
    def log(P):
        rng = np.random.default_rng(LOG_SEED[P]); d, p = law(P); rows = []; col = 0
        for _ in range(nph):
            du = int(rng.choice(d, p=p)); tt = np.arange(du)
            rows.append(np.stack([np.full(du, col), tt, (tt == du - 1).astype(int)], 1)); col = 1 - col
        return np.concatenate(rows)
    A, B = log(ref), log(L); tmx = {c: A[A[:, 0] == c, 1].max() for c in (0, 1)}

    def hazard(Z):
        h = {}
        for c in (0, 1):
            Zc = Z[Z[:, 0] == c]; cnt = np.bincount(Zc[:, 1], minlength=200).astype(float)
            end = np.bincount(Zc[:, 1], weights=Zc[:, 2], minlength=200)
            h[c] = np.divide(end, cnt, out=np.zeros_like(end), where=cnt > 0)
        return h
    hA, hB = hazard(A), hazard(B)
    inside = B[:, 1] <= np.where(B[:, 0] == 1, tmx[1], tmx[0]); S_exit = float(1 - inside.mean()); Bi = B[inside]
    D = float(np.mean(np.abs(np.array([hB[c][t] for c, t, _ in Bi]) - np.array([hA[c][t] for c, t, _ in Bi])))) if len(Bi) else 0.0
    return dict(S_exit=S_exit, D_haz=D, K=D + S_exit, W1=w1(B[:, 1], A[:, 1]))


def spearman(x, y):
    def rk(z):
        z = np.asarray(z, float); o = np.argsort(z, kind='stable'); r = np.empty(len(z)); r[o] = np.arange(len(z))
        for v in np.unique(z):
            r[z == v] = r[z == v].mean()
        return r
    rx, ry = rk(x), rk(y)
    return float(np.corrcoef(rx, ry)[0, 1]) if np.std(rx) > 0 and np.std(ry) > 0 else float('nan')


def boot(d, reps=2000, seed=0):
    rng = np.random.default_rng(seed); S, E = d.shape
    m = [d[np.ix_(rng.integers(0, S, S), rng.integers(0, E, E))].mean() for _ in range(reps)]
    return [float(np.percentile(m, 2.5)), float(np.percentile(m, 97.5))]


def run_merge(a, out):
    seeds = sorted(int(p.name.split('_')[1]) for p in out.glob('seed_*') if (p / 'cells.json').exists())
    C = {s: json.loads((out / f'seed_{s}' / 'cells.json').read_text()) for s in seeds}
    R = {s: dict(np.load(out / f'seed_{s}' / 'regrets.npz')) for s in seeds}
    main_seeds = [s for s in seeds if s <= 4]

    def M(key, ss=None):
        return np.array([R[s][key] for s in (ss or main_seeds)])

    def mean(key, ss=None):
        return float(M(key, ss).mean())
    pred = {}
    for P in ('EXT', 'CUT'):
        d = M(f'Z_ACT|{P}|plain') - M(f'Z_{P}|{P}|plain'); dm = M(f'M_ACT|{P}|plain') - M(f'M_{P}|{P}|plain'); ci = boot(d)
        pred[f'C0-1 Delta({P}) > 0'] = dict(mean=float(d.mean()), ci=ci, pass_=bool(ci[0] > 0))
        pred[f'C0-3 DeltaM({P}) <= Delta({P})/4'] = dict(deltaM=float(dm.mean()), delta=float(d.mean()), pass_=bool(dm.mean() <= d.mean() / 4))
        rl, pl = mean(f'Z_ACT|{P}|relabel'), mean(f'Z_ACT|{P}|plain')
        pred[f'C0-5 relabel worse on {P}'] = dict(relabel=rl, plain=pl, pass_=bool(rl > pl))
    oos = {P: float(np.mean([C[s]['cells'][f'Z_ACT|{P}|oos_mass'] for s in main_seeds])) for P in ('EXT', 'CUT')}
    dE = pred['C0-1 Delta(EXT) > 0']['mean']
    pred['C0-2 oos mass EXT >= 0.10, CUT = 0'] = dict(**oos, pass_=bool(oos['EXT'] >= 0.10 and oos['CUT'] == 0.0))
    fb, pl = mean('Z_ACT|EXT|fallback'), mean('Z_ACT|EXT|plain')
    pred['C0-2 fallback recovers >= half of Delta(EXT)'] = dict(fallback=fb, plain=pl, delta=dE, pass_=bool(fb <= pl - 0.5 * dE))
    ft = abs(mean('Z_FT|FT|plain') - mean('M_FT|FT|plain')); rb = 0.05 * mean('rule|FT|plain')
    pred['C0-3 FT: compiled silence = message'] = dict(diff=ft, bound=rb, pass_=bool(ft <= rb))
    worst = {nm: max(mean(f'{nm}|{L}|plain') for L in ('ACT', 'EXT', 'CUT')) for nm in ('Z_MIX', 'Z_ACT', 'Z_EXT', 'Z_CUT')}
    pred['C0-4 mixture minimax'] = dict(worst=worst, pass_=bool(all(worst['Z_MIX'] <= worst[k] for k in ('Z_ACT', 'Z_EXT', 'Z_CUT'))))
    xs = [s for s in seeds if s <= 2 and all(f'Z_{L}|{L}|plain' in R[s] for L in EXTRA)]; cb = {}; cc = {}
    if xs:
        tgt = ['FT', 'EXT', 'CUT'] + EXTRA; stats = {L: light_log_stats(L) for L in tgt}
        D = {L: mean(f'Z_ACT|{L}|plain', xs) - mean(f'Z_{L}|{L}|plain', xs) for L in tgt}
        DM = {L: mean(f'M_ACT|{L}|plain', xs) - mean(f'M_{L}|{L}|plain', xs) for L in tgt}
        DS = {L: mean(f'Z*_ACT|{L}|plain', xs) - mean(f'Z*_{L}|{L}|plain', xs) for L in tgt}
        sp = {k: spearman([stats[L][k] for L in tgt], [D[L] for L in tgt]) for k in ('K', 'S_exit', 'W1', 'D_haz')}
        spm = {k: spearman([stats[L][k] for L in tgt], [DM[L] for L in tgt]) for k in ('K', 'S_exit', 'W1', 'D_haz')}
        sps = {k: spearman([stats[L][k] for L in tgt], [DS[L] for L in tgt]) for k in ('K', 'S_exit', 'W1', 'D_haz')}
        inn = [L for L in tgt if stats[L]['S_exit'] == 0.0]; sp_in = spearman([stats[L]['D_haz'] for L in inn], [D[L] for L in inn])
        cb = dict(seeds=xs, stats=stats, Delta=D, DeltaM=DM, DeltaZstar=DS, spearman=sp, spearman_M=spm, spearman_Zstar=sps,
                  inside_lights=inn, spearman_inside=sp_in)
        pred['C0b-1 Spearman(K, Delta) >= 0.7'] = dict(value=sp['K'], pass_=bool(sp['K'] >= 0.7))
        pred['C0b-2 Spearman(K) > Spearman(S_exit), Spearman(W1)'] = dict(K=sp['K'], S_exit=sp['S_exit'], W1=sp['W1'],
                                                                          pass_=bool(sp['K'] > sp['S_exit'] and sp['K'] > sp['W1']))
        pred['C0b-3 inside lights: Spearman(D_haz, Delta) >= 0.6 (weak)'] = dict(value=sp_in, lights=inn, pass_=bool(sp_in >= 0.6))
        if all('Z_ACT|PROBE|plain' in R[s] for s in main_seeds):          # Addendum C0c
            phi = {s: float(R[s]['Z_ACT|PROBE|plain'].mean() - R[s]['Z_ACT|ACT|plain'].mean()) for s in main_seeds}
            phiM = {s: float(R[s]['M_ACT|PROBE|plain'].mean() - R[s]['M_ACT|ACT|plain'].mean()) for s in main_seeds}
            cl = [(s, L) for s in main_seeds for L in ('EXT', 'CUT')] + [(s, L) for s in xs for L in ['FT'] + EXTRA]
            dd = {(s, L): float(R[s][f'Z_ACT|{L}|plain'].mean() - R[s][f'Z_{L}|{L}|plain'].mean()) for s, L in cl}
            prod = [phi[s] * stats[L]['K'] for s, L in cl]; tg = [dd[c] for c in cl]
            s_prod, s_K = spearman(prod, tg), spearman([stats[L]['K'] for _, L in cl], tg)
            agree_l = []
            for L in sorted({L for _, L in cl}):
                ss = [s for s, LL in cl if LL == L]
                if len(ss) >= 3:
                    agree_l.append(spearman([phi[s] for s in ss], [dd[(s, L)] for s in ss]) > 0)
            cc = dict(phi=phi, phiM=phiM, cells={f'{s}|{L}': dd[(s, L)] for s, L in cl}, spearman_product=s_prod, spearman_K=s_K,
                      phi_range=float(max(phi.values()) - min(phi.values())), seed_order_agreement=f'{sum(agree_l)}/{len(agree_l)}')
            pred['C0c-1 Spearman(phi*K, Delta) >= 0.6'] = dict(value=s_prod, pass_=bool(s_prod >= 0.6))
            pred['C0c-2 product beats K alone'] = dict(product=s_prod, K=s_K, pass_=bool(s_prod > s_K))
            pred['C0c-3 seed order of phi matches Delta in >= half of the lights (reported)'] = dict(
                value=cc['seed_order_agreement'], pass_=bool(sum(agree_l) * 2 >= len(agree_l) > 0))
    studs = [p + L for p in ('Z_', 'M_') for L in ('FT', 'ACT', 'EXT', 'CUT', 'MIX')]
    tab = {nm: {L: mean(f'{nm}|{L}|plain') for L in MAIN} for nm in studs}
    stars = {f'{k}*_{L}': {L2: mean(f'{k}*_{L}|{L2}|plain') for L2 in (MAIN if L == 'ACT' else [L])} for k in ('Z', 'M') for L in MAIN}
    res = dict(protocol='research/city_sim/PROTOCOL_CITY_C0_20261002.md', seeds=seeds, main_seeds=main_seeds,
               source_sha256={s: C[s]['source_sha256'] for s in seeds}, regret_table=tab, bayes_tables=stars,
               rule={L: mean(f'rule|{L}|plain') for L in MAIN}, predictions=pred, addendum=cb, addendum_c0c=cc,
               agree={s: {k: v['agree'] for k, v in C[s]['train'].items()} for s in seeds})
    (out / 'result.json').write_text(json.dumps(res, indent=1))
    L1 = [f'C0 regret table (mean over seeds {main_seeds}; rows = student, columns = deployment light)', 'student | ' + ' | '.join(MAIN)]
    L1 += [f'{nm} | ' + ' | '.join(f'{tab[nm][L]:.2f}' for L in MAIN) for nm in studs]
    L1 += ['rule car | ' + ' | '.join(f'{res["rule"][L]:.2f}' for L in MAIN)]
    L1 += ['exact Bayes tables: ' + '; '.join(f'{k}: ' + ', '.join(f'{L2} {v:.2f}' for L2, v in vv.items()) for k, vv in stars.items())]
    L1 += ['Z_ACT variants: ' + '; '.join(f'{L}: plain {mean(f"Z_ACT|{L}|plain"):.2f} clip {mean(f"Z_ACT|{L}|clip"):.2f} '
                                         f'fallback {mean(f"Z_ACT|{L}|fallback"):.2f} relabel {mean(f"Z_ACT|{L}|relabel"):.2f}' for L in ('ACT', 'EXT', 'CUT'))]
    if cb:
        L1 += ['C0b light-log certificate (seeds ' + str(xs) + '): ' + '; '.join(
            f'{L}: K {cb["stats"][L]["K"]:.3f} (S_exit {cb["stats"][L]["S_exit"]:.3f}, D_haz {cb["stats"][L]["D_haz"]:.3f}, W1 {cb["stats"][L]["W1"]:.1f}) '
            f'Delta {cb["Delta"][L]:+.2f} DeltaM {cb["DeltaM"][L]:+.2f} DeltaZ* {cb["DeltaZstar"][L]:+.2f}' for L in cb['Delta'])]
        L1 += [f'C0b Spearman with Delta: {json.dumps({k: round(v, 3) for k, v in cb["spearman"].items()})}; with DeltaM: '
               f'{json.dumps({k: round(v, 3) for k, v in cb["spearman_M"].items()})}; with DeltaZ*: {json.dumps({k: round(v, 3) for k, v in cb["spearman_Zstar"].items()})}']
    if cc:
        L1 += [f'C0c phi per seed {json.dumps({k: round(v, 3) for k, v in cc["phi"].items()})}; Spearman(phi*K) {cc["spearman_product"]:.3f} vs K {cc["spearman_K"]:.3f}']
    L1 += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L1); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); torch.set_num_threads(1)
    sizes = (40, 80, 40, 2) if a.smoke else (3000, 3000, 1000, 8)
    if a.sizes:
        sizes = tuple(a.sizes)
    if a.panels:
        run_panels(a, out, sizes)
    elif a.seed is not None:
        run_seed(a, out, sizes)
    elif a.merge:
        run_merge(a, out)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--panels', nargs='+'); ap.add_argument('--seed', type=int); ap.add_argument('--merge', action='store_true')
    ap.add_argument('--extra', action='store_true')
    ap.add_argument('--sizes', type=int, nargs=4, default=None, help='development override: NTR NEV NCAL EPOCHS')
    main(ap.parse_args())
