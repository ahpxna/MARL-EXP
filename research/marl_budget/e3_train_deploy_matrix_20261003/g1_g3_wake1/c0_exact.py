"""Exact (model-based, no sampling) evaluation of a frozen C0 car policy on a light law, by forward propagation of the state
distribution in the Z information-set MDP (stationary renewal light; the model the C0 v3 Bayes tables solve).  Imports the
testbed's own constants/backup from scripts/CITY_c0_testbed.py (read-only).  Gives per-state visitation, exact expected cost,
and the performance-difference decomposition sum_t E_{d_t}[Q*_L(s, pi(s)) - V*_L(s)]."""
import sys
from pathlib import Path
import numpy as np, torch
sys.path.insert(0, '/Users/phanan/cig-amf-main')
import scripts.CITY_c0_testbed as C
O = Path('/Users/phanan/cig-amf-main/research/city_sim/c0_v3_20261002')

def hazard(L, hi):
    d, p = C.law(L); surv = np.array([p[d >= t + 1].sum() for t in range(hi)]); end = np.array([p[d == t + 1].sum() for t in range(hi)])
    return np.where(surv > 0, end / np.maximum(surv, 1e-300), 1.0)

def tables(L):
    z = np.load(O / 'panels' / f'{L}_tables.npz'); V = z['Z'].astype(np.float64); h = hazard(L, V.shape[3])
    assert np.allclose(h, z['h']), L
    Q = C._backup_Z(V, h)                          # (X, V, 2, TM, NA) Bayes action values of the Z information set under law L
    return V, Q, h

def init_dist(L, TM):
    d, p = C.law(L); ED = float((d * p).sum()); age = np.array([p[d > k].sum() for k in range(TM)]) / ED
    D0 = np.zeros((C.XM, C.VMAX + 1, 2, TM)); xs = np.arange(-250, -149) + C.XM; vs = np.arange(8, 13)
    D0[np.ix_(xs, vs)] = (1.0 / (len(xs) * len(vs))) * 0.5 * age[None, None, None, :]   # both colours
    return D0

def net_actions(net, TM, tau_clip=None):
    X, Vv, G, Tt = np.meshgrid(np.arange(-C.XM, 0), np.arange(C.VMAX + 1), np.arange(2), np.arange(TM), indexing='ij')
    ta = Tt if tau_clip is None else np.minimum(Tt, tau_clip)
    f = C.feats(X.ravel().astype(float), Vv.ravel().astype(float), G.ravel() == 1, ta.ravel().astype(float), np.zeros(X.size), False)
    with torch.no_grad():
        return net(torch.as_tensor(f)).argmin(1).numpy().reshape(X.shape)

def table_actions(Vsrc, hsrc, TM):
    """Actions of a Bayes table (law of the table) at every state of a TM-wide grid, tau clipped to the table (as table_q)."""
    Qs = C._backup_Z(Vsrc, hsrc); hi = Vsrc.shape[3]; A = Qs.argmin(-1)          # (X, V, 2, hi)
    idx = np.minimum(np.arange(TM), hi - 1); return A[..., idx]

def evaluate(pi, L, V, Q, h):
    """pi: (X, V, 2, TM) action indices.  Returns dict with exact expected cost, timeout prob, per-step visitation sums."""
    X_, Vv_, _, TM = V.shape; D = init_dist(L, TM); hh = h[None, None, None, :]
    xg = np.arange(-C.XM, 0)[:, None, None, None]; vg = np.arange(C.VMAX + 1)[None, :, None, None]
    gg = np.arange(2)[None, None, :, None]; tg = np.arange(TM)[None, None, None, :]
    a = C.ACC[pi]; v2 = np.clip(vg + a, 0, C.VMAX); x2 = xg + v2; tn = np.minimum(tg + 1, TM - 1)
    pas = x2 >= 0; stepc = 1.0 + 0.05 * a.astype(float) ** 2
    Vstar = Q.min(-1); adv = np.take_along_axis(Q, pi[..., None], -1)[..., 0] - Vstar      # A*_L(s, pi(s)) >= 0
    occ = np.zeros_like(D); cost = 0.0; pdl = 0.0
    flat = lambda xi, vi, gi, ti: ((xi * (C.VMAX + 1) + vi) * 2 + gi) * TM + ti
    N = D.size
    for t in range(C.T):
        occ += D; pdl += float((D * adv).sum())
        newD = np.zeros(N)
        for sw, pr in ((0, 1 - hh), (1, hh)):
            w = D * pr; gnext = gg if sw == 0 else 1 - gg; tnext = tn if sw == 0 else np.zeros_like(tg)
            green_next = (gnext == 1)
            passed = pas & green_next; forced = pas & ~green_next
            c = stepc + C.PV * forced + C.IDLE * ((~passed) & ((v2 == 0) | forced))
            cost += float((w * c).sum())
            xi = np.where(forced, C.XM - 1, x2 + C.XM); vi = np.where(forced, 0, v2)
            keep = ~passed
            dest = flat(np.broadcast_to(xi, D.shape), np.broadcast_to(vi, D.shape), np.broadcast_to(gnext, D.shape), np.broadcast_to(tnext, D.shape))
            newD += np.bincount(dest[keep], weights=np.broadcast_to(w, D.shape)[keep], minlength=N)
        D = newD.reshape(occ.shape)
    alive = float(D.sum()); cost += C.TIMEOUT * alive
    return dict(cost=cost, alive=alive, occ=occ, pdl=pdl, adv=adv)

def load_net(seed, name='Z_ACT'):
    sd = torch.load(O / f'seed_{seed}' / 'nets.pt', weights_only=False)[name]
    net = torch.nn.Sequential(torch.nn.Linear(4, 64), torch.nn.ReLU(), torch.nn.Linear(64, 64), torch.nn.ReLU(), torch.nn.Linear(64, C.NA))
    net.load_state_dict(sd); net.eval(); return net
