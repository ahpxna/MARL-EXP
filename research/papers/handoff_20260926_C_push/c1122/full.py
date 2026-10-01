"""Exact checks in the FULL model (36-state lattice / sequences), b = 1, a = r."""
import itertools
from fractions import Fraction as Fr
n = (1, 1, 2, 2)
box = [v for v in itertools.product(*[range(t + 1) for t in n])]
T2I = {'A': 0, 'a': 1, 'B': 2, 'b': 3}

def S(r, v):
    return r * (v[0] - v[1]) + (v[2] - v[3])

def base(r, k):
    return min(abs(S(r, u)) for u in box if sum(u) == k)

def raw(r, v):
    return abs(S(r, v)) - base(r, sum(v))

def states(s):
    v = [0, 0, 0, 0]
    out = [tuple(v)]
    for ch in s:
        v[T2I[ch]] += 1
        out.append(tuple(v))
    return out

def flip(s):
    return s.swapcase()

def rev(s):
    return s[::-1]

def orbit(s):
    o = []
    for t in (s, flip(s), rev(s), flip(rev(s))):
        if t not in o:
            o.append(t)
    return o

def symmix(pts):
    """pts: list of (weight, seq) -> symmetrised mixture over orbits"""
    mix = {}
    for w, s in pts:
        o = orbit(s)
        for t in o:
            mix[t] = mix.get(t, 0) + Fr(w) / len(o)
    return mix

def check_mix(r, mix):
    tot = sum(mix.values())
    assert tot == 1, tot
    assert all(w >= 0 for w in mix.values())
    dev = Fr(0)
    for k in range(7):
        for t in range(4):
            mean = sum(w * states(s)[k][t] for s, w in mix.items()) / n[t]
            dev = max(dev, abs(mean - Fr(k, 6)) * 6)
    costs = [sum(w * raw(r, states(s)[k]) for s, w in mix.items()) for k in range(1, 6)]
    return dev, costs

def dp(r, mu5, L5):
    """mu5, L5: dicts k->value for k=1..5 (full-lattice weights); returns potential table and value"""
    psi = {}
    for v in sorted(box, key=lambda v: -sum(v)):
        k = sum(v)
        if k == 6:
            psi[v] = Fr(0); continue
        nc = Fr(0)
        if 1 <= k <= 5:
            nc = mu5.get(k, 0) * raw(r, v) + L5.get(k, 0) * (v[0] + v[1] - Fr(k, 3))
        best = None
        for t in range(4):
            if v[t] < n[t]:
                u = tuple(v[j] + (1 if j == t else 0) for j in range(4))
                best = psi[u] if best is None or psi[u] < best else best
        psi[v] = nc + best
    return psi

def red_to_full(mu, lam1, lam2):
    mu1, mu2, mu3 = mu
    mu5 = {1: Fr(mu1) / 2, 5: Fr(mu1) / 2, 2: Fr(mu2) / 2, 4: Fr(mu2) / 2, 3: Fr(mu3)}
    L5 = {1: Fr(lam1) / 2, 5: -Fr(lam1) / 2, 2: Fr(lam2) / 2, 4: -Fr(lam2) / 2}
    return mu5, L5

def lb(r, mu, lam1, lam2):
    mu5, L5 = red_to_full(mu, lam1, lam2)
    psi = dp(r, mu5, L5)
    pen = Fr(2, 6) * sum(abs(x) for x in L5.values()) * 1  # (eta/6)*sum_{k,tau}|l|, 2 taus -> coefficient of eta
    return psi[(0, 0, 0, 0)], pen, psi
