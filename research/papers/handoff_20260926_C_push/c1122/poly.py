"""Univariate polynomials in t with Fraction coefficients (list, low->high)."""
from fractions import Fraction as Fr

def trim(p):
    p = [Fr(c) for c in p]
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p

def add(p, q):
    n = max(len(p), len(q))
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])

def sub(p, q):
    return add(p, [-c for c in q])

def mul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return trim(r)

def sc(c, p):
    return trim([Fr(c) * x for x in p])

def ev(p, t):
    s = Fr(0)
    for c in reversed(p):
        s = s * t + c
    return s

def interp(ts, vs):
    """Lagrange interpolation, returns poly"""
    res = [Fr(0)]
    for i, (ti, vi) in enumerate(zip(ts, vs)):
        term = [Fr(vi)]
        den = Fr(1)
        for j, tj in enumerate(ts):
            if j != i:
                term = mul(term, [-tj, 1])
                den *= (ti - tj)
        res = add(res, sc(1 / den, term))
    return trim(res)

def bernstein_ok(p, t0, t1):
    """p >= 0 on [t0,t1] certified by nonneg Bernstein coeffs (deg <= 2). returns (ok, coeffs)
    representation p(t) = (c0 (t1-t)^2 + c1 (t-t0)(t1-t) + c2 (t-t0)^2) / (t1-t0)^2 for deg<=2"""
    p = trim(p) + [Fr(0)] * 3
    p = p[:3]
    # solve: coefficients via values: at t0: c0 (t1-t0)^2/(t1-t0)^2 = c0 = p(t0); at t1: c2 = p(t1)
    c0 = ev(p, t0)
    c2 = ev(p, t1)
    # leading coeff: c0 - c1 + c2 = p2 * (t1-t0)^2
    c1 = c0 + c2 - p[2] * (t1 - t0) ** 2
    return (c0 >= 0 and c1 >= 0 and c2 >= 0), (c0, c1, c2)

def fmt_hom(p, deg):
    """homogenise poly in t (t=a/b) to degree deg in a,b; return Lean expr string"""
    p = trim(p)
    terms = []
    for i, c in enumerate(p):
        if c == 0:
            continue
        j = deg - i
        assert j >= 0, (p, deg)
        mon = ' * '.join(['a'] * i + ['b'] * j)
        cs = f"({c.numerator}/{c.denominator})" if c.denominator != 1 else f"({c.numerator})"
        terms.append(f"{cs} * {mon}" if mon else cs)
    if not terms:
        return "0"
    return " + ".join(terms)
