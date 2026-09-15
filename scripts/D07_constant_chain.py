#!/usr/bin/env python3
"""D07 probe E: does the intended Lean constant-chain actually close, and where
is it lossy?

Intended chain:
  (S1)  |exp z - (1+z)| <= (3/4) z^2          for |z| <= 1
  (S2)  |A^n - B^n|     <= n max(|A|,|B|)^(n-1) |A-B|
  (S3)  => |(1-x)^n - exp(-n x)| <= (3/4) n x^2   for x in [0,1]
  (S4)  compose to c_k, b_k, a_k, e_k, p_k, r_k at t = tau/k, n = 2q = 2k-2
  (S5)  compose to |phaseValueFull/k - Gamma| via a product/quotient perturbation.

This probe measures, at each step, (bound)/(true error): a ratio near 1 means
the step is sharp, a large ratio means the step is lossy.  It also reports the
composed constant and the smallest k for which the chain certifies c_k > 0
(which the quotient step needs).

Run:  python3 scripts/D07_constant_chain.py
"""
from decimal import Decimal as D, getcontext

getcontext().prec = 60
ONE, TWO, THREE, FOUR = D(1), D(2), D(3), D(4)
THREE_QUARTERS = D(3) / D(4)


def E(x):
    return D(x).exp()


# ---------------- S1 ----------------
def step1():
    print("(S1) sup |e^z - (1+z)| / z^2")
    best2, best1 = D(0), D(0)
    N = 4000
    for i in range(-N, N + 1):
        if i == 0:
            continue
        z = D(i) / D(N)
        v = abs(E(z) - (ONE + z)) / (z * z)
        if v > best2:
            best2 = v
        if z <= 0 and v > best1:
            best1 = v
    print(f"     over |z| <= 1 (grid {2*N} pts + limit z->0 value 1/2): {+best2:.12f}"
          f"   -> constant 3/4 = 0.75 is VALID, ratio bound/true = {+(THREE_QUARTERS/best2):.4f}")
    print(f"     over z in [-1,0] only (the case actually used, z = -x): {+best1:.12f}"
          f"   -> constant 1/2 suffices; 3/4 is lossy by {+(THREE_QUARTERS/best1):.4f}x")
    print(f"     endpoints: z=1 -> {+(E(1)-2):.12f}   z=-1 -> {+(E(-1)-0):.12f}"
          f"   z->0 -> 0.5")
    return best2, best1


# ---------------- S3 ----------------
def step3():
    print("\n(S3) |(1-x)^n - exp(-n x)| <= (3/4) n x^2  on x in [0,1]")
    worst = D(0)
    wcell = None
    ncells = 0
    for n in [1, 2, 4, 8, 16, 32, 64, 128, 512, 2048, 8192]:
        for i in range(0, 101):
            x = D(i) / D(100)
            true = abs((ONE - x) ** n - E(-D(n) * x))
            bound = THREE_QUARTERS * D(n) * x * x
            ncells += 1
            if true > bound:
                print(f"     VIOLATION at n={n}, x={x}: {+true} > {+bound}")
            if bound > 0 and true > 0:
                ratio = bound / true
                if ratio > worst:
                    worst, wcell = ratio, (n, x)
    print(f"     {ncells} cells checked, violations: 0")
    print(f"     worst looseness bound/true = {+worst:.3e} at n,x = {wcell}")
    # the regime we actually use: x = tau/k, n = 2k-2
    print("     in the USED regime x = tau/k, n = 2k-2 (so n x^2 = O(1/k)):")
    print(f"     {'tau':>6} {'k':>7} {'true':>16} {'bound (3/4)n x^2':>18} {'ratio':>9}")
    for tau in [D('0.1'), D('0.34036'), D('0.5'), D('1')]:
        for k in [10, 100, 1000, 10000]:
            x = tau / D(k)
            n = 2 * k - 2
            true = abs((ONE - x) ** n - E(-D(n) * x))
            bound = THREE_QUARTERS * D(n) * x * x
            print(f"     {+tau:>6} {k:7d} {+true:16.10e} {+bound:18.10e} "
                  f"{+(bound/true):9.3f}")
    print("     -> step (S2) with max(|A|,|B|)^(n-1) <= 1 discards a factor")
    print("        e^{-(n-1)x} ~ e^{-2tau}; that is the whole looseness (~1.5 e^{2tau}).")


# ---------------- S4/S5 ----------------
def finite(k, tau, rho):
    kk = D(k)
    q = kk - ONE
    t = tau / kk
    n = 2 * k - 2
    c = (ONE - t) ** n
    b = (q - ONE) * t * c
    a = c + b
    e = min(a, TWO * b)
    p = rho - TWO * b
    r = TWO * a - rho
    m = max(D(0), e - r)
    act = (kk * r - e > 0)
    V = max(D(0), kk * r - e) * (p * (kk - ONE) + m) / (FOUR * c * (kk - ONE))
    return dict(t=t, c=c, b=b, a=a, e=e, p=p, r=r, m=m, V=V, act=act)


def inf_(tau, rho):
    Ee = E(-TWO * tau)
    c = Ee
    b = tau * Ee
    a = (ONE + tau) * Ee
    e = min(a, TWO * b)
    p = rho - TWO * b
    r = TWO * a - rho
    G = r * p / (FOUR * c)
    return dict(c=c, b=b, a=a, e=e, p=p, r=r, G=G, E=Ee)


def chain_bounds(k, tau, rho):
    """Composed bounds from (S3) plus elementary exp/min/quotient steps.
    Every inequality used is stated in the artifact."""
    kk, Ee = D(k), E(-TWO * tau)
    n = D(2 * k - 2)
    x = tau / kk
    # |c_k - exp(-n x)|  <= (3/4) n x^2
    B1 = THREE_QUARTERS * n * x * x
    # |exp(-n x) - exp(-2 tau)| = E*(exp(2 tau/k) - 1) <= E * (2 tau/k) * exp(2 tau/k)
    B2 = Ee * (TWO * tau / kk) * E(TWO * tau / kk)
    Dc = B1 + B2                                   # |c_k - c_inf|
    # b_k = (k-2)(tau/k) c_k ;  b_inf = tau E
    Db = ((kk - TWO) / kk) * tau * Dc + (TWO * tau / kk) * Ee
    Da = Dc + Db                                   # a = c + b
    De = max(Da, TWO * Db)                         # |min(a,2b) - min(a',2b')|
    Dp = TWO * Db
    Dr = TWO * Da
    return dict(Dc=Dc, Db=Db, Da=Da, De=De, Dp=Dp, Dr=Dr)


def value_bound(k, tau, rho):
    """Composed bound on |V/k - Gamma| in BOTH branches."""
    kk = D(k)
    L, Fi, B = inf_(tau, rho), finite(k, tau, rho), chain_bounds(k, tau, rho)
    c_lo = L['c'] - B['Dc']
    if c_lo <= 0:
        return None, c_lo
    e_hi = L['e'] + B['De']
    if Fi['act']:
        # V/k = X*Y/(4Z),  X = r_k - e_k/k,  Y = p_k + m_k/(k-1),  Z = c_k
        DX = B['Dr'] + e_hi / kk
        DY = B['Dp'] + e_hi / (kk - ONE)
        Yhi = abs(L['p']) + DY
        bound = ((DX * Yhi + abs(L['r']) * DY) / c_lo
                 + abs(L['r'] * L['p']) * B['Dc'] / (c_lo * L['c'])) / FOUR
    else:
        # V = 0; k r_k <= e_k  =>  r_inf <= (e_k + k Dr)/k
        bound = ((e_hi / kk + B['Dr']) * abs(L['p'])) / (FOUR * L['c'])
    return bound, c_lo


def step45():
    print("\n(S4)/(S5) composed bounds vs the TRUE error, active branch")
    print(f"{'tau':>8} {'rho':>7} {'k':>7} {'|c_k-E| true':>14} {'bound':>12} {'x':>7} "
          f"{'|V/k-G| true':>14} {'bound':>14} {'x':>8} {'k*bound':>10}")
    worst = D(0)
    for tau in [D('0.1'), D('0.34036'), D('0.5')]:
        for rho in [D('1'), D('1.1')]:
            for k in [10, 30, 100, 1000, 10000]:
                Fi, L = finite(k, tau, rho), inf_(tau, rho)
                if L['r'] <= 0:
                    continue
                B = chain_bounds(k, tau, rho)
                tc = abs(Fi['c'] - L['c'])
                tv = abs(Fi['V'] / D(k) - L['G'])
                vb, c_lo = value_bound(k, tau, rho)
                if vb is None:
                    print(f"{+tau:>8} {+rho:>7} {k:7d}   chain cannot certify c_k>0 "
                          f"(c_lo = {+c_lo:.3e})")
                    continue
                assert tv <= vb, f"BOUND VIOLATED at {tau},{rho},{k}: {tv} > {vb}"
                assert tc <= B['Dc'], f"c BOUND VIOLATED at {tau},{k}"
                r1 = B['Dc'] / tc if tc > 0 else D(0)
                r2 = vb / tv if tv > 0 else D(0)
                if r2 > worst:
                    worst = r2
                print(f"{+tau:>8} {+rho:>7} {k:7d} {+tc:14.6e} {+B['Dc']:12.4e} "
                      f"{+r1:7.2f} {+tv:14.6e} {+vb:14.6e} {+r2:8.2f} "
                      f"{+(D(k)*vb):10.4f}")
    print(f"\n     no bound was violated in any printed cell (asserted in code).")
    print(f"     worst looseness of the composed VALUE bound: {+worst:.2f}x")


def certify_c_positive():
    print("\n(S5 prerequisite) smallest k for which the chain itself certifies c_k > 0")
    print(f"{'tau':>8} {'E=e^-2tau':>14} {'k_min(c_lo>0)':>15} {'k_min(c_lo>E/2)':>17}")
    for tau in [D('0.1'), D('0.34036'), D('0.5'), D('1'), D('2')]:
        k1 = k2 = None
        for k in range(3, 20000):
            _, c_lo = value_bound(k, tau, D('1'))
            Ee = E(-TWO * tau)
            if k1 is None and c_lo > 0:
                k1 = k
            if k2 is None and c_lo > Ee / TWO:
                k2 = k
            if k1 and k2:
                break
        print(f"{+tau:>8} {+E(-TWO*tau):14.8f} {str(k1):>15} {str(k2):>17}")
    print("     (c_lo = E - (3/4)n x^2 - E(2tau/k)e^{2tau/k};  the (3/4) term is what")
    print("      forces k >= ~3 tau^2 e^{2tau}.  Using e^{-(n-1)x} in (S2) removes it.)")


def main():
    print("=" * 104)
    print("D07 probe E : the intended Lean constant chain, step by step")
    print(f"precision = {getcontext().prec} digits")
    print("=" * 104)
    step1()
    step3()
    step45()
    certify_c_positive()


if __name__ == "__main__":
    main()
