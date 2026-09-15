#!/usr/bin/env python3
"""D07 probe C: what actually degrades as the limit approaches the phase boundary
   r_inf = 2(1+tau)e^{-2tau} - rho  ->  0.

Two separate questions, deliberately kept apart:
  (C1) does the O(1/k) CONSTANT  C = lim_k k (V/k - Gamma)  blow up as r_inf -> 0 ?
  (C2) does the k at which the asymptotic regime is entered blow up ?

and one sanity question the conjecture as stated does NOT cover:
  (C3) what happens for r_inf < 0 (rho past the boundary), where the stated
       Gamma is NEGATIVE but phaseValueFull is >= 0 by construction?

Run:  python3 scripts/D07_boundary_uniformity.py
"""
from decimal import Decimal as D, getcontext

getcontext().prec = 60
ONE, TWO, FOUR = D(1), D(2), D(4)


def model_V(k, tau, rho):
    k = D(k)
    q = k - ONE
    t = tau / k
    om = ONE - t
    n = int(2 * (k - 1))
    pw = om ** n
    b = (q - ONE) * t * pw
    a = om ** (n + 1) + q * t * pw
    c = a - b
    p = rho - TWO * b
    r = TWO * a - rho
    e = min(a, TWO * b)
    V = max(D(0), k * r - e) * (p * (k - ONE) + max(D(0), e - r)) / (FOUR * c * (k - ONE))
    return V, (k * r - e > 0)


def lim(tau, rho):
    E = (-TWO * tau).exp()
    a, b, c = (ONE + tau) * E, tau * E, E
    p, r, e = rho - TWO * b, TWO * a - rho, min(a, TWO * b)
    return E, a, b, c, p, r, e, r * p / (FOUR * c)


def C_analytic(tau, rho):
    E, a_i, b_i, c_i, p_i, r_i, e_i, G = lim(tau, rho)
    C1 = (2 * tau - tau * tau) * E
    B1 = tau * E * (2 * tau - tau * tau - 2)
    R = 2 * (C1 + B1)              # = 2 tau^2 (1-tau) E
    P = -2 * B1
    m_i = max(D(0), e_i - r_i)
    return ((R - e_i) * p_i + r_i * P + r_i * m_i) / (FOUR * c_i) \
        - r_i * p_i * C1 / (FOUR * c_i * c_i), R, e_i


def Dk(k, tau, rho, G):
    V, act = model_V(k, tau, rho)
    return V - D(k) * G, act


def kgrid(kmax):
    """geometric grid 3 .. kmax, ~240 points, strictly increasing ints"""
    out, x = [], 3.0
    step = (kmax / 3.0) ** (1.0 / 240)
    while x <= kmax:
        v = int(round(x))
        if not out or v > out[-1]:
            out.append(v)
        x *= step
    return out


def main():
    print("=" * 96)
    print("D07 probe C : behaviour as r_inf -> 0  (phase boundary rho -> 2(1+tau)e^{-2tau})")
    print(f"precision = {getcontext().prec} digits")
    print("=" * 96)

    tau = D('0.34036')
    E, a_i, b_i, c_i, p0, r0, e_i, _ = lim(tau, D(1))
    rho_star = TWO * (ONE + tau) * E      # rho at which r_inf = 0
    print(f"\ntau = {tau};  boundary rho* = 2(1+tau)e^-2tau = {+rho_star:.15f}")
    print(f"e_inf = min(a,2b) = {+e_i:.12f}")

    margins = [D('1e-1'), D('1e-2'), D('1e-3'), D('1e-4'), D('1e-5'), D('1e-6')]
    print(f"\n(C1)/(C2)  margin m = r_inf ; rho = rho* - m ; k scanned on a geometric")
    print(f"           grid 3..k_max with k_max = max(20000, 200/m)  (~240 points,")
    print(f"           then a dense +-30% refinement round the sign change).")
    print(f"\n{'m':>9} {'Gamma':>14} {'k0 (first active k)':>20} {'k0*m':>10} "
          f"{'sup_k |D_k|':>14} {'C_emp(large k)':>16} {'C_analytic':>14}")
    for m in margins:
        rho = rho_star - m
        _, _, _, _, p_i, r_i, e2, G = lim(tau, rho)
        kmax = max(20000, int(200 / float(m)))
        ks = kgrid(kmax)
        # find first active k by scan then bisection
        k0 = None
        lo = None
        for k in ks:
            _, act = model_V(k, tau, rho)
            if act:
                k0 = k
                break
            lo = k
        if k0 is not None and lo is not None:
            a_, b_ = lo, k0
            while b_ - a_ > 1:
                mid = (a_ + b_) // 2
                _, act = model_V(mid, tau, rho)
                if act:
                    b_ = mid
                else:
                    a_ = mid
            k0 = b_
        sup = D(0)
        supk = None
        dense = set(ks)
        if k0:
            for k in range(max(3, int(k0 * 0.7)), int(k0 * 1.3) + 2):
                dense.add(k)
        for k in sorted(dense):
            d, _ = Dk(k, tau, rho, G)
            if abs(d) > sup:
                sup, supk = abs(d), k
        dbig, _ = Dk(max(ks), tau, rho, G)
        Ca, R, e_inf = C_analytic(tau, rho)
        print(f"{float(m):9.0e} {+G:14.10f} {k0 if k0 else '-':>20} "
              f"{(float(k0)*float(m) if k0 else 0):10.2f} "
              f"{+sup:14.10f} {+dbig:16.10f} {+Ca:14.10f}")
    print(f"\n   predicted large-k plateau at m=0:  (R - e_inf) p_inf /(4 c_inf) with")
    Ca0, R0, e0 = C_analytic(tau, rho_star)
    print(f"   R = 2 tau^2 (1-tau) E = {+R0:.12f},  e_inf = {+e0:.12f},  C(m=0) = {+Ca0:.12f}")
    print(f"   predicted k0 ~ (e_inf - R)/m = {+((e0 - R0)):.6f}/m")

    print("\n" + "-" * 96)
    print("(C3)  rho PAST the boundary: r_inf < 0.  The stated Gamma goes negative,")
    print("      but phaseValueFull >= 0 always (max(0,.) in its numerator).")
    print(f"\n{'m (=-r_inf)':>12} {'Gamma':>14} {'k':>8} {'V/k':>16} "
          f"{'V/k - Gamma':>16} {'D_k = k(V/k-Gamma)':>20}")
    for m in [D('1e-3'), D('1e-2'), D('1e-1')]:
        rho = rho_star + m
        _, _, _, _, _, _, _, G = lim(tau, rho)
        for k in [10, 100, 1000, 10000, 100000]:
            V, _ = model_V(k, tau, rho)
            print(f"{float(m):12.0e} {+G:14.10f} {k:8d} {+(V/D(k)):16.12f} "
                  f"{+(V/D(k)-G):16.12f} {+(V-D(k)*G):20.6f}")
    print("\n  -> D_k grows LINEARLY in k there: the conjecture is false as literally")
    print("     stated unless Gamma is replaced by max(0, Gamma) / r_inf >= 0 is assumed.")

    print("\n" + "-" * 96)
    print("(C4) sanity anchor tau = 0: D_k must be EXACTLY 0 (corner_value).")
    for rho in [D('1'), D('1.3'), D('2')]:
        for k in [3, 10, 1000]:
            V, _ = model_V(k, D(0), rho)
            G = rho * (TWO - rho) / FOUR
            print(f"    tau=0 rho={+rho} k={k:5d}  V - k*rho(2-rho)/4 = {+(V - D(k)*G)}")


if __name__ == "__main__":
    main()
