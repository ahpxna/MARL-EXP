#!/usr/bin/env python3
"""D07 probe B: the t = tau/k limit of phaseValueFull / k, and its O(1/k) rate.

All arithmetic is stdlib `decimal` at 60 significant digits (correctly rounded
exp/ln), so no floating-point rounding can decide any conclusion here: the
quantities compared are O(1) and the working precision is 1e-60.

Model (transcribed from the Lean sources; see D07_exact_c_identity.py header):
    q = k - 1,  t = tau / k
    b = (q-1) t (1-t)^(2q)
    a = (1-t)^(2q+1) + q t (1-t)^(2q)
    c = a - b = (1-t)^(2q)              [proved exactly in probe A]
    p = rho - 2b,  r = 2a - rho,  e = min(a, 2b)
    V = phaseValueFull k p c e r
      = max(0, k r - e) * (p (k-1) + max(0, e - r)) / (4 c (k-1))

Conjectured limit:
    V / k  ->  Gamma(tau,rho) = (2(1+tau)E - rho)(rho - 2 tau E) / (4 E),  E = e^{-2tau}

Measured:  D_k := k * (V/k - Gamma) = V - k*Gamma.   The O(1/k) claim is
"D_k stabilises to a finite constant C(tau,rho)".

Run:  python3 scripts/D07_rate_law.py
Grid size is printed; nothing is silently truncated.
"""
from decimal import Decimal as D, getcontext

getcontext().prec = 60

ONE = D(1)
TWO = D(2)
FOUR = D(4)


def expd(x):
    return D(x).exp()


# ---------------- finite-k model ----------------

def model(k, tau, rho):
    """Return dict of the exact finite-k quantities at t = tau/k."""
    k = D(k)
    q = k - 1
    t = tau / k
    om = ONE - t
    pw2q = om ** int(2 * (k - 1))            # (1-t)^(2q), integer exponent
    b = (q - 1) * t * pw2q
    a = om ** int(2 * (k - 1) + 1) + q * t * pw2q
    c = a - b
    p = rho - TWO * b
    r = TWO * a - rho
    e = min(a, TWO * b)
    num1 = max(D(0), k * r - e)
    num2 = p * (k - 1) + max(D(0), e - r)
    V = num1 * num2 / (FOUR * c * (k - 1))
    return dict(k=k, q=q, t=t, a=a, b=b, c=c, p=p, r=r, e=e, V=V,
                active=(k * r - e > 0), ekink=(e - r > 0),
                strong=((q - 1) * b >= ONE))


def limits(tau, rho):
    E = expd(-2 * tau)
    a_inf = (ONE + tau) * E
    b_inf = tau * E
    c_inf = E
    p_inf = rho - TWO * b_inf
    r_inf = TWO * a_inf - rho
    e_inf = min(a_inf, TWO * b_inf)
    Gamma = r_inf * p_inf / (FOUR * c_inf)
    return dict(E=E, a=a_inf, b=b_inf, c=c_inf, p=p_inf, r=r_inf, e=e_inf, Gamma=Gamma)


def Dk(k, tau, rho):
    m = model(k, tau, rho)
    L = limits(tau, rho)
    return m['V'] - D(k) * L['Gamma'], m, L


# ---------------- the analytic prediction for C ----------------
# Expanding r_k = r_inf + R/k + O(1/k^2) etc. gives
#   C = [ (R - e_inf) p_inf + r_inf P + r_inf p_inf * m_inf/1 ] / (4 c_inf)
#       - r_inf p_inf C1 / (4 c_inf^2)      ... (m_inf = max(0,e_inf-r_inf))
# with, from  (1-tau/k)^(2k-2) = E (1 + (2tau - tau^2)/k + O(1/k^2)):
#   C1 = (2tau - tau^2) E            (1/k coefficient of c_k)
#   b_k = (k-2)(tau/k)(1-tau/k)^(2k-2) = tau E (1 + (2tau - tau^2 - 2)/k + ...)
#        -> B1 = tau E (2tau - tau^2 - 2)
#   a_k = c_k + b_k  ->  A1 = C1 + B1
#   R = 2*A1,  P = -2*B1
def predicted_C(tau, rho):
    L = limits(tau, rho)
    E, r_inf, p_inf, c_inf, e_inf = L['E'], L['r'], L['p'], L['c'], L['e']
    C1 = (2 * tau - tau * tau) * E
    B1 = tau * E * (2 * tau - tau * tau - 2)
    A1 = C1 + B1
    R = 2 * A1
    P = -2 * B1
    m_inf = max(D(0), e_inf - r_inf)
    # d/d(1/k) of  (r - e/k)(p + m/(k-1))/(4c)
    C = ((R - e_inf) * p_inf + r_inf * P + r_inf * m_inf) / (FOUR * c_inf) \
        - r_inf * p_inf * C1 / (FOUR * c_inf * c_inf)
    return C


KS = [10, 14, 20, 28, 40, 57, 80, 113, 160, 226, 320, 453, 640, 905,
      1280, 1810, 2560, 3620, 5120]


def main():
    print("=" * 100)
    print("D07 probe B : rate law for phaseValueFull/k under t = tau/k")
    print(f"precision = {getcontext().prec} decimal digits; k grid = {KS} ({len(KS)} values)")
    print("=" * 100)

    taus = [D('0.05'), D('0.1'), D('0.2'), D('0.34036'), D('0.4'), D('0.5')]
    worst = D(0)
    worst_cell = None
    rows = []
    for tau in taus:
        L0 = limits(tau, D(1))
        rmax = 2 * (ONE + tau) * L0['E']          # rho must be < rmax for r_inf > 0
        rhos = []
        for f in ['0', '0.25', '0.5', '0.75']:
            rho = ONE + D(f) * (min(rmax, TWO) - ONE)
            rhos.append(rho)
        for rho in rhos:
            L = limits(tau, rho)
            print(f"\n--- tau = {tau}  rho = {+rho}   "
                  f"r_inf = {+L['r']:.8f}  p_inf = {+L['p']:.8f}  "
                  f"Gamma = {+L['Gamma']:.12f}")
            print(f"    {'k':>6} {'V/k':>20} {'D_k = k(V/k - Gamma)':>24} "
                  f"{'D_k - D_prev':>16}  branch")
            prev = None
            for k in KS:
                d, m, _ = Dk(k, tau, rho)
                dd = '' if prev is None else f"{+(d - prev):16.3e}"
                br = ('ACT' if m['active'] else 'ZERO') + \
                     ('/kink' if m['ekink'] else '/    ') + \
                     ('/strong' if m['strong'] else '/weak  ')
                print(f"    {k:6d} {+(m['V']/D(k)):20.14f} {+d:24.14f} {dd}  {br}")
                prev = d
            Cpred = predicted_C(tau, rho)
            print(f"    D_5120            = {+prev:.14f}")
            print(f"    analytic C (1/k coefficient, hand-expanded) = {+Cpred:.14f}")
            print(f"    |D_5120 - C_pred| = {+abs(prev - Cpred):.3e}")
            rows.append((tau, rho, prev, Cpred))
            if abs(prev) > worst:
                worst, worst_cell = abs(prev), (tau, rho)

    print("\n" + "=" * 100)
    print("SUMMARY  (C is the empirical 1/k constant, = D_k at k = 5120)")
    print(f"{'tau':>10} {'rho':>12} {'C_emp':>18} {'C_pred':>18} {'|diff|':>12}")
    for tau, rho, c, cp in rows:
        print(f"{+tau:10} {+rho:12.6f} {+c:18.10f} {+cp:18.10f} {+abs(c-cp):12.2e}")
    print(f"\nlargest |C| on this grid: {+worst:.6f} at tau,rho = "
          f"{worst_cell[0]}, {+worst_cell[1]:.6f}")
    print("\nUniform-bound check |V/k - Gamma| <= Cbar/k over the WHOLE grid, k >= 10:")
    cbar = D(0)
    cell = None
    n = 0
    for tau in taus:
        L0 = limits(tau, D(1))
        rmax = 2 * (ONE + tau) * L0['E']
        for f in ['0', '0.25', '0.5', '0.75']:
            rho = ONE + D(f) * (min(rmax, TWO) - ONE)
            for k in KS:
                d, _, _ = Dk(k, tau, rho)
                n += 1
                if abs(d) > cbar:
                    cbar, cell = abs(d), (k, tau, rho)
    print(f"    cells = {n};  Cbar = max_k k|V/k - Gamma| = {+cbar:.6f}"
          f"  attained at k={cell[0]}, tau={cell[1]}, rho={+cell[2]:.6f}")


if __name__ == "__main__":
    main()
