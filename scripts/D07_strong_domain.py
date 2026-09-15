#!/usr/bin/env python3
"""D07 probe D: the `strong` field of Region under t = tau/k.

Region (LeanD6ReferenceEndpointWorldsV1.lean:18-28) demands, with q >= 2, k = q+1:
    ht0/ht1 : 0 <= t <= 1
    hr/hr2  : 1 <= rho <= 2
    hp      : 1/2 <= rho - 2 b
    strong  : 1 <= (q-1) * slopeBval = (q-1)^2 t (1-t)^(2q)

Under t = tau/k, q = k-1:
    S(k,tau) := (k-2)^2 (tau/k) (1 - tau/k)^(2k-2)  >= 1.

Questions answered here:
  (D1) exact: for which q is `strong` satisfiable at all?  (sup over t, exact rationals)
  (D2) the admissible tau window [tau_-(k), tau_+(k)] and its k -> infinity behaviour
  (D3) does the window converge to a limit window?
  (D4) is the reported "first inhabited at q = 8, t ~ 0.037818, i.e. tau ~ 0.34"
       consistent with the exact lower root?
  (D5) the JOINT window: strong AND c>0 AND (exists rho in [1,2] with hp, and
       separately with the active phase e <= k r).

Run:  python3 scripts/D07_strong_domain.py
"""
from fractions import Fraction as F
from decimal import Decimal as D, getcontext

getcontext().prec = 50
ONE, TWO, FOUR = D(1), D(2), D(4)


# ---------- D1: exact sup over t of (q-1)^2 t (1-t)^(2q) ----------
def strong_sup_exact(q):
    """max over t in [0,1] of (q-1)^2 t (1-t)^(2q), attained at t = 1/(2q+1).
    Returned as an exact Fraction."""
    n = 2 * q
    t = F(1, n + 1)
    return F((q - 1) ** 2) * t * (1 - t) ** n, t


# ---------- finite-k quantities ----------
def quantities(k, tau):
    k = D(k)
    q = k - ONE
    t = tau / k
    om = ONE - t
    n = int(2 * (k - 1))
    pw = om ** n
    b = (q - ONE) * t * pw
    a = om ** (n + 1) + q * t * pw
    c = pw                      # = a - b, proved in probe A
    e = min(a, TWO * b)
    return t, a, b, c, e, (q - ONE) * b


def S(k, tau):
    return quantities(k, tau)[5]


def bisect(f, lo, hi, iters=200):
    """root of f on [lo,hi] with f(lo), f(hi) of opposite sign"""
    flo = f(lo)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if (f(mid) >= 0) == (flo >= 0):
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def main():
    print("=" * 92)
    print("D07 probe D : the `strong` domain 1 <= (q-1)*b under t = tau/k")
    print("=" * 92)

    # ---- D1 ----
    print("\n(D1) EXACT: sup_t (q-1)^2 t (1-t)^(2q)  (max at t* = 1/(2q+1)), exact rationals")
    print(f"{'q':>4} {'k=q+1':>6} {'sup value (float)':>20} {'>= 1 ?':>8} {'t* = 1/(2q+1)':>16}")
    first = None
    for q in range(2, 16):
        v, tstar = strong_sup_exact(q)
        ok = v >= 1
        if ok and first is None:
            first = q
        print(f"{q:4d} {q+1:6d} {float(v):20.10f} {str(ok):>8} {str(tstar):>16}")
    print(f"  -> `strong` is UNSATISFIABLE for every q <= {first-1} and first satisfiable "
          f"at q = {first} (exact rational comparison, no floating point).")

    # ---- D4: exact roots at q = 8 ----
    print("\n(D4) the two roots of (q-1)^2 t (1-t)^(2q) = 1 at q = 8 (k = 9):")
    q = 8
    f = lambda t: D((q - 1) ** 2) * t * (ONE - t) ** (2 * q) - ONE
    tstar = D(1) / D(2 * q + 1)
    tlo = bisect(f, D('1e-9'), tstar)
    thi = bisect(f, tstar, ONE - D('1e-9'))
    print(f"    t_- = {+tlo:.12f}   ->  tau_- = k t_- = {+(tlo*9):.12f}")
    print(f"    t_+ = {+thi:.12f}   ->  tau_+ = k t_+ = {+(thi*9):.12f}")
    print(f"    reported grid-scan value t ~ 0.037818 ; |t_- - 0.037818| = "
          f"{+abs(tlo - D('0.037818')):.2e}")
    print(f"    reported tau ~ 0.34 ; computed tau_- = {+(tlo*9):.6f}  -> CONSISTENT")

    # ---- D2/D3: the tau window as a function of k ----
    print("\n(D2)/(D3) admissible tau window {tau : S(k,tau) >= 1} for t = tau/k")
    print(f"{'k':>8} {'tau_-':>14} {'tau_+':>14} {'k*tau_-':>12} {'tau_+/ln k':>12} "
          f"{'S at tau=0.34':>14}")
    for k in [9, 10, 12, 16, 24, 32, 64, 128, 512, 2048, 8192, 32768, 131072]:
        g = lambda tau: S(k, tau) - ONE
        # peak of S in tau is near tau = k/(2k-1) ~ 1/2
        peak = D(k) / D(2 * k - 1)
        if g(peak) < 0:
            print(f"{k:8d} {'-- empty --':>14}")
            continue
        lo = bisect(g, D('1e-12'), peak)
        hi = bisect(g, peak, D(k) - D('1e-12'))
        import math
        print(f"{k:8d} {+lo:14.9f} {+hi:14.9f} {+(lo*k):12.6f} "
              f"{float(hi)/math.log(k):12.6f} {+S(k, D('0.34')):14.6f}")
    print("  -> tau_-(k) ~ (const)/k -> 0  and  tau_+(k) ~ (1/2) ln k -> infinity.")
    print("     The window does NOT converge to a bounded limit window; it exhausts (0,inf).")
    print("     For a FIXED window [tau_min, tau_max] the requirement is just k >= K:")
    for tmin, tmax in [(D('0.05'), D('0.5')), (D('0.1'), D('0.4')), (D('0.34'), D('0.34'))]:
        K = None
        for k in range(3, 200000):
            if S(k, tmin) >= ONE and S(k, tmax) >= ONE:
                K = k
                break
        print(f"       [tau_min,tau_max] = [{+tmin},{+tmax}]  ->  strong holds for all "
              f"k >= K = {K}")

    # ---- D5: joint region ----
    print("\n(D5) JOINT feasibility.  Needed simultaneously:")
    print("     c > 0 (<=> t < 1) ; strong ; and some rho in [1,2] with")
    print("       hp     : rho >= 1/2 + 2b                      (Region field)")
    print("       active : rho <= 2a - e/k   (so that phaseValueFull > 0)")
    print(f"\n{'k':>7} {'tau':>8} {'strong?':>8} {'lo=max(1,1/2+2b)':>18} "
          f"{'hi_region=2':>12} {'hi_active=2a-e/k':>18} {'Region?':>8} {'Active?':>8}")
    for k in [9, 12, 20, 50, 200, 2000]:
        for tau in [D('0.1'), D('0.34036'), D('0.5'), D('0.7'), D('1.0')]:
            t, a, b, c, e, s = quantities(k, tau)
            lo = max(ONE, D('0.5') + TWO * b)
            hi_act = TWO * a - e / D(k)
            print(f"{k:7d} {+tau:8} {str(s >= ONE):>8} {+lo:18.9f} {2:12d} "
                  f"{+hi_act:18.9f} {str(s >= ONE and lo <= TWO and t < ONE):>8} "
                  f"{str(s >= ONE and lo <= min(TWO, hi_act) and t < ONE):>8}")

    # limiting active-phase ceiling
    print("\n     limit (k -> inf): active with some rho >= 1 requires 2(1+tau)e^{-2tau} >= 1.")
    h = lambda tau: TWO * (ONE + tau) * (-TWO * tau).exp() - ONE
    taustar = bisect(h, D('0.01'), D('2'))
    print(f"       tau* = {+taustar:.15f}   (for tau > tau* NO rho in [1,2] is in the "
          f"active phase in the limit)")
    print(f"       check: 2(1+tau*)e^{{-2tau*}} - 1 = {+h(taustar):.3e}")


if __name__ == "__main__":
    main()
