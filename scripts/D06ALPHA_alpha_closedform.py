"""D06ALPHA probe 1: closed-form limit law of the D6 reference construction
under t = tau / k^alpha, alpha in {1/2, 1, 3/2, 2, 5/2}.

NO mpmath/sympy in this environment, so: `decimal` at 60 significant digits,
cross-validated against EXACT fractions.Fraction on an overlap grid.

EXACTNESS DESIGN: k is taken of the form k = m^2 wherever exactness is claimed,
so k^alpha = m^(2 alpha) is an INTEGER for every alpha in {1/2,1,3/2,2,5/2} and
t = tau/m^(2 alpha) is rational.  Those cells are computed in Fraction with zero
rounding.  Larger k uses decimal; the exact-vs-decimal deviation is printed
(PART 0) so the reader can see the numerical error budget instead of trusting it.

Objects (transcribed from Lean, self-checked in D06ALPHA_selfcheck.py):
  a = (1-t)^(2q+1) + q t (1-t)^(2q),  b = (q-1) t (1-t)^(2q),  c = a-b = (1-t)^(2q)
  p = rho-2b,  r = 2a-rho,  e = min(a,2b),  k = q+1
  phaseValueFull k p c e r = max(0,kr-e)(p(k-1)+max(0,e-r)) / (4 c (k-1))

Conditions per cell:
  strong : 1 <= (k-2) b          -- Lean Region.strong, a SUFFICIENT hypothesis
  branch : 1-a <= (k-2) b  AND  1 <= a k
           -- the EXACT condition (derived and brute-forced in
              D06ALPHA_selfcheck.py) for countLoss to coincide with the phase
              formula at every feasible (u,v).  strong => branch, never converse.
  active : e <= k r              -- the phaseValueFull > 0 branch

Run: python3 /Users/phanan/cig-amf-main/scripts/D06ALPHA_alpha_closedform.py
"""

import sys
from decimal import Decimal as D, getcontext
from fractions import Fraction as F

sys.path.insert(0, "/Users/phanan/cig-amf-main/scripts")
from D06ALPHA_gamelib import slopes, phase_value_full

getcontext().prec = 60

ALPHAS = [F(1, 2), F(1), F(3, 2), F(2), F(5, 2)]


def dec(x):
    if isinstance(x, F):
        return D(x.numerator) / D(x.denominator)
    return D(str(x))


def kpow(k, alpha):
    """k^alpha for alpha in {1/2,1,3/2,2,5/2}: built from sqrt and integer powers."""
    kd = D(k)
    s = kd.sqrt()
    return {F(1, 2): s, F(1): kd, F(3, 2): kd * s, F(2): kd * kd,
            F(5, 2): kd * kd * s}[alpha]


def exact_cell(m, alpha, tau, rho):
    """Exact Fraction cell at k = m^2, t = tau/m^(2 alpha)."""
    k = m * m
    t = F(tau) / F(m) ** int(2 * alpha)
    a, b, c = slopes(k, t)
    p, r, e = F(rho) - 2 * b, 2 * a - F(rho), min(a, 2 * b)
    v = phase_value_full(k, p, c, e, r)
    return dict(k=k, t=t, a=a, b=b, c=c, p=p, r=r, e=e, V=v,
                strong=((k - 2) * b >= 1),
                branch=((1 - a <= (k - 2) * b) and (a * k >= 1)),
                active=(e <= k * r))


def d_cell(k, alpha, tau, rho):
    """Decimal cell at arbitrary k (60 significant digits)."""
    kd, q = D(k), D(k - 1)
    t = dec(tau) / kpow(k, alpha)
    one_t = D(1) - t
    c = one_t ** (2 * (k - 1))
    a = one_t ** (2 * (k - 1) + 1) + q * t * c
    b = (q - 1) * t * c
    rh = dec(rho)
    p, r, e = rh - 2 * b, 2 * a - rh, min(a, 2 * b)
    num = max(D(0), kd * r - e) * (p * (kd - 1) + max(D(0), e - r))
    V = num / (4 * (c * (kd - 1)))
    return dict(k=k, t=t, a=a, b=b, c=c, p=p, r=r, e=e, V=V,
                strong=((kd - 2) * b >= 1),
                branch=((1 - a <= (kd - 2) * b) and (a * kd >= 1)),
                active=(e <= kd * r))


def dexp(x):
    return x.exp()


def dlog(x):
    return x.ln()


def predicted_limit(alpha, tau, rho):
    """Predicted lim_{k->inf} V/k, derived by hand; CHECKED against numbers below."""
    ta, rh = dec(tau), dec(rho)
    if alpha < 1:
        return D(0)                                  # r -> -rho < 0, so kr-e -> -inf
    if alpha == 1:
        ai = (1 + ta) * dexp(-2 * ta)
        bi = ta * dexp(-2 * ta)
        ci = dexp(-2 * ta)
        return max(D(0), 2 * ai - rh) * (rh - 2 * bi) / (4 * ci)
    return rh * (2 - rh) / 4                          # alpha>1: corner law


def nstr(x, n=8):
    if isinstance(x, D):
        return f"{x:.{n}e}" if x != 0 else "0"
    return str(x)


def main():
    print("=" * 104)
    print("PART 0.  EXACT (Fraction) vs decimal(60) on k = m^2, m = 2..14, "
          "tau=1/2, rho=6/5, all five alpha")
    tau, rho = F(1, 2), F(6, 5)
    worst = D(0)
    nb = 0
    for alpha in ALPHAS:
        for m in range(2, 15):
            ce = exact_cell(m, alpha, tau, rho)
            cd = d_cell(m * m, alpha, tau, rho)
            for key in ("a", "b", "c", "V"):
                x, y = dec(ce[key]), cd[key]
                if x != 0:
                    worst = max(worst, abs((x - y) / x))
                else:
                    worst = max(worst, abs(y))
            assert ce["strong"] == cd["strong"], (alpha, m, "strong")
            assert ce["branch"] == cd["branch"], (alpha, m, "branch")
            assert ce["active"] == cd["active"], (alpha, m, "active")
            nb += 1
    print(f"  cells compared: {nb};  max relative deviation over (a,b,c,V): {worst:.3e}")
    print("  every strong/branch/active boolean agrees between exact and decimal.")

    print()
    print("=" * 104)
    print("PART 1.  LIMIT LAW OF THE SCALARS.  tau=1/2, rho=6/5.")
    for alpha in ALPHAS:
        print(f"\n  alpha = {alpha}")
        print(f"    {'k':>8} {'a':>15} {'b':>15} {'c':>15} {'e':>15} {'r':>15} "
              f"{'(k-2)b':>12} {'strong':>7} {'branch':>7} {'active':>7}")
        for k in [10, 100, 1000, 10 ** 4, 10 ** 5]:
            d = d_cell(k, alpha, tau, rho)
            print(f"    {k:>8} {nstr(d['a'],7):>15} {nstr(d['b'],7):>15} "
                  f"{nstr(d['c'],7):>15} {nstr(d['e'],7):>15} {nstr(d['r'],7):>15} "
                  f"{nstr((D(k)-2)*d['b'],5):>12} {str(d['strong']):>7} "
                  f"{str(d['branch']):>7} {str(d['active']):>7}")

    print()
    print("=" * 104)
    print("PART 2.  NORMALISATION.  log-log slope of phaseValueFull against k.")
    print("  slope_j = log(V(k_{j+1})/V(k_j)) / log(k_{j+1}/k_j);  slope 1 <=> V ~ const * k")
    for alpha in ALPHAS:
        ks = [10 ** e for e in range(1, 7)]
        Vs = [d_cell(k, alpha, tau, rho)["V"] for k in ks]
        sl = []
        for i in range(len(ks) - 1):
            if Vs[i] > 0 and Vs[i + 1] > 0:
                sl.append(float(dlog(Vs[i + 1] / Vs[i]) / dlog(D(ks[i + 1]) / D(ks[i]))))
            else:
                sl.append(float("nan"))
        print(f"  alpha={str(alpha):>3}:  V = " + ", ".join(nstr(v, 4) for v in Vs))
        print(f"            slope = " + ", ".join(f"{s: .6f}" for s in sl))

    print()
    print("=" * 104)
    print("PART 3.  V/k  vs the predicted limit L, and the correction exponent gamma.")
    print("  resid = V/k - L;  gamma_j = -log|resid_{j+1}/resid_j| / log(k_{j+1}/k_j)")
    for tau_f in [F(1, 4), F(1, 2), F(1)]:
        for rho_f in [F(1), F(6, 5), F(8, 5)]:
            print(f"\n  tau={tau_f}  rho={rho_f}")
            for alpha in ALPHAS:
                L = predicted_limit(alpha, tau_f, rho_f)
                ks = [10 ** e for e in range(2, 7)]
                res = [d_cell(k, alpha, tau_f, rho_f)["V"] / D(k) - L for k in ks]
                gam = []
                for i in range(len(ks) - 1):
                    if res[i] != 0 and res[i + 1] != 0:
                        gam.append(float(-dlog(abs(res[i + 1]) / abs(res[i]))
                                         / dlog(D(ks[i + 1]) / D(ks[i]))))
                    else:
                        gam.append(float("nan"))
                print(f"    alpha={str(alpha):>3}  L={nstr(L,10):>18}  "
                      f"resid=" + ",".join(nstr(x, 3) for x in res))
                print(f"              gamma=" + ",".join(f"{g: .4f}" for g in gam))

    print()
    print("=" * 104)
    print("PART 4.  alpha < 1: where the closed-form value dies (V = 0 <=> k r <= e).")
    for alpha in [F(1, 2), F(9, 10) if False else F(1, 2)][:1]:
        pass
    for alpha_f, label in [(0.5, "1/2"), (0.75, "3/4"), (0.9, "9/10")]:
        for tau_f in [0.25, 0.5, 1.0]:
            first0 = None
            for k in range(3, 6000):
                td = dec(tau_f) / (D(k) ** dec(alpha_f) if alpha_f not in (0.5,)
                                   else D(k).sqrt())
                # generic alpha: use exp(alpha ln k)
                td = dec(tau_f) / dexp(dec(alpha_f) * dlog(D(k)))
                one_t = D(1) - td
                c = one_t ** (2 * (k - 1))
                a = one_t ** (2 * k - 1) + D(k - 1) * td * c
                b = D(k - 2) * td * c
                rh = D("1.2")
                r, e = 2 * a - rh, min(a, 2 * b)
                if D(k) * r - e <= 0:
                    first0 = k
                    break
            print(f"  alpha={label} tau={tau_f} rho=1.2: first k with V == 0 : {first0}")

    print()
    print("=" * 104)
    print("PART 5.  WHERE THE HYPOTHESES HOLD.  S=strong(Lean), B=exact branch, "
          "A=active.  tau=1/2 rho=6/5")
    print("   exact Fractions, k = m^2:")
    print("     m    k   " + "".join(f"| alpha={str(al):>3}: S B A " for al in ALPHAS))
    for m in range(2, 15):
        row = f"    {m:>2} {m*m:>4}   "
        for alpha in ALPHAS:
            d = exact_cell(m, alpha, tau, rho)
            row += (f"|            {'T' if d['strong'] else 'F'} "
                    f"{'T' if d['branch'] else 'F'} {'T' if d['active'] else 'F'} ")
        print(row)
    print("   decimal(60), larger k:")
    print("          k   " + "".join(f"| alpha={str(al):>3}: S B A " for al in ALPHAS))
    for k in [100, 1000, 10 ** 4, 10 ** 5, 10 ** 6]:
        row = f"    {k:>9}   "
        for alpha in ALPHAS:
            d = d_cell(k, alpha, tau, rho)
            row += (f"|            {'T' if d['strong'] else 'F'} "
                    f"{'T' if d['branch'] else 'F'} {'T' if d['active'] else 'F'} ")
        print(row)
    print()
    print("  margins at k=10^6 (distance from each boundary; sign = holds):")
    for alpha in ALPHAS:
        d = d_cell(10 ** 6, alpha, tau, rho)
        print(f"    alpha={str(alpha):>3}:  (k-2)b-1 = {nstr((D(10**6)-2)*d['b']-1,5):>14}"
              f"   (k-2)b-(1-a) = {nstr((D(10**6)-2)*d['b']-(1-d['a']),5):>14}"
              f"   a*k-1 = {nstr(d['a']*D(10**6)-1,5):>14}"
              f"   k*r-e = {nstr(D(10**6)*d['r']-d['e'],5):>14}")


if __name__ == "__main__":
    main()
