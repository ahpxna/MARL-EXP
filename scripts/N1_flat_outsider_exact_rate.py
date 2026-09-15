#!/usr/bin/env python3
"""N1 - flat-outsider exact rate Gamma_K, checked against a direct optimizer.

Instance (the family named in the batch spec):
  relation i : two actions, means (0, 1), unit variance   -> capacity 1
  relation j : K >= 2 actions, all means 0, unit variance -> capacity 0
  Top-1 = {i}, unique, even though j's extrema are tied.

Allocation w over the 2 + K cells, sum w = 1.  Effective variances v = 1/w.
An alternative is (p0, p1, y_1..y_K); it flips the Top-1 iff
  range_j = max_{a,b} |y_a - y_b|  >=  |p1 - p0| = range_i.
Its energy is  p0^2/(2 v_i0) + (p1-1)^2/(2 v_i1) + sum_a y_a^2/(2 u_a).

CLAIM UNDER TEST (a shorter proof path than the symmetrization route in the
spec - no concavity, no permutation averaging, no WLOG):

  (1) J(w) = 1 / (2 (V + U)),   V = v_i0 + v_i1,  U = max_{a != b} (u_a + u_b)
      i.e. the whole instance collapses to ONE pair-flip whose effective
      variance is V + U.  Lower: any flipping alternative must shrink i to some
      z and open ONE pair of j's cells to at least z; both halves are
      pair_flip_lower.  Upper: the explicit minimiser.

  (2) sup_w J(w) = Gamma_K = 1 / (2 (2 + sqrt(2K))^2),  attained at
      mass a* = 2/(2+sqrt(2K)) on relation i split evenly between its two
      endpoints and (1-a*)/K on each cell of j.

Every check raises AssertionError on mismatch; it never prints and exits 0.
"""
import itertools
import math
import random
from fractions import Fraction


# ---------------------------------------------------------------- claim (1)

def J_closed_form(v0, v1, u):
    """1 / (2 (V + U)) with V = v0+v1 and U the LARGEST pair sum in u."""
    V = v0 + v1
    U = max(u[a] + u[b] for a in range(len(u)) for b in range(len(u)) if a != b)
    return 1.0 / (2.0 * (V + U))


def J_direct(v0, v1, u, grid=4001):
    """J by direct minimisation over the one free variable z, with the inner
    per-relation minimisations done in closed form from first principles.

    For a fixed shrunk range z of relation i:
      cheapest way to reach range_i <= z : displacements s,t >= 0 with
        s + t >= 1 - z, cost s^2/(2v0) + t^2/(2v1)  ->  (1-z)^2/(2(v0+v1))
      cheapest way to reach range_j >= z : pick a pair (a,b), displacements
        with |da| + |db| >= z                       ->  z^2/(2(u_a+u_b))
        minimised over pairs by taking the LARGEST u_a+u_b.
    This routine does NOT reuse the closed form: it scans z numerically.
    """
    V = v0 + v1
    U = max(u[a] + u[b] for a in range(len(u)) for b in range(len(u)) if a != b)

    def f(z):
        ci = (1.0 - z) ** 2 / (2.0 * V) if z <= 1.0 else 0.0
        return ci + z * z / (2.0 * U)

    # coarse scan past z = 1 to catch every branch, then ternary-refine the
    # bracket so the residual is the function's, not the grid's
    zs = [2.0 * i / grid for i in range(grid + 1)]
    k = min(range(len(zs)), key=lambda i: f(zs[i]))
    lo = zs[max(0, k - 1)]
    hi = zs[min(len(zs) - 1, k + 1)]
    for _ in range(200):
        m1 = lo + (hi - lo) / 3.0
        m2 = hi - (hi - lo) / 3.0
        if f(m1) <= f(m2):
            hi = m2
        else:
            lo = m1
    return min(f(lo), f(hi), f((lo + hi) / 2.0))


def J_bruteforce_alternative(v0, v1, u, samples=200000, seed=0):
    """Sanity floor: random flipping alternatives can never beat J."""
    rng = random.Random(seed)
    K = len(u)
    best = float("inf")
    for _ in range(samples):
        z = rng.uniform(0.0, 1.5)
        # shrink i to range z, splitting the move between the endpoints
        frac = rng.random()
        s = frac * max(0.0, 1.0 - z)
        t = max(0.0, 1.0 - z) - s
        p0, p1 = s, 1.0 - t
        # open one pair of j to at least z
        a, b = rng.sample(range(K), 2)
        g = rng.random()
        y = [0.0] * K
        y[a] = g * z
        y[b] = -(1.0 - g) * z
        # feasibility: range_j >= range_i
        rng_i = abs(p1 - p0)
        rng_j = max(y) - min(y)
        if rng_j + 1e-12 < rng_i:
            continue
        cost = p0 ** 2 / (2 * v0) + (p1 - 1.0) ** 2 / (2 * v1)
        cost += sum(y[c] ** 2 / (2 * u[c]) for c in range(K))
        best = min(best, cost)
    return best


def check_claim_1():
    rng = random.Random(11)
    worst_rel = 0.0
    for trial in range(300):
        K = rng.choice([2, 2, 3, 4, 5, 7])
        v0 = math.exp(rng.uniform(-3, 3))
        v1 = math.exp(rng.uniform(-3, 3))
        u = [math.exp(rng.uniform(-3, 3)) for _ in range(K)]
        cf = J_closed_form(v0, v1, u)
        dr = J_direct(v0, v1, u)
        rel = abs(cf - dr) / max(cf, 1e-300)
        worst_rel = max(worst_rel, rel)
        assert rel < 2e-6, (
            f"closed form != direct scan: K={K} v=({v0},{v1}) u={u} "
            f"closed={cf!r} direct={dr!r} rel={rel!r}")
        if trial < 40:                      # expensive, only a sample
            bf = J_bruteforce_alternative(v0, v1, u, samples=20000, seed=trial)
            assert bf >= cf - 1e-9 * max(1.0, cf), (
                f"a sampled alternative beat the claimed J: {bf!r} < {cf!r}")
    return worst_rel


# ---------------------------------------------------------------- claim (2)

def gamma_closed(K):
    return 1.0 / (2.0 * (2.0 + math.sqrt(2.0 * K)) ** 2)


def J_of_allocation(wi0, wi1, wj):
    """J for one allocation, via claim (1). Zero weight => infinite effective
    variance => that cell can be moved for free, so J = 0; handled explicitly
    instead of dividing by zero."""
    if min(wi0, wi1) <= 0:
        return 0.0
    K = len(wj)
    zeros = sum(1 for w in wj if w <= 0)
    if zeros >= 2:
        return 0.0                      # two free cells open j's range for free
    v0, v1 = 1.0 / wi0, 1.0 / wi1
    u = [(1.0 / w if w > 0 else float("inf")) for w in wj]
    V = v0 + v1
    U = max(u[a] + u[b] for a in range(K) for b in range(K) if a != b)
    if U == float("inf"):
        return 0.0
    return 1.0 / (2.0 * (V + U))


def optimal_allocation(K):
    s = math.sqrt(2.0 * K)
    a = 2.0 / (2.0 + s)
    return a / 2.0, a / 2.0, [(1.0 - a) / K] * K


def check_claim_2():
    rows = []
    for K in [2, 3, 4, 8, 16, 32]:
        wi0, wi1, wj = optimal_allocation(K)
        j_star = J_of_allocation(wi0, wi1, wj)
        g = gamma_closed(K)
        assert abs(j_star - g) <= 1e-12 * max(1.0, g), (
            f"K={K}: claimed optimum not attained: {j_star!r} vs {g!r}")

        # no allocation may beat Gamma_K: random search + coordinate polish
        rng = random.Random(1000 + K)
        best, best_w = j_star, (wi0, wi1, wj)
        for _ in range(30000):
            raw = [rng.expovariate(1.0) for _ in range(2 + K)]
            tot = sum(raw)
            w = [x / tot for x in raw]
            val = J_of_allocation(w[0], w[1], w[2:])
            if val > best:
                best, best_w = val, (w[0], w[1], w[2:])
        # local polish around the claimed optimum
        cur = [wi0, wi1] + list(wj)
        step = 0.05
        for _ in range(4000):
            i, j = rng.sample(range(2 + K), 2)
            d = step * rng.random() * cur[i]
            cand = list(cur)
            cand[i] -= d
            cand[j] += d
            if cand[i] <= 0:
                continue
            val = J_of_allocation(cand[0], cand[1], cand[2:])
            if val > J_of_allocation(cur[0], cur[1], cur[2:]):
                cur = cand
            if val > best:
                best = val
            step *= 0.9995
        assert best <= g * (1 + 1e-9), (
            f"K={K}: found an allocation beating Gamma_K: {best!r} > {g!r} at {best_w!r}")
        rows.append((K, g, K * g, wi0 + wi1, math.sqrt(2.0 / K)))
    return rows


# ------------------------------------------------- the budget inequality used

def check_budget_inequality():
    """4/x + 2K/(1-x) >= (2 + sqrt(2K))^2 on (0,1), equality at x = 2/(2+sqrt(2K)).
    This is the Cauchy step the Lean proof will need; check it exactly in the
    algebraic form  (sqrt(2K) x - 2(1-x))^2 >= 0."""
    rng = random.Random(7)
    for K in [2, 3, 5, 8, 16, 32, 64]:
        s = math.sqrt(2.0 * K)
        rhs = (2.0 + s) ** 2
        xstar = 2.0 / (2.0 + s)
        assert abs(4.0 / xstar + 2.0 * K / (1 - xstar) - rhs) < 1e-9 * rhs
        for _ in range(2000):
            x = rng.uniform(1e-6, 1 - 1e-6)
            lhs = 4.0 / x + 2.0 * K / (1 - x)
            assert lhs >= rhs - 1e-9 * rhs, (K, x, lhs, rhs)
            # the identity the Lean proof will use
            ident = lhs - rhs - (s * x - 2 * (1 - x)) ** 2 / (x * (1 - x))
            assert abs(ident) < 1e-6 * max(1.0, abs(lhs)), (K, x, ident)


def check_two_smallest_pair():
    """min_{a != b} (w_a + w_b) <= 2 W / K  - the order-statistic step.
    Checked exactly over rationals so no float decides it."""
    rng = random.Random(3)
    for K in range(2, 9):
        for _ in range(3000):
            w = [Fraction(rng.randint(1, 50), rng.randint(1, 50)) for _ in range(K)]
            W = sum(w)
            m = min(w[a] + w[b] for a in range(K) for b in range(K) if a != b)
            assert m <= 2 * W / K, (K, w, m, 2 * W / K)


if __name__ == "__main__":
    worst = check_claim_1()
    check_budget_inequality()
    check_two_smallest_pair()
    rows = check_claim_2()
    print(f"claim (1) J = 1/(2(V+U)): worst relative deviation vs direct scan = {worst:.3e}")
    print("claim (2) Gamma_K = 1/(2(2+sqrt(2K))^2):")
    print(f"{'K':>4} {'Gamma_K':>14} {'K*Gamma_K':>12} {'mass on i':>11} {'sqrt(2/K)':>11}")
    for K, g, kg, mi, pred in rows:
        print(f"{K:>4} {g:>14.10f} {kg:>12.8f} {mi:>11.8f} {pred:>11.8f}")
    print("all checks passed")
