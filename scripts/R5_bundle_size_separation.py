"""R5: bundle size for evidence acquisition -- exact separation probe.

Every number here is an exact Fraction or an integer. Every claim is an assert;
there is no print-and-exit-0 path. Companion to
work/p13_conjectures/LeanSupportParityBundleSizeV1.lean, which PROVES the
radius bridge, the adaptive posterior pairing, the bundle-size-1 multi-tip
statement and the bundle-size->=d parity statement. This file supplies the
quantities Lean does not formalise: costs, priors, Bayes risks, entropies and
the greedy trajectories.

What is checked
  A. radius bridge, recomputed from the RAW multi-tip support (max-min over the
     actual support points), not from the closed form.
  B. parity: every answer pattern of every bundle of < d bit queries splits the
     fiber evenly, so the Bayes risk stays exactly 1/2; at d bits it is 0.
  C. bundle size of three geometries: multi-tip dense, interval membership,
     laminar (dyadic) membership -- all 1 -- versus parity -- exactly d.
  D. greedy rules: one-step risk-per-cost picks the direct query (cost M);
     WORLD-entropy-per-cost picks the bits (cost d, optimal); DECISION-entropy
     (entropy of the parity bit) picks the direct query (cost M). So "greedy
     fails" is false as stated: it depends on which uncertainty is scored.
  E. hard-budget cliff, independent full-state Bellman DP re-derivation.

Skipped configurations are recorded in the 'skipped' field of the JSON.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib, json

CHECKS = 0


def bump(n=1):
    global CHECKS
    CHECKS += n


# ---------------------------------------------------------------- A. bridge
def raw_selected_radius(m, W, j):
    """selectedRadius(components W, {j}) recomputed from the definition:
    (max - min)/2 of a |-> sum_{j' != j} point(a)(j') over the actual support
    points {0} u {tip w : w in W}, with tip w j' = 1 - (m-1)*[j'==w]."""
    vals = []
    pts = [None] + sorted(W)                       # None is the zero point
    for w in pts:
        if w is None:
            vals.append(F(0))
        else:
            tot = sum((F(1) - (F(m - 1) if jj == w else F(0))) for jj in range(m))
            assert tot == 1, "tip must sum to 1"
            vals.append(tot - (F(1) - (F(m - 1) if j == w else F(0))))
    return (max(vals) - min(vals)) / 2


def parity(x):
    return bin(x).count("1") % 2


def support_of(d, x):
    """W_x = {1 - b(x)} u {i+2 : x_i = 1} inside Fin (d+2)."""
    return frozenset({1 - parity(x)} | {i + 2 for i in range(d) if x >> i & 1})


def check_bridge(dmax):
    for d in range(2, dmax + 1):
        m = d + 2
        for x in range(1 << d):
            W = support_of(d, x)
            for j in (0, 1):
                r = raw_selected_radius(m, W, j)
                assert r == F(m - 1, 2) * int(j in W), (d, x, j, r)
                assert F(2, m - 1) * r == int(j != parity(x)), (d, x, j, r)
                bump(2)
            for i in range(d):
                assert (i + 2 in W) == bool(x >> i & 1)
                bump()
        # multi-tip side of the bridge: radius 0 iff the tip is absent
        for W in ({0}, {0, 1}, set(range(m)), set(range(m)) - {1}):
            for j in range(m):
                assert (raw_selected_radius(m, frozenset(W), j) == 0) == (j not in W)
                bump()


# ------------------------------------------------- B. parity fibers / bundles
def parity_fiber_counts(d, Q):
    """answer pattern -> (#worlds with parity 0, #worlds with parity 1)."""
    out = {}
    for x in range(1 << d):
        key = tuple((x >> i) & 1 for i in Q)
        c = out.setdefault(key, [0, 0])
        c[parity(x)] += 1
    return out


def parity_bayes_risk(d, Q):
    tot = F(0)
    for _, (n0, n1) in parity_fiber_counts(d, Q).items():
        tot += F(min(n0, n1), 1 << d)
    return tot


def check_parity_bundles(dmax):
    rows = []
    for d in range(2, dmax + 1):
        for k in range(0, d + 1):
            for Q in combinations(range(d), k):
                counts = parity_fiber_counts(d, Q)
                risk = parity_bayes_risk(d, Q)
                if k < d:
                    for _, (n0, n1) in counts.items():
                        assert n0 == n1, (d, Q, n0, n1)   # posterior parity uniform
                        bump()
                    assert risk == F(1, 2), (d, Q, risk)
                else:
                    assert all(min(n0, n1) == 0 for n0, n1 in counts.values())
                    assert risk == F(0), (d, Q, risk)
                bump()
        rows.append({"d": d,
                     "risk_by_bundle_size": [str(parity_bayes_risk(d, tuple(range(k))))
                                             for k in range(d + 1)],
                     "bundle_size": d})
        # bundle size is exactly d: no smaller bundle moves the risk at all
        assert all(parity_bayes_risk(d, tuple(range(k))) == F(1, 2) for k in range(d))
        assert parity_bayes_risk(d, tuple(range(d))) == F(0)
        bump(2)
    return rows


# ------------------------------------------------- C. bundle size, geometries
def generic_bayes_risk(worlds, n, Q):
    """worlds: list of frozensets of unsafe tips, uniform. Decisions: tips.
    loss(W, j) = [j in W]. Q: tuple of tips whose membership is observed."""
    groups = {}
    for W in worlds:
        groups.setdefault(tuple(int(i in W) for i in Q), []).append(W)
    tot = F(0)
    for _, g in groups.items():
        best = min(sum(1 for W in g if j in W) for j in range(n))
        tot += F(best, len(worlds))
    return tot


def min_bundle_size(worlds, n, kmax):
    """smallest k such that SOME bundle of k membership queries strictly
    reduces the Bayes risk. Returns None if no bundle up to kmax does."""
    base = generic_bayes_risk(worlds, n, ())
    for k in range(1, kmax + 1):
        for Q in combinations(range(n), k):
            if generic_bayes_risk(worlds, n, Q) < base:
                return k, base, generic_bayes_risk(worlds, n, Q)
    return None, base, base


def dense_multitip_worlds(m):
    return [frozenset(set(range(m)) - {w}) for w in range(m)]


def interval_worlds(n):
    return [frozenset(range(a, b + 1)) for a in range(n) for b in range(a, n)]


def dyadic_worlds(k):
    """laminar family: every dyadic block of [0, 2^k)."""
    n = 1 << k
    out = []
    for lvl in range(k + 1):
        w = 1 << lvl
        for a in range(0, n, w):
            out.append(frozenset(range(a, a + w)))
    return out


def check_geometry_bundle_sizes():
    rows = []
    for m in range(3, 8):
        worlds = dense_multitip_worlds(m)
        k, base, after = min_bundle_size(worlds, m, 2)
        assert k == 1, (m, k)
        assert base == F(m - 1, m) and after == F(m - 2, m), (m, base, after)
        bump(3)
        rows.append({"geometry": "multitip_dense", "n": m, "worlds": len(worlds),
                     "bundle_size": k, "risk_0": str(base), "risk_1": str(after)})
    for n in range(3, 8):
        worlds = interval_worlds(n)
        k, base, after = min_bundle_size(worlds, n, 2)
        assert k == 1, (n, k)
        assert after < base, (n, base, after)
        bump(2)
        rows.append({"geometry": "interval_membership", "n": n, "worlds": len(worlds),
                     "bundle_size": k, "risk_0": str(base), "risk_1": str(after)})
    for kk in (2, 3):
        n = 1 << kk
        worlds = dyadic_worlds(kk)
        k, base, after = min_bundle_size(worlds, n, 2)
        assert k == 1, (kk, k)
        assert after < base, (kk, base, after)
        bump(2)
        rows.append({"geometry": "laminar_dyadic", "n": n, "worlds": len(worlds),
                     "bundle_size": k, "risk_0": str(base), "risk_1": str(after)})
    return rows


# ----------------------------------------------------------- D. greedy rules
def log2_exact(k):
    assert k >= 1 and (k & (k - 1)) == 0, f"posterior support {k} is not a power of two"
    return k.bit_length() - 1


def world_entropy_bits(d, Q):
    """expected posterior entropy of the WORLD, in bits. Exact: every fiber is
    a subcube, so every posterior is uniform on a power of two."""
    tot = F(0)
    for _, g in group_worlds(d, Q).items():
        tot += F(len(g), 1 << d) * log2_exact(len(g))
    return tot


def group_worlds(d, Q):
    out = {}
    for x in range(1 << d):
        out.setdefault(tuple((x >> i) & 1 for i in Q), []).append(x)
    return out


def parity_entropy_bits(d, Q):
    """expected posterior entropy of the DECISION variable b(x), in bits."""
    tot = F(0)
    for _, g in group_worlds(d, Q).items():
        n0 = sum(1 for x in g if parity(x) == 0)
        n1 = len(g) - n0
        assert n0 == n1 or n0 == 0 or n1 == 0, "posterior parity must be uniform or certain"
        tot += F(len(g), 1 << d) * (1 if n0 == n1 else 0)
    return tot


def greedy_costs(d, M):
    """Run the three one-step greedy rules to completion. Each returns the total
    cost paid to reach zero Bayes risk. Direct query at tips 0/1 costs M and
    reveals b(x); each auxiliary bit costs 1."""
    assert M > 1, "M = 1 makes bit and direct gains-per-cost tie"
    out = {}
    for name, score in (("risk", "risk"), ("world_entropy", "we"),
                        ("decision_entropy", "de")):
        Q, cost = (), 0
        while True:
            if name == "risk":
                cur = parity_bayes_risk(d, Q)
                if cur == 0:
                    break
                gains = [(F(cur - parity_bayes_risk(d, tuple(sorted(Q + (i,)))), 1), 1, i)
                         for i in range(d) if i not in Q]
                gains.append((F(cur - 0, 1), M, "direct"))
            elif name == "world_entropy":
                cur = world_entropy_bits(d, Q)
                if parity_bayes_risk(d, Q) == 0:
                    break
                gains = [(cur - world_entropy_bits(d, tuple(sorted(Q + (i,)))), 1, i)
                         for i in range(d) if i not in Q]
                # the direct query reveals b(x): one bit of world entropy
                gains.append((F(1), M, "direct"))
            else:
                cur = parity_entropy_bits(d, Q)
                if parity_bayes_risk(d, Q) == 0:
                    break
                gains = [(cur - parity_entropy_bits(d, tuple(sorted(Q + (i,)))), 1, i)
                         for i in range(d) if i not in Q]
                gains.append((cur - 0, M, "direct"))
            best = max(gains, key=lambda t: t[0] / t[1])
            assert best[0] > 0, (name, d, M, Q, best)
            cost += best[1]
            if best[2] == "direct":
                break
            Q = tuple(sorted(Q + (best[2],)))
        out[name] = cost
    return out


def check_greedy(dmax):
    rows = []
    for d in range(2, dmax + 1):
        for M in sorted({d + 1, 2 * d, d * d + 1}):
            g = greedy_costs(d, M)
            opt = min(d, M)
            assert opt == d, (d, M)
            assert g["risk"] == M, (d, M, g)
            assert g["world_entropy"] == d, (d, M, g)
            assert g["decision_entropy"] == M, (d, M, g)
            bump(4)
            # one-step gains at the root, stated exactly
            root_bit_risk_gain = parity_bayes_risk(d, ()) - parity_bayes_risk(d, (0,))
            assert root_bit_risk_gain == 0
            root_bit_we_gain = world_entropy_bits(d, ()) - world_entropy_bits(d, (0,))
            assert root_bit_we_gain == 1
            bump(2)
            rows.append({"d": d, "direct_cost_M": M, "optimal_cost": opt,
                         "risk_greedy_cost": g["risk"],
                         "world_entropy_greedy_cost": g["world_entropy"],
                         "decision_entropy_greedy_cost": g["decision_entropy"],
                         "risk_greedy_ratio": str(F(g["risk"], opt)),
                         "world_entropy_greedy_ratio": str(F(g["world_entropy"], opt)),
                         "root_one_step_bit_risk_gain": str(root_bit_risk_gain),
                         "root_one_step_bit_world_entropy_gain_bits":
                             str(root_bit_we_gain)})
    return rows


# ------------------------------------------------------------ E. budget cliff
def cliff_dp(d, M):
    """Independent full-state Bellman DP over exact world sets."""
    @lru_cache(None)
    def risk(worlds, budget, unused):
        n = len(worlds)
        p = sum(parity(x) for x in worlds)
        best = F(min(p, n - p), n)
        if budget >= M:
            return F(0)
        if budget:
            for i in range(d):
                if unused >> i & 1:
                    val = F(0)
                    for bit in (0, 1):
                        g = tuple(x for x in worlds if x >> i & 1 == bit)
                        if g:
                            val += F(len(g), n) * risk(g, budget - 1, unused ^ (1 << i))
                    best = min(best, val)
        return best
    return [risk(tuple(range(1 << d)), B, (1 << d) - 1) for B in range(d + 1)]


def check_cliff(dmax):
    rows = []
    for d in range(2, dmax + 1):
        for M in sorted({d, 2 * d, d * d}):
            vals = cliff_dp(d, M)
            expect = [F(1, 2) if B < min(d, M) else F(0) for B in range(d + 1)]
            assert vals == expect, (d, M, vals, expect)
            bump()
            rows.append({"d": d, "direct_cost_M": M,
                         "hard_budget_risk": [str(v) for v in vals],
                         "cliff_at": min(d, M)})
    return rows


def run():
    bridge_dmax, bundle_dmax, geom_note, greedy_dmax, cliff_dmax = 8, 8, "n<=7", 6, 5
    check_bridge(bridge_dmax)
    parity_rows = check_parity_bundles(bundle_dmax)
    geom_rows = check_geometry_bundle_sizes()
    greedy_rows = check_greedy(greedy_dmax)
    cliff_rows = check_cliff(cliff_dmax)
    return {
        "scope": ("Exact finite uniform-prior probe for R5. Parity is a BENCHMARK, "
                  "not the claim; the claim is the bundle-size separation between "
                  "geometries under the same membership primitive."),
        "exact_checks": CHECKS,
        "skipped": {
            "radius_bridge": f"d in 2..{bridge_dmax} only (2^d worlds enumerated); "
                             "larger d not attempted",
            "parity_bundles": f"d in 2..{bundle_dmax}; all 2^d bundles per d",
            "geometry_bundle_sizes": f"multitip m in 3..7, intervals {geom_note}, "
                                     "dyadic laminar n in {4,8}; bundle search "
                                     "capped at k<=2 because k=1 already succeeds",
            "greedy": f"d in 2..{greedy_dmax}, M in {{d+1, 2d, d^2+1}}; M=1 excluded "
                      "because bit and direct gain-per-cost tie there",
            "cliff_dp": f"full-state DP d in 2..{cliff_dmax} only (state space is "
                        "the power set of the cube); d>5 not attempted here, but "
                        "parity_bundle_probe.json covers d<=6 full-state and d<=10 "
                        "symmetry-reduced",
            "not_probed": ["non-uniform priors", "noisy answers", "expected-cost "
                           "(non-pathwise) budgets", "query classes other than "
                           "single-tip membership"],
        },
        "A_radius_bridge": "raw max-min recomputation agrees with the indicator "
                           "(2/(m-1))*selectedRadius(W_x,{j}) = [j != b(x)]",
        "B_parity_bundles": parity_rows,
        "C_geometry_bundle_sizes": geom_rows,
        "D_greedy": greedy_rows,
        "E_budget_cliff": cliff_rows,
        "headline": ("bundle size is a property of how the danger region sits "
                     "relative to the query class: 1 for multitip, interval and "
                     "laminar danger sets under membership queries, exactly d for "
                     "the parity danger set under the same primitive."),
        "greedy_caveat": ("risk-greedy and decision-entropy-greedy both overspend "
                          "by M/d; WORLD-entropy-greedy is optimal here, so the "
                          "failure is not a failure of greedy acquisition in "
                          "general."),
    }


if __name__ == "__main__":
    out = run()
    out["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    dest = Path("/Users/phanan/cig-amf-main/research/worker_distinct_completion_20260913/"
                "R5_bundle_size_separation.json")
    dest.write_text(json.dumps(out, indent=2) + "\n")
    print("PASS", out["exact_checks"], "exact checks ->", dest)
