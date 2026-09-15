#!/usr/bin/env python3
"""MASTER: (1) audit the 'price of evidence B' field, (2) build a FIXED-WORLD
acquisition model in which the query is executable and the cost is a sample count.

PART 1  DIAGNOSIS.  research/master_reference_20260912/..._v1.json reports
        price_of_evidence_B[k,rho].cheapest_t_that_kills_floor = the smallest
        GRID t that is (a) inside the sufficient regime (k-2)b>=1 and (b) has
        V_k(t,rho)=0.  We recompute the true dead-set over a much finer t grid,
        WITHOUT the regime filter, and report how often the published number is
        set by the grid's left endpoint or by the regime boundary rather than by
        the floor actually dying.  We also check the t=0 limit in closed form.

PART 2  FIXED WORLD.  The world F_{A,t0} is built once at t0 and NEVER
        recompensated.  A query picks a reference t1, draws X ~ Bernoulli(t1)^{2k},
        and reads Y = F_{A,t0}(X) + N(0,sigma^2).  The readout is the per-coordinate
        linear response

            Delta_i(t1) := E_{t1}[Y | X_i=1] - E_{t1}[Y | X_i=0] - rho*1_T(i).

        CLAIM (verified exactly on full cubes, and derived in the findings file):
            Delta_i(t1) = a(t1) - a(t0)   for i in A and for i = z
            Delta_i(t1) = b(t1) - b(t0)   for i in B
            contrast Gamma(t0,t1) := Delta_A - Delta_B = c(t1) - c(t0),
            c(t) = (1-t)^(2k-2).
        Hence Gamma(t0,t0) = 0 EXACTLY: at the incumbent reference the linear
        response carries zero information about A.  That is the floor.
        Cost to break it: n(t1) = 4 z^2 W_i(t1) / Gamma(t0,t1)^2 samples, with
        W_i(t1) = Var(Y|X_i=1)/t1 + Var(Y|X_i=0)/(1-t1) the per-sample variance
        of the plug-in slope.  W blows up at t1 -> 0 and t1 -> 1, Gamma vanishes
        at t1 = t0, so n has an interior minimum n* = the acquisition price.

PART 3  ADVERSE CHECK.  The floor is a property of the LINEAR-RESPONSE CHANNEL,
        not of the information in the sample.  We compute the per-sample Gaussian
        KL between the fixed worlds F_{A,t0} and F_{A',t0} (A' = A with one
        coordinate swapped) AT t1 = t0 and show it is strictly positive, so a
        full-likelihood analyst does NOT face the floor.  A check that can never
        return False is not a check; this one returns False for the full channel.

Exact rational arithmetic (fractions.Fraction) everywhere except the final
sample-size numbers, where the float residual is reported.
"""
from __future__ import annotations
import argparse, itertools, json, math, os, sys
from fractions import Fraction as F

PROTOCOL_VERSION = "master_fixed_world_acquisition_v1"
Z975 = 1.959963984540054  # two-sided 5%


# ---------------------------------------------------------------- D6 algebra
def slopes(k, t):
    """(a, b, c) of the D6 reference-phase derivation, |A|=k, |B|=k-1."""
    c = (1 - t) ** (2 * k - 2)
    return c * (1 + (k - 2) * t), c * (k - 2) * t, c


def pieces(k, t, rho):
    a, b, c = slopes(k, t)
    return a, b, a - b, rho - 2 * b, 2 * a - rho, min(a, 2 * b)


def pos(x):
    return x if x > 0 else F(0)


def V_formula(k, t, rho):
    a, b, cg, p, r, e = pieces(k, t, rho)
    return pos(k * r - e) * (p * (k - 1) + pos(e - r)) / (4 * cg * (k - 1))


def in_regime(k, t, rho):
    return (k - 2) * pieces(k, t, rho)[1] >= 1


# ------------------------------------------------- PART 1: audit the "price"
def audit_price(artifact_path, fine_den=4096):
    """Recompute the dead-set on a fine grid with NO regime filter."""
    with open(artifact_path) as f:
        art = json.load(f)
    ks = art["grid"]["ks"]
    rhos = [F(x) for x in art["grid"]["rhos"]]
    coarse = [F(x) for x in art["grid"]["ts"]]
    tmin_coarse = min(coarse)

    # fine grid strictly inside (0, 1/4], dyadic so every coarse point is included
    fine = sorted({F(i, fine_den) for i in range(1, fine_den // 4 + 1)} | set(coarse))

    rows = []
    for row in art["price_of_evidence_B"]:
        k, rho = row["k"], F(row["rho"])
        published = row["cheapest_t_that_kills_floor"]
        # closed-form t -> 0 limit: a->1, b->0, c->1, e->0, r->2-rho
        dead_at_zero = bool(k * (2 - rho) <= 0)
        dead_fine = [t for t in fine if V_formula(k, t, rho) == 0]
        alive_fine = [t for t in fine if V_formula(k, t, rho) != 0]
        true_cheapest_dead = min(dead_fine) if dead_fine else None
        # is the published number pinned by the grid's left endpoint?
        pinned_by_grid = published is not None and F(published) == tmin_coarse
        # is it pinned by the regime boundary? (smallest in-regime coarse t)
        in_reg_coarse = [t for t in coarse if in_regime(k, t, rho)]
        pinned_by_regime = (published is not None and in_reg_coarse
                            and F(published) == min(in_reg_coarse))
        rows.append({
            "k": k, "rho": str(rho),
            "published_cheapest_t_that_kills_floor": published,
            "dead_at_t_eq_0_closed_form": dead_at_zero,
            "true_cheapest_dead_t_on_fine_grid": (str(true_cheapest_dead)
                                                  if true_cheapest_dead is not None else None),
            "true_cheapest_dead_t_float": (float(true_cheapest_dead)
                                           if true_cheapest_dead is not None else None),
            "published_float": float(F(published)) if published else None,
            "overstatement_factor": (float(F(published) / true_cheapest_dead)
                                     if published and true_cheapest_dead and true_cheapest_dead > 0
                                     else None),
            "published_equals_grid_left_endpoint": pinned_by_grid,
            "published_equals_smallest_in_regime_t": bool(pinned_by_regime),
            "n_alive_fine": len(alive_fine), "n_dead_fine": len(dead_fine),
            "n_in_regime_coarse": len(in_reg_coarse), "n_coarse": len(coarse),
        })
    n = len(rows)
    pub = [r for r in rows if r["published_cheapest_t_that_kills_floor"] is not None]
    summary = {
        "rows": n,
        "rows_with_a_published_price": len(pub),
        "published_price_is_grid_left_endpoint": sum(r["published_equals_grid_left_endpoint"] for r in pub),
        "published_price_is_smallest_in_regime_t": sum(r["published_equals_smallest_in_regime_t"] for r in pub),
        "rows_where_floor_is_already_dead_at_t=0": sum(r["dead_at_t_eq_0_closed_form"] for r in rows),
        "rows_where_published_price_strictly_exceeds_true_cheapest_dead_t":
            sum(1 for r in pub if r["true_cheapest_dead_t_on_fine_grid"] is not None
                and F(r["published_cheapest_t_that_kills_floor"]) > F(r["true_cheapest_dead_t_on_fine_grid"])),
        "max_overstatement_factor": max([r["overstatement_factor"] for r in pub
                                         if r["overstatement_factor"] is not None] or [None]),
        "fine_grid_denominator": fine_den,
        "fine_grid_points": len(fine),
    }
    return {"summary": summary, "rows": rows}


# ------------------------------------------ PART 2: the actual fixed world
def build_world(k, t0, rho, h, alpha=None, beta=None):
    """Return (n_coords, z, T, A, B, F) with F: tuple->Fraction, built ONCE at t0.

    Default alpha=k, beta=k-1 is the construction.  alpha/beta override lets us
    decouple the block sizes, which is where the B-slope spelling is testable.
    """
    al = k if alpha is None else alpha
    be = (k - 1) if beta is None else beta
    n = al + be + 1
    z = n - 1
    nonz = list(range(n - 1))
    T = frozenset(range(k))            # visible k-set, excludes z when k <= n-1
    # A = h elements of T, then fill from the tail of nonz
    Ta = [i for i in nonz if i in T]
    Na = [i for i in nonz if i not in T]
    assert h <= len(Ta) and (al - h) <= len(Na), "infeasible (h, alpha)"
    A = frozenset(Ta[:h] + Na[:al - h])
    B = frozenset(nonz) - A
    assert len(A) == al and len(B) == be

    def gate(x):
        if x[z] == 1:
            return 0
        if any(x[i] for i in A):
            return 1
        return 1 if sum(x[j] for j in B) >= 2 else 0

    cube = list(itertools.product((0, 1), repeat=n))

    def bern_w(x, t):
        w = F(1)
        for xi in x:
            w *= t if xi == 1 else (1 - t)
        return w

    Eg0 = sum(bern_w(x, t0) * gate(x) for x in cube)
    # response slopes of g_A at t0, by exact conditional expectation
    s = {}
    for i in range(n):
        num1 = sum(bern_w(tuple(v for j, v in enumerate(x) if j != i), t0) * gate(x)
                   for x in cube if x[i] == 1)
        num0 = sum(bern_w(tuple(v for j, v in enumerate(x) if j != i), t0) * gate(x)
                   for x in cube if x[i] == 0)
        s[i] = num1 - num0

    coef = {i: (rho * (1 if i in T else 0) - s[i]) for i in range(n)}

    def Fworld(x):
        return gate(x) - Eg0 + sum(coef[i] * (x[i] - t0) for i in range(n))

    return dict(n=n, z=z, T=T, A=A, B=B, cube=cube, gate=gate, s_at_t0=s,
                coef=coef, Eg0=Eg0, Fworld=Fworld, bern_w=bern_w, k=k,
                t0=t0, rho=rho, alpha=al, beta=be)


def cond_moments(W, t1, i):
    """Exact E[F|X_i=u] and Var(F|X_i=u) under Bernoulli(t1)^n, u in {0,1}."""
    out = {}
    for u in (0, 1):
        m = F(0); m2 = F(0)
        for x in W["cube"]:
            if x[i] != u:
                continue
            w = W["bern_w"](tuple(v for j, v in enumerate(x) if j != i), t1)
            y = W["Fworld"](x)
            m += w * y
            m2 += w * y * y
        out[u] = (m, m2 - m * m)
    return out


def fixed_world_response(W, t1):
    """Delta_i(t1) for every coordinate, exactly."""
    d = {}
    for i in range(W["n"]):
        cm = cond_moments(W, t1, i)
        d[i] = cm[1][0] - cm[0][0] - W["rho"] * (1 if i in W["T"] else 0)
    return d


def verify_response_law(k, t0, rho, h, t1s, alpha=None, beta=None):
    W = build_world(k, t0, rho, h, alpha, beta)
    al, be = W["alpha"], W["beta"]
    checks = []
    for t1 in t1s:
        # closed forms for the GENERAL block sizes
        a1 = (1 - t1) ** (al + be - 1) * (1 + (be - 1) * t1)
        b1 = (be - 1) * t1 * (1 - t1) ** (al + be - 1)
        a0 = (1 - t0) ** (al + be - 1) * (1 + (be - 1) * t0)
        b0 = (be - 1) * t0 * (1 - t0) ** (al + be - 1)
        c1 = (1 - t1) ** (al + be - 1)
        c0 = (1 - t0) ** (al + be - 1)
        d = fixed_world_response(W, t1)
        okA = all(d[i] == a1 - a0 for i in W["A"])
        okB = all(d[j] == b1 - b0 for j in W["B"])
        okz = (d[W["z"]] == a1 - a0)
        gam = d[next(iter(W["A"]))] - d[next(iter(W["B"]))]
        checks.append({"t1": str(t1), "A_slope_ok": okA, "B_slope_ok": okB,
                       "z_slope_ok": okz,
                       "Gamma_exact": str(gam),
                       "Gamma_eq_c(t1)-c(t0)": bool(gam == c1 - c0),
                       "Gamma_float": float(gam)})
    return {"k": k, "alpha": al, "beta": be, "t0": str(t0), "rho": str(rho), "h": h,
            "n_coords": W["n"], "checks": checks,
            "all_pass": all(c["A_slope_ok"] and c["B_slope_ok"] and c["z_slope_ok"]
                            and c["Gamma_eq_c(t1)-c(t0)"] for c in checks)}


def cost_curve(k, t0, rho, h, sigma, t1_grid):
    """n(t1) = 4 z^2 W_i(t1) / Gamma^2 for classifying one coordinate i in A vs B."""
    W = build_world(k, t0, rho, h)
    i = next(iter(W["A"]))
    c0 = (1 - t0) ** (2 * k - 2)
    rows = []
    for t1 in t1_grid:
        c1 = (1 - t1) ** (2 * k - 2)
        gam = c1 - c0
        cm = cond_moments(W, t1, i)
        var1, var0 = cm[1][1] + sigma ** 2, cm[0][1] + sigma ** 2
        Wvar = var1 / t1 + var0 / (1 - t1)     # per-sample variance of the slope estimate
        if gam == 0:
            rows.append({"t1": str(t1), "t1_f": float(t1), "Gamma": 0.0,
                         "per_sample_var": float(Wvar), "n_samples": None,
                         "note": "FLOOR: contrast identically zero at t1 = t0"})
            continue
        n = 4 * Z975 ** 2 * float(Wvar) / float(gam) ** 2
        rows.append({"t1": str(t1), "t1_f": float(t1), "Gamma": float(gam),
                     "per_sample_var": float(Wvar), "n_samples": n,
                     "efficiency_Gamma2_over_W": float(gam) ** 2 / float(Wvar)})
    live = [r for r in rows if r["n_samples"] is not None]
    best = min(live, key=lambda r: r["n_samples"]) if live else None
    return {"k": k, "t0": str(t0), "rho": str(rho), "h": h, "sigma": str(sigma),
            "coordinate_tested": i, "c_t0": float(c0),
            "curve": rows,
            "argmin_t1": best["t1"] if best else None,
            "argmin_t1_f": best["t1_f"] if best else None,
            "min_samples_X": best["n_samples"] if best else None,
            "Gamma_at_argmin": best["Gamma"] if best else None,
            "argmin_is_interior": bool(best and min(t1_grid) < F(best["t1"]) < max(t1_grid))}


# ---------------------------------- PART 3: the channel restriction is load-bearing
def full_channel_check(k, t0, rho, h, sigma):
    """At t1 = t0 the LINEAR RESPONSE is blind.  Is the SAMPLE blind?  No."""
    W = build_world(k, t0, rho, h)
    # A' = A with one element swapped for one element of B, same h if possible
    a_el = sorted(i for i in W["A"] if i not in W["T"])
    b_el = sorted(j for j in W["B"] if j not in W["T"])
    if not a_el or not b_el:
        a_el = sorted(W["A"]); b_el = sorted(W["B"])
    swap_out, swap_in = a_el[0], b_el[0]
    A2 = (W["A"] - {swap_out}) | {swap_in}

    def gate2(x):
        if x[W["z"]] == 1:
            return 0
        if any(x[i] for i in A2):
            return 1
        B2 = set(range(W["n"] - 1)) - A2
        return 1 if sum(x[j] for j in B2) >= 2 else 0

    Eg02 = sum(W["bern_w"](x, t0) * gate2(x) for x in W["cube"])
    s2 = {}
    for i in range(W["n"]):
        n1 = sum(W["bern_w"](tuple(v for j, v in enumerate(x) if j != i), t0) * gate2(x)
                 for x in W["cube"] if x[i] == 1)
        n0 = sum(W["bern_w"](tuple(v for j, v in enumerate(x) if j != i), t0) * gate2(x)
                 for x in W["cube"] if x[i] == 0)
        s2[i] = n1 - n0
    coef2 = {i: (rho * (1 if i in W["T"] else 0) - s2[i]) for i in range(W["n"])}

    def F2(x):
        return gate2(x) - Eg02 + sum(coef2[i] * (x[i] - t0) for i in range(W["n"]))

    # per-sample Gaussian KL at t1 = t0
    d2 = sum(W["bern_w"](x, t0) * (W["Fworld"](x) - F2(x)) ** 2 for x in W["cube"])
    kl = d2 / (2 * sigma ** 2)
    # slope contrast between the two worlds at t1 = t0, for the same coordinates
    d_1 = fixed_world_response(W, t0)
    slope_blind = all(v == 0 for v in d_1.values())
    n_full = (math.log(1 / 0.05) / float(kl)) if kl > 0 else None
    return {"k": k, "t0": str(t0), "rho": str(rho), "h": h, "sigma": str(sigma),
            "swap": [swap_out, swap_in],
            "linear_response_at_t1_eq_t0_is_identically_zero": bool(slope_blind),
            "E[(F_A - F_A')^2]_at_t0": float(d2),
            "per_sample_gaussian_KL_at_t0": float(kl),
            "full_channel_samples_for_5pct_error_approx": n_full,
            "VERDICT": ("floor is a property of the LINEAR-RESPONSE CHANNEL only; "
                        "the full sample separates the two worlds at t1 = t0"
                        if kl > 0 else
                        "the two worlds are indistinguishable even from the full sample")}


# ------------------------------------------------------------------- driver
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--artifact",
                    default="research/master_reference_20260912/master_reference_phase_certificates_v1.json")
    ap.add_argument("--fine-den", type=int, default=4096)
    a = ap.parse_args()
    if os.path.exists(a.out) and not a.overwrite:
        sys.exit(f"refusing to overwrite {a.out}; pass --overwrite")

    out = {"protocol_version": PROTOCOL_VERSION,
           "arithmetic": "exact Fraction for every response/contrast/variance; "
                         "float only for the final sample counts (residual reported)",
           "scope_note": "cube verification is limited to small block sizes because the "
                         "cube is 2^(alpha+beta+1); k in {3,4} and decoupled blocks up to "
                         "9 coordinates.  This is a deliberate, stated truncation."}

    # ---- Part 1
    out["part1_price_audit"] = audit_price(a.artifact, a.fine_den)

    # ---- Part 2a: response law on full cubes, construction block sizes
    t1s = [F(0), F(1, 8), F(1, 4), F(1, 3), F(1, 2), F(3, 4)]
    law = []
    for k in (3, 4):
        for t0 in (F(1, 8), F(1, 4)):
            for rho in (F(1), F(3, 2)):
                for h in (1, k):
                    law.append(verify_response_law(k, t0, rho, h, t1s))
    out["part2a_response_law_construction_blocks"] = {
        "cases": len(law), "all_pass": all(c["all_pass"] for c in law), "detail": law}

    # ---- Part 2b: decoupled block sizes (this is where a wrong B-slope shows up)
    law2 = []
    for (al, be) in ((3, 2), (4, 2), (3, 4), (2, 5), (5, 3)):
        law2.append(verify_response_law(3, F(1, 8), F(1), 1, t1s, alpha=al, beta=be))
    out["part2b_response_law_decoupled_blocks"] = {
        "cases": len(law2), "all_pass": all(c["all_pass"] for c in law2),
        "closed_form_B_slope_tested": "(|B|-1) t (1-t)^(|A|+|B|-1)",
        "detail": law2}

    # ---- Part 2c: the floor and the cost curve
    t1_grid = [F(i, 64) for i in range(1, 64)]
    costs = []
    for k in (3, 4):
        for t0 in (F(1, 32), F(1, 8), F(1, 4)):
            for sigma in (F(1, 10), F(1)):
                costs.append(cost_curve(k, t0, F(1), 1, sigma, t1_grid))
    out["part2c_cost"] = {
        "cost_model": "one query = one i.i.d. draw X ~ Bernoulli(t1)^(2k) with "
                      "Y = F_{A,t0}(X) + N(0,sigma^2); cost = number of draws",
        "estimator": "plug-in slope difference-in-means, two-sided 5% test of "
                     "'coordinate i is in A' vs 'in B'",
        "sample_size": "n(t1) = 4 * 1.959963984540054^2 * W_i(t1) / Gamma(t0,t1)^2",
        "t1_grid": "i/64, i=1..63  (t1 = t0 lands on the grid where t0 is dyadic)",
        "cases": costs}

    # ---- Part 3: adverse check
    out["part3_channel_restriction_is_load_bearing"] = [
        full_channel_check(k, t0, F(1), 1, F(1, 10))
        for k in (3, 4) for t0 in (F(1, 8), F(1, 4))]

    with open(a.out, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)

    # ---- console
    s = out["part1_price_audit"]["summary"]
    print("=== PART 1: audit of price_of_evidence_B ===")
    for kk, vv in s.items():
        print(f"  {kk}: {vv}")
    print("\n=== PART 2a/2b: fixed-world response law ===")
    print(f"  construction blocks : {out['part2a_response_law_construction_blocks']['cases']} cases, "
          f"all_pass={out['part2a_response_law_construction_blocks']['all_pass']}")
    print(f"  decoupled blocks    : {out['part2b_response_law_decoupled_blocks']['cases']} cases, "
          f"all_pass={out['part2b_response_law_decoupled_blocks']['all_pass']}")
    print("\n=== PART 2c: acquisition cost, fixed world ===")
    print(f"{'k':>2} {'t0':>6} {'sigma':>5} {'t1*':>7} {'Gamma*':>10} {'min n':>14} {'interior':>9}")
    for c in out["part2c_cost"]["cases"]:
        print(f"{c['k']:>2} {c['t0']:>6} {c['sigma']:>5} {str(c['argmin_t1']):>7} "
              f"{c['Gamma_at_argmin']:>10.6f} {c['min_samples_X']:>14.2f} "
              f"{str(c['argmin_is_interior']):>9}")
    print("\n=== PART 3: is the floor a fact about information, or about the channel? ===")
    for c in out["part3_channel_restriction_is_load_bearing"]:
        print(f"  k={c['k']} t0={c['t0']}  slope_blind={c['linear_response_at_t1_eq_t0_is_identically_zero']}  "
              f"KL/sample={c['per_sample_gaussian_KL_at_t0']:.6g}  "
              f"full-channel n~{c['full_channel_samples_for_5pct_error_approx']:.2f}")
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
