#!/usr/bin/env python3
"""N5 -- measurement-RESOLUTION robustness of the QUERY sufficiency claim.

The existing QUERY result (scripts/QUERY_restricted_decoder_exact.py, artifact
research/high_risk_20260910/QUERY_restricted_decoder_exact.json) is an EXACT-KEY
statement: two units collide iff their restricted summaries are bit-identical.
This probe replaces exact key equality by a measurement resolution eta and asks
whether the claim survives.

THEOREM UNDER TEST (finite Theta, scalar target g, observations y = R(theta)+e
with ||e||_{w,inf} <= eta):

    E*_eta := inf_psi sup_{theta, ||e||<=eta} |psi(R(theta)+e) - g(theta)|
            = (1/2) * max{ |g(a)-g(b)| : ||R(a)-R(b)||_{w,inf} <= 2 eta }

    eta_crit(eps) := (1/2) * min{ ||R(a)-R(b)||_{w,inf} : |g(a)-g(b)| > 2 eps }
    (E*_eta <= eps for every eta < eta_crit(eps); E*_eta > eps at eta = eta_crit.
     If no pair has |g(a)-g(b)| > 2 eps the min is over the empty set: that case
     is SPLIT OUT, never coerced to a number.)

This is the Donoho optimal-recovery modulus of continuity specialised to a finite
world set; the identity is NOT claimed as novel (see the findings file).

WHAT FAILS LOUDLY (AssertionError, never a print-and-exit-0):
  * the pairwise formula vs an independent subset/compatibility-pattern brute
    force vs an explicit decoder brute force over a rational observation grid;
  * the eta_crit threshold property, checked at eta just below, at, and above;
  * a DISCRIMINATING negative control: the "connected component" fallacy (the
    2eta relation is NOT transitive) must give a strictly LARGER value on a
    designed panel -- if it never did, the pairwise formula would be a
    relabelling of the exact-key quotient and this package would be empty;
  * the exact-key legacy radius must equal E*_0;
  * monotonicity of eta -> E*_eta;
  * a structural audit of the panel's own confound filter.

CONFIGURATIONS DELIBERATELY SKIPPED (stated, not silent):
  * Part 1 subset brute force is capped at n <= 12 worlds (2^12 patterns) and
    dimension <= 3; larger synthetic panels use the pairwise formula only.
  * Part 3 full-panel (1600 units, 1.28M pairs) sweeps every catalog subset in
    float64 and then re-certifies ONLY the arg-min pair in exact rational
    arithmetic; it does not re-certify all 1.28M distances exactly.
  * The panel itself is NOT regenerated here (it needs the external rware
    runtime); this probe consumes the committed artifact and re-derives every
    count from the raw records rather than trusting the summary JSON.
  * Shapley targets are reported for the baseline representation only; the
    32-subset sweep uses the ATE target, matching the claim being audited.

Re-run:  python3 scripts/N5_resolution_minimax.py
"""
from __future__ import annotations

import collections
import itertools
import json
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PANEL = ROOT / "research/high_risk_20260910/QUERY_natural_panel_v2.json"
LEGACY = ROOT / "research/high_risk_20260910/QUERY_restricted_decoder_exact.json"
OUT = ROOT / "research/high_risk_20260910/N5_resolution_minimax_20260913.json"

NOOP = 0
N_ACTIONS = 5
INF = None  # explicit "no such pair" sentinel; never a number


# ==========================================================================
# core quantities (exact rational arithmetic)
# ==========================================================================

def winf(a, b):
    """Weighted-inf-norm distance; inputs already divided by their accuracies."""
    return max((abs(x - y) for x, y in zip(a, b)), default=Fr(0))


def estar_pairwise(R, g, eta):
    """(1/2) max |g(a)-g(b)| over pairs with ||R(a)-R(b)||_inf <= 2 eta."""
    n = len(R)
    best = Fr(0)
    for i in range(n):
        for j in range(i, n):
            if winf(R[i], R[j]) <= 2 * eta:
                d = abs(g[i] - g[j])
                if d > best:
                    best = d
    return Fr(best, 1) / 2 if isinstance(best, int) else best / 2


def estar_subsets(R, g, eta, cap=12):
    """INDEPENDENT brute force: sup over observations y of the halfrange of g
    over the worlds compatible with y.

    The compatible set at y is {theta : ||y - R(theta)||_inf <= eta}; as y ranges
    over R^d these sets are exactly the subsets S whose boxes have a common
    point, i.e. for every coordinate d:  max_S (R_d - eta) <= min_S (R_d + eta).
    Enumerating subsets therefore evaluates the true sup without ever using the
    pairwise formula.  Capped at `cap` worlds.
    """
    n = len(R)
    if n > cap:
        raise ValueError(f"subset brute force capped at {cap} worlds, got {n}")
    dim = len(R[0])
    best = Fr(0)
    for r in range(1, n + 1):
        for S in itertools.combinations(range(n), r):
            ok = True
            for d in range(dim):
                lo = max(R[i][d] - eta for i in S)
                hi = min(R[i][d] + eta for i in S)
                if lo > hi:
                    ok = False
                    break
            if not ok:
                continue
            gs = [g[i] for i in S]
            half = (max(gs) - min(gs)) / 2
            if half > best:
                best = half
    return best


def estar_decoder_gridsearch(R, g, eta, refine=2):
    """Decoder brute force on a finite rational observation grid.

    For each grid observation y the decoder value is chosen by an explicit search
    over candidate values (all pairwise midpoints of g), so 'the midrange is
    optimal' is CHECKED here, not assumed.  Because the decoder's value at y
    does not constrain its value elsewhere, inf_psi sup = sup_y inf_c.
    The grid contains every coordinate of every R(theta) shifted by
    k*eta/refine for k in [-refine, refine] and every pairwise midpoint
    coordinate, so it contains the midpoint witness of the lower bound.
    Returns a LOWER bound on the true sup (a grid can only miss).
    """
    n, dim = len(R), len(R[0])
    coords = []
    for d in range(dim):
        vals = set()
        for i in range(n):
            for k in range(-refine, refine + 1):
                vals.add(R[i][d] + Fr(k, refine) * eta)
            for j in range(n):
                vals.add((R[i][d] + R[j][d]) / 2)
        coords.append(sorted(vals))
    cand = sorted({(g[i] + g[j]) / 2 for i in range(n) for j in range(n)})
    best = Fr(0)
    for y in itertools.product(*coords):
        comp = [i for i in range(n) if winf(y, R[i]) <= eta]
        if not comp:
            continue
        loc = min(max(abs(c - g[i]) for i in comp) for c in cand)
        if loc > best:
            best = loc
    return best


def estar_components(R, g, eta):
    """NEGATIVE CONTROL, deliberately WRONG: treat 2-eta-closeness as if it were
    an equivalence relation and take the halfrange over connected components.
    Must strictly exceed the truth on the designed chain panel below."""
    n = len(R)
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(n):
        for j in range(i + 1, n):
            if winf(R[i], R[j]) <= 2 * eta:
                a, b = find(i), find(j)
                if a != b:
                    parent[a] = b
    comp = collections.defaultdict(list)
    for i in range(n):
        comp[find(i)].append(g[i])
    return max((max(v) - min(v)) / 2 for v in comp.values())


def eta_crit(R, g, eps):
    """(1/2) min ||R(a)-R(b)|| over pairs with |g(a)-g(b)| > 2 eps.
    Returns (value, witness) or (INF, None) when there is no such pair."""
    n = len(R)
    best, wit = None, None
    for i in range(n):
        for j in range(i + 1, n):
            if abs(g[i] - g[j]) > 2 * eps:
                d = winf(R[i], R[j])
                if best is None or d < best:
                    best, wit = d, (i, j)
    if best is None:
        return INF, None
    return best / 2, wit


def legacy_exact_radius(R, g):
    """Exact-key radius exactly as Lean CIGAMF.P13.QueryScalarMinimax.radius and
    as QUERY_restricted_decoder_exact.exact_decoder_report compute it: the max
    half-diameter over fibres of the EXACT key.  Independent code path."""
    fib = collections.defaultdict(list)
    for r, gg in zip(R, g):
        fib[tuple(r)].append(gg)
    return max((max(v) - min(v)) / 2 for v in fib.values())


# ==========================================================================
# PART 1 -- exact identity on small synthetic panels, degenerate cases included
# ==========================================================================

def synthetic_panels():
    """(name, R, g, etas).  R entries are already in accuracy units."""
    F = Fr
    P = []
    # single world
    P.append(("single_world", [[F(0)]], [F(7)], [F(0), F(1), F(5)]))
    # two worlds, distinct responses, distinct targets
    P.append(("two_worlds_1d", [[F(0)], [F(3)]], [F(0), F(1)],
              [F(0), F(1, 2), F(3, 2), F(2), F(10)]))
    # ties in g (targets equal, responses differ)
    P.append(("tie_in_g", [[F(0)], [F(3)], [F(9)]], [F(2), F(2), F(2)],
              [F(0), F(1), F(7)]))
    # duplicate responses with different targets: exact-key failure at eta=0
    P.append(("duplicate_responses", [[F(0)], [F(0)], [F(4)]], [F(0), F(5), F(1)],
              [F(0), F(1), F(3)]))
    # duplicate responses AND duplicate targets
    P.append(("duplicate_everything", [[F(1)], [F(1)]], [F(3), F(3)],
              [F(0), F(2)]))
    # the non-transitivity chain: this is where the component fallacy fails
    P.append(("chain_nontransitive", [[F(0)], [F(2)], [F(4)]], [F(0), F(5), F(10)],
              [F(0), F(1), F(2)]))
    # 2-d, mixed
    P.append(("two_dim", [[F(0), F(0)], [F(1), F(0)], [F(0), F(3)], [F(1), F(3)]],
              [F(0), F(1), F(4), F(6)], [F(0), F(1, 2), F(1), F(3, 2), F(2)]))
    # 3-d with a half-integer separation (midpoint is not on the input lattice)
    P.append(("three_dim_halfint",
              [[F(0), F(0), F(0)], [F(1), F(0), F(0)], [F(0), F(1), F(1)]],
              [F(0), F(3), F(-2)], [F(0), F(1, 4), F(1, 2), F(1)]))
    # negative and fractional targets
    P.append(("fractional_targets",
              [[F(0)], [F(1, 2)], [F(3, 2)]], [F(-1, 3), F(1, 7), F(9, 5)],
              [F(0), F(1, 4), F(1, 2), F(3)]))
    # all responses identical (representation carries nothing)
    P.append(("constant_response", [[F(5)], [F(5)], [F(5)]], [F(0), F(2), F(9)],
              [F(0), F(3)]))
    # all targets constant (the case a "filter out constant targets" step drops)
    P.append(("constant_target", [[F(0)], [F(1)], [F(8)]], [F(4), F(4), F(4)],
              [F(0), F(1, 2), F(9)]))
    return P


def part1():
    print("=" * 78)
    print("PART 1  exact minimax identity, three independent routes")
    print("=" * 78)
    rows = []
    for name, R, g, etas in synthetic_panels():
        for eta in etas:
            a = estar_pairwise(R, g, eta)
            b = estar_subsets(R, g, eta)
            c = estar_decoder_gridsearch(R, g, eta)
            if a != b:
                raise AssertionError(
                    f"pairwise != subset brute force on {name} eta={eta}: {a} vs {b}")
            if c > a:
                raise AssertionError(
                    f"grid decoder search EXCEEDS the claimed optimum on {name} "
                    f"eta={eta}: {c} > {a} (upper bound is wrong)")
            if c != a:
                raise AssertionError(
                    f"grid decoder search misses the claimed optimum on {name} "
                    f"eta={eta}: {c} < {a} (lower bound witness not attained)")
            rows.append({"panel": name, "eta": str(eta), "E_star": str(a)})
            print(f"   {name:<22} eta={str(eta):>5}  E*={str(a):>7}  "
                  f"subsets={str(b):>7}  grid-decoder={str(c):>7}  OK")
        # eta = 0 must reproduce the legacy exact-key radius
        lr = legacy_exact_radius(R, g)
        e0 = estar_pairwise(R, g, Fr(0))
        if lr != e0:
            raise AssertionError(f"E*_0 != exact-key radius on {name}: {e0} vs {lr}")
        # monotone in eta
        vals = [estar_pairwise(R, g, e) for e in sorted(set(etas))]
        if any(x > y for x, y in zip(vals, vals[1:])):
            raise AssertionError(f"E*_eta not monotone on {name}: {vals}")
    print("   -> pairwise == subset brute force == grid decoder search on "
          f"{len(rows)} (panel, eta) cells; E*_0 == exact-key radius; monotone.")
    return rows


def part1_controls():
    print("\n" + "=" * 78)
    print("PART 1b  DISCRIMINATING controls (each must be able to return False)")
    print("=" * 78)
    F = Fr
    R = [[F(0)], [F(2)], [F(4)]]
    g = [F(0), F(5), F(10)]
    eta = F(1)
    truth = estar_pairwise(R, g, eta)
    comp = estar_components(R, g, eta)
    if not comp > truth:
        raise AssertionError(
            "component fallacy did NOT differ from the pairwise value; the "
            "2-eta relation would then be transitive here and this control is "
            "not a control")
    print(f"   non-transitivity control: pairwise E*={truth}, component "
          f"fallacy={comp}  (strictly larger -- control discriminates)")

    # a control that CAN fail: if the identity were 'max over pairs with
    # distance < 2 eta' (strict) instead of '<=', this panel would expose it.
    R2 = [[F(0)], [F(2)]]
    g2 = [F(0), F(6)]
    got = estar_pairwise(R2, g2, F(1))
    if got != F(3):
        raise AssertionError(f"boundary (distance exactly 2 eta) wrong: {got}")
    strict = Fr(0)
    for i in range(2):
        for j in range(2):
            if winf(R2[i], R2[j]) < 2 * F(1):
                strict = max(strict, abs(g2[i] - g2[j]) / 2)
    if strict == got:
        raise AssertionError("strict-vs-nonstrict control is not discriminating")
    print(f"   closed-ball boundary control: <= gives {got}, < would give "
          f"{strict}  (they differ -- the '<=' in the statement is load-bearing)")

    # eta_crit threshold property, including the empty-bad-pair split
    for name, R3, g3 in [
            ("threshold_chain", [[F(0)], [F(3)], [F(10)]], [F(0), F(1), F(4)]),
            ("threshold_ties", [[F(0)], [F(1)], [F(2)]], [F(0), F(0), F(0)])]:
        for eps in [F(0), F(1, 2), F(1), F(2), F(5)]:
            ec, wit = eta_crit(R3, g3, eps)
            if ec is INF:
                # no pair exceeds 2 eps: the tolerance is already enough for
                # EVERY eta, including eta = +infinity (all pairs compatible)
                huge = max(max(abs(a[0] - b[0]) for a in R3 for b in R3), F(1))
                if not estar_pairwise(R3, g3, huge) <= eps:
                    raise AssertionError(
                        f"{name}: empty-bad-pair case claimed unconditional "
                        f"sufficiency but E* at eta={huge} exceeds eps={eps}")
                print(f"   {name:<18} eps={str(eps):>3}  eta_crit=NO BAD PAIR "
                      f"(tolerance already met for every eta)")
                continue
            below = ec * Fr(9, 10)
            if not estar_pairwise(R3, g3, below) <= eps:
                raise AssertionError(f"{name}: E* exceeds eps strictly below eta_crit")
            if not estar_pairwise(R3, g3, ec) > eps:
                raise AssertionError(
                    f"{name}: E* does NOT exceed eps AT eta_crit={ec} (the "
                    "threshold is not attained by the minimising pair)")
            print(f"   {name:<18} eps={str(eps):>3}  eta_crit={str(ec):>6} "
                  f"witness={wit}  below OK / at-equality breaks OK")
    print("   -> all controls discriminate.")


# ==========================================================================
# PART 2 -- the real panel
# ==========================================================================

CATALOG = ("mechanism_features", "privileged_geometry", "relation_features",
           "response_h2", "weak_prior_score")

# Declared measurement accuracies, fixed BEFORE any target is read.
#   integer count coordinates: the environment's own quantum.
#     RewardType.GLOBAL adds exactly +1 per delivered request, so a horizon-h
#     return is an integer number of deliveries and 1 delivery is the finest
#     resolvable difference.  Grid geometry is in whole cells.
#   float model-output coordinates: no instrument accuracy for a learned
#     feature is documented anywhere in this repo, so one accuracy unit is
#     DECLARED to be that coordinate's observed dynamic range over the panel
#     (a response-side quantity: no target is touched).  eta is then read as
#     "fraction of the feature's dynamic range".
INTEGER_BLOCKS = {"c1", "c2", "privileged_geometry"}
FLOAT_BLOCKS = {"relation_features", "mechanism_features", "weak_prior_score"}


def load_units():
    payload = json.loads(PANEL.read_text())
    cands = payload["candidates"]
    units = []
    counts = collections.Counter()
    counts["records_in_artifact"] = len(payload["records"])
    for rec in payload["records"]:
        if rec.get("status") != "OK":
            counts["records_filtered_panel_error"] += 1
            continue
        counts["records_ok"] += 1
        for jj, agent in enumerate(cands):
            base1 = rec["R1"][jj][NOOP]
            base2 = rec["R2"][jj][NOOP]
            baseT = rec["RT"][jj][NOOP]
            u = {
                "seed": rec["seed"], "t": rec["t"], "cand": int(agent), "local": jj,
                "physical_key": rec["physical_key"], "rng_key": rec["rng_key"],
                "c1": [Fr(v - base1) for v in rec["R1"][jj]],
                "c2": [Fr(v - base2) for v in rec["R2"][jj]],
                "cT": [Fr(v - baseT) for v in rec["RT"][jj]],
            }
            u["ateT"] = Fr(sum(rec["RT"][jj]), N_ACTIONS) - Fr(baseT)
            for k, v in rec["catalog"].items():
                row = v[jj]
                u[k] = [Fr(float(x)) for x in (row if isinstance(row, list) else [row])]
            units.append(u)
    return payload, units, counts


def block_vector(u, block):
    return u["c2"] if block == "response_h2" else u[block]


def accuracies(units):
    """sigma per coordinate.  Uses responses/features only -- never a target."""
    sig = {}
    rng = {}
    for block in ("c1", "c2", "relation_features", "mechanism_features",
                  "weak_prior_score", "privileged_geometry"):
        dim = len(block_vector(units[0], "response_h2" if block == "c2" else block))
        for d in range(dim):
            vals = [block_vector(u, "response_h2" if block == "c2" else block)[d]
                    for u in units]
            lo, hi = min(vals), max(vals)
            rng[(block, d)] = hi - lo
            if block in INTEGER_BLOCKS:
                sig[(block, d)] = Fr(1)          # physical quantum
            else:
                sig[(block, d)] = (hi - lo) if hi > lo else Fr(1)
    return sig, rng


def rep_vector(u, extras, sig):
    out = []
    for d, v in enumerate(u["c1"]):
        out.append(v / sig[("c1", d)])
    for name in extras:
        block = "c2" if name == "response_h2" else name
        for d, v in enumerate(block_vector(u, name)):
            out.append(v / sig[(block, d)])
    return out


def rep_labels(extras):
    lab = [("c1", d) for d in range(N_ACTIONS)]
    for name in extras:
        block = "c2" if name == "response_h2" else name
        dim = {"c2": 5, "relation_features": 6, "mechanism_features": 4,
               "weak_prior_score": 1, "privileged_geometry": 7}[block]
        lab += [(block, d) for d in range(dim)]
    return lab


def curve_and_crit(R, g, eps_grid):
    """Exact (D,G) pair scan.  Returns the full E*_eta breakpoint curve and
    eta_crit for each eps.  O(n^2) in exact rationals -- used on the small
    subpanel; the full panel uses the float64 path with an exact re-check."""
    n = len(R)
    pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            pairs.append((winf(R[i], R[j]), abs(g[i] - g[j]), i, j))
    pairs.sort(key=lambda x: x[0])
    curve, run = [], Fr(0)
    for d, gap, _, _ in pairs:
        if gap > run:
            run = gap
            curve.append((d, run / 2))
    crit = {}
    for eps in eps_grid:
        cand = [(d, i, j) for d, gap, i, j in pairs if gap > 2 * eps]
        if not cand:
            crit[str(eps)] = {"eta_crit": None, "witness": None,
                              "note": "no pair exceeds 2*eps: tolerance already met"}
        else:
            d, i, j = min(cand)
            crit[str(eps)] = {"eta_crit": str(d / 2), "eta_crit_float": float(d / 2),
                              "witness": (i, j)}
    return curve, crit, len(pairs)


def part3():
    print("\n" + "=" * 78)
    print("PART 3  the collected RWARE panel -- COMPLETE inclusion accounting")
    print("=" * 78)
    payload, units, counts = load_units()
    art = payload["counts"]
    n_cand = len(payload["candidates"])
    constant = [u for u in units if all(v == 0 for v in u["cT"])]
    evaluable = [u for u in units if any(v != 0 for v in u["cT"])]
    acct = {
        "generated_env_steps": art["generated_steps"],
        "episodes": art["episodes"],
        "reachable_snapshots": art["reachable_snapshots"],
        "filtered_panel_error": art.get("filtered_panel_error", 0),
        "panel_built": art["panel_built"],
        "candidates_per_snapshot": n_cand,
        "units_total": len(units),
        "units_constant_target": len(constant),
        "units_evaluable": len(evaluable),
        "units_c1_all_zero": sum(1 for u in units if all(v == 0 for v in u["c1"])),
    }
    for k, v in acct.items():
        print(f"   {k:<28} {v}")
    if art["reachable_snapshots"] != art["panel_built"] + art.get("filtered_panel_error", 0):
        raise AssertionError("snapshot accounting does not close")
    if art["panel_built"] * n_cand != len(units):
        raise AssertionError("unit accounting does not close")
    if len(constant) + len(evaluable) != len(units):
        raise AssertionError("constant/evaluable split does not close")

    # ---- structural audit of the panel's own confound filter -------------
    phys = collections.Counter((u["physical_key"], u["local"]) for u in units)
    full = collections.Counter((u["physical_key"], u["rng_key"], u["local"]) for u in units)
    audit = {
        "physical_state_groups": len(phys),
        "max_units_sharing_a_physical_key": max(phys.values()),
        "full_key_groups": len(full),
        "max_units_sharing_physical_and_rng_key": max(full.values()),
        "rng_confound_filter_can_ever_fire": max(phys.values()) > 1,
        "determinism_check_can_ever_fail": max(full.values()) > 1,
    }
    print("   -- confound-filter audit --")
    for k, v in audit.items():
        print(f"   {k:<44} {v}")
    if audit["rng_confound_filter_can_ever_fire"]:
        print("   (filter is live on this panel: rng-confounded pairs exist)")
    else:
        print("   (filter is VACUOUS on this panel: every physical_key is unique,")
        print("    so 'bad_pairs_rng_confounded' is forced to 0 by construction,")
        print("    not by evidence.  physical_key embeds the step counter.)")

    sig, rng = accuracies(units)
    print("   -- declared accuracies fixed from responses only (no target read) --")
    for k in sorted(sig, key=str):
        print(f"      sigma{str(k):<32} = {str(sig[k]):<22} observed range "
              f"{float(rng[k]):.6g}")

    eps_grid = [Fr(0), Fr(1, 10), Fr(1, 5), Fr(3, 10), Fr(1, 2)]
    results = {}

    # ---- evaluable subpanel: every catalog subset, exact arithmetic ------
    print("\n   -- evaluable subpanel (n=%d): all 32 catalog subsets, exact --"
          % len(evaluable))
    g_eval = [u["ateT"] for u in evaluable]
    sub = {}
    for r in range(len(CATALOG) + 1):
        for extras in itertools.combinations(CATALOG, r):
            R = [rep_vector(u, extras, sig) for u in evaluable]
            e0 = estar_pairwise(R, g_eval, Fr(0))
            lr = legacy_exact_radius(R, g_eval)
            if e0 != lr:
                raise AssertionError(f"E*_0 != exact-key radius for {extras}")
            curve, crit, npairs = curve_and_crit(R, g_eval, eps_grid)
            key = "+".join(extras) if extras else "c1_only"
            ec0 = crit[str(Fr(0))]
            wit = ec0.get("witness")
            sep = _sep(R, wit[0], wit[1], extras) if wit else []
            sub[key] = {
                "bought": list(extras), "n_pairs": npairs,
                "E_star_0": str(e0),
                "exact_keys_sufficient": e0 == 0,
                "eta_crit_eps0": ec0["eta_crit"],
                "eta_crit_eps0_float": ec0.get("eta_crit_float"),
                "eta_crit_by_eps": crit,
                "critical_pair_units": ([
                    {"seed": evaluable[wit[0]]["seed"], "t": evaluable[wit[0]]["t"],
                     "cand": evaluable[wit[0]]["cand"]},
                    {"seed": evaluable[wit[1]]["seed"], "t": evaluable[wit[1]]["t"],
                     "cand": evaluable[wit[1]]["cand"]}] if wit else None),
                "critical_pair_separations": sep,
                "critical_pair_separated_by_privileged_geometry": any(
                    s["coordinate"].startswith("privileged_geometry") for s in sep),
                "critical_pair_separated_by_response_only": all(
                    s["coordinate"].startswith(("c1", "c2")) for s in sep) if sep else None,
                "curve_breakpoints": [(str(d), str(v)) for d, v in curve][:40],
                "n_curve_breakpoints": len(curve),
            }
            flag = "SUFFICIENT@eta=0" if e0 == 0 else ""
            print(f"      {key:<66} E*_0={str(e0):>5}  eta_crit(0)="
                  f"{(('%.3g' % ec0['eta_crit_float']) if ec0['eta_crit'] else 'NO BAD PAIR'):>10}"
                  f"  {flag}")
    results["evaluable_subpanel"] = sub

    # ---- full panel (no constant filtering) -----------------------------
    print("\n   -- FULL panel (n=%d, constants NOT removed): declared subsets --"
          % len(units))
    print("      SWEEP SHRUNK ON PURPOSE: 1600 units = 1,279,200 pairs; the")
    print("      32-subset sweep is run on the evaluable subpanel only and the")
    print("      full panel is run for 6 declared representations.  Stated, not")
    print("      silent.")
    declared = [(), ("response_h2",), ("privileged_geometry",), ("relation_features",),
                ("privileged_geometry", "relation_features"), CATALOG]
    g_full = [u["ateT"] for u in units]
    fullres = {}
    for extras in declared:
        R = [rep_vector(u, extras, sig) for u in units]
        key = "+".join(extras) if extras else "c1_only"
        t0 = time.time()
        out = _full_panel_scan(R, g_full, eps_grid, units, extras, sig)
        out["seconds"] = round(time.time() - t0, 1)
        fullres[key] = out
        print(f"      {key:<66} E*_0={out['E_star_0']:>5}  eta_crit(0)="
              f"{(('%.3g' % out['eta_crit_eps0_float']) if out['eta_crit_eps0'] else 'NO BAD PAIR'):>10}"
              f"  ({out['seconds']}s)")
    results["full_panel"] = fullres
    return payload, units, evaluable, acct, audit, sig, rng, results


def _full_panel_scan(R, g, eps_grid, units, extras, sig):
    """float64 chunked scan of all pairs, with the arg-min pair re-certified in
    exact rational arithmetic.

    The TARGET side is kept exactly integral: every g here is a rational, so the
    gaps are scaled to int64 by the common denominator L and every
    "|g(a)-g(b)| > 2 eps" test is an integer comparison.  Doing that test in
    float64 is WRONG -- |2.6 - 2.4| evaluates to 0.20000000000000018, which is
    strictly greater than 0.2 in float and not greater than 1/5 in fact; the
    earlier version of this function tripped its own arg-min assertion on
    exactly that.  The RESPONSE side (the distances D) is float64 and only the
    arg-min distance is re-certified exactly -- stated here, not silent.
    """
    import numpy as np
    from math import gcd
    n = len(R)
    L = 1
    for v in g:
        L = L * v.denominator // gcd(L, v.denominator)
    Gi = np.array([int(v * L) for v in g], dtype=np.int64)
    X = np.array([[float(v) for v in r] for r in R], dtype=np.float64)
    best_d = {str(e): (np.inf, None) for e in eps_grid}
    # gap > 2*p/q  <=>  gap_int * q > 2*p*L      (all integers)
    thr = {str(e): 2 * e.numerator * L for e in eps_grid}
    qs = {str(e): e.denominator for e in eps_grid}
    ds, gs = [], []
    CH = 128
    for s0 in range(0, n, CH):
        blk = X[s0:s0 + CH]
        d = np.abs(blk[:, None, :] - X[None, :, :]).max(axis=2)
        gg = np.abs(Gi[s0:s0 + CH, None] - Gi[None, :])
        rows = np.arange(s0, min(s0 + CH, n))[:, None]
        cols = np.arange(n)[None, :]
        mask = cols > rows
        ds.append(d[mask])
        gs.append(gg[mask])
        for eps in eps_grid:
            k_ = str(eps)
            m2 = mask & (gg * qs[k_] > thr[k_])
            if not m2.any():
                continue
            dv = np.where(m2, d, np.inf)
            flat = int(np.argmin(dv))
            i, j = np.unravel_index(flat, dv.shape)
            if dv[i, j] < best_d[k_][0]:
                best_d[k_] = (float(dv[i, j]), (int(s0 + i), int(j)))
    D = np.concatenate(ds)
    Gd = np.concatenate(gs)
    order = np.argsort(D, kind="stable")
    D, Gd = D[order], Gd[order]
    run = np.maximum.accumulate(Gd)
    bp, last = [], -1
    for i in range(len(D)):
        if run[i] > last:
            last = int(run[i])
            bp.append((float(D[i]), str(Fr(int(run[i]), 2 * L))))
    e0 = legacy_exact_radius(R, g)      # independent of the float scan
    out = {"n_pairs": int(len(D)), "E_star_0": str(e0),
           "exact_keys_sufficient": bool(e0 == 0),
           "target_scale_denominator": L,
           "curve_breakpoints": [(f"{a:.6g}", b) for a, b in bp][:40],
           "n_curve_breakpoints": len(bp)}
    crit = {}
    for eps in eps_grid:
        dv, wit = best_d[str(eps)]
        if wit is None:
            crit[str(eps)] = {"eta_crit": None,
                              "note": "no pair exceeds 2*eps: tolerance already met"}
            continue
        i, j = wit
        exact = winf(R[i], R[j]) / 2          # exact re-certification of arg-min
        if abs(float(exact) - dv / 2) > 1e-12 * max(1.0, dv):
            raise AssertionError(
                f"float scan and exact re-check disagree for {extras} eps={eps}: "
                f"{float(exact)} vs {dv/2}")
        if not abs(g[i] - g[j]) > 2 * eps:
            raise AssertionError("arg-min witness does not actually exceed 2*eps")
        crit[str(eps)] = {
            "eta_crit": str(exact), "eta_crit_float": float(exact),
            "witness_units": [
                {"seed": units[i]["seed"], "t": units[i]["t"], "cand": units[i]["cand"]},
                {"seed": units[j]["seed"], "t": units[j]["t"], "cand": units[j]["cand"]}],
            "witness_target_gap": str(abs(g[i] - g[j])),
            "witness_per_coordinate_separation": _sep(R, i, j, extras),
        }
    out["eta_crit_by_eps"] = crit
    c0 = crit[str(Fr(0))]
    out["eta_crit_eps0"] = c0["eta_crit"]
    out["eta_crit_eps0_float"] = c0.get("eta_crit_float")
    out["threshold_check"] = _threshold_check(D, run, c0, e0, L)
    return out


def _threshold_check(D, run, c0, e0, L=1):
    """E*_eta = 0 for every eta < eta_crit(0) and E*_eta > 0 at eta_crit(0).

    Three genuinely different regimes, each handled explicitly:
      * no bad pair at all           -> g is constant; nothing to certify.
      * eta_crit(0) == 0             -> a bad pair at distance 0, i.e. the exact
                                        keys already collide.  There is NO eta
                                        strictly below 0, so the 'below' half is
                                        vacuous and is reported as vacuous, not
                                        as a pass.  The 'at' half still bites.
      * eta_crit(0) > 0              -> both halves bite.
    """
    import numpy as np
    if c0["eta_crit"] is None:
        if e0 != 0:
            raise AssertionError("no bad pair but the exact-key radius is nonzero")
        return {"regime": "no_bad_pair", "E_star_at_any_eta": "0"}
    ec = float(Fr(c0["eta_crit"]))
    at_mask = D <= 2 * ec * (1 + 1e-12)
    if not at_mask.any():
        raise AssertionError("no pair is compatible at eta_crit(0)")
    at = Fr(int(run[at_mask].max()), 2 * L)
    if not at > 0:
        raise AssertionError("E* does not become positive at eta_crit(0)")
    if ec == 0.0:
        if e0 == 0:
            raise AssertionError("eta_crit(0)=0 but the exact keys are sufficient")
        return {"regime": "eta_crit_zero_exact_keys_already_collide",
                "below_half_is_vacuous": True,
                "E_star_at_eta_crit": str(at), "E_star_0": str(e0)}
    below_mask = D < 2 * ec * (1 - 1e-12)
    below = Fr(int(run[below_mask].max()), 2 * L) if below_mask.any() else Fr(0)
    if below != 0:
        raise AssertionError(
            f"E* = {below} is nonzero strictly below eta_crit(0) = {ec}")
    return {"regime": "strict_positive_threshold",
            "E_star_sup_over_eta_below_eta_crit": str(below),
            "E_star_at_eta_crit": str(at),
            "n_pairs_strictly_below": int(below_mask.sum())}


def _sep(R, i, j, extras):
    lab = rep_labels(extras)
    out = []
    for k, (blk, d) in enumerate(lab):
        s = abs(R[i][k] - R[j][k])
        if s != 0:
            out.append({"coordinate": f"{blk}[{d}]", "separation_in_accuracy_units": str(s),
                        "separation_float": float(s)})
    return out


def packing_floor(R):
    """(1/2) * min over ALL distinct-response pairs of ||R(a)-R(b)||.

    eta_crit(eps) is a min over the SUBSET of pairs whose targets differ by more
    than 2 eps, so it always satisfies eta_crit(eps) >= packing_floor, with
    equality exactly when the closest distinct pair in the whole representation
    is already a bad pair.  (An earlier draft of this probe called this a
    "ceiling" and asserted the opposite inequality; the real panel produced
    eta_crit = 0.0588 > floor = 0.0294 and exposed it.  The floor is the number
    an eta_crit must be read against: an eta_crit sitting ON the floor is the
    worst case the packing allows, and a large eta_crit is only meaningful
    relative to the shuffled null below.)
    """
    n = len(R)
    best = None
    for i in range(n):
        for j in range(i + 1, n):
            d = winf(R[i], R[j])
            if d == 0:
                continue
            if best is None or d < best:
                best = d
    return None if best is None else best / 2


def certifiable_fraction(R, g, eta, eps):
    """Fraction of units u for which the decoder is GUARANTEED within eps when
    the truth is u and the measurement error is at most eta.

    If the truth is u then the observation y = R(u)+e lies within eta of R(u),
    so every world compatible with y lies within 2 eta of R(u).  The halfrange
    of g over that superset is therefore a valid per-unit worst-case error
    bound.  A unit is 'eps-certifiable at resolution eta' when that bound is
    <= eps.  (It is an UPPER bound on the per-unit worst case, so this fraction
    is a LOWER bound on the true certifiable fraction.)
    """
    n = len(R)
    ok = 0
    for i in range(n):
        lo = hi = g[i]
        for j in range(n):
            if winf(R[i], R[j]) <= 2 * eta:
                if g[j] < lo:
                    lo = g[j]
                if g[j] > hi:
                    hi = g[j]
        if (hi - lo) / 2 <= eps:
            ok += 1
    return Fr(ok, n)


# ==========================================================================
# PART 4 -- the decisive question and a shuffle control
# ==========================================================================

def part4(units, evaluable, sig, results):
    print("\n" + "=" * 78)
    print("PART 4  decisive question: do exact-key-sufficient instances have")
    print("        eta_crit near zero?  Plus a label-shuffle control.")
    print("=" * 78)
    ETA_MEAS = Fr(1, 2)     # one accuracy unit of total blur between two worlds
    ETA_FINE = Fr(1, 200)   # a 200x finer instrument
    print(f"   declared resolutions (fixed before any target was read): "
          f"eta_meas={ETA_MEAS}, eta_fine={ETA_FINE}")
    verdict = []
    for scope, res in (("evaluable_subpanel", results["evaluable_subpanel"]),
                       ("full_panel", results["full_panel"])):
        for key, r in res.items():
            if not r.get("exact_keys_sufficient"):
                continue
            ec = r["eta_crit_eps0"]
            if ec is None:
                verdict.append({"scope": scope, "representation": key,
                                "eta_crit_eps0": None,
                                "survives_eta_meas": True,
                                "note": "g is constant on this panel: no bad pair"})
                continue
            ecf = Fr(ec)
            v = {"scope": scope, "representation": key,
                 "eta_crit_eps0": str(ecf), "eta_crit_eps0_float": float(ecf),
                 "survives_eta_meas": bool(ecf > ETA_MEAS),
                 "survives_eta_fine": bool(ecf > ETA_FINE)}
            verdict.append(v)
            print(f"   {scope:<20} {key:<48} eta_crit(0)={float(ecf):.6g}  "
                  f"survives eta_meas={v['survives_eta_meas']}  "
                  f"eta_fine={v['survives_eta_fine']}")
    if not verdict:
        raise AssertionError("no exact-key-sufficient representation found; the "
                             "audit target does not exist in this artifact")

    # ---- the two headline statements, CERTIFIED here (each can return False) --
    suff = [v for v in verdict if v.get("eta_crit_eps0") is not None]
    if not suff:
        raise AssertionError("no sufficient representation with a finite eta_crit")
    if any(v["survives_eta_meas"] for v in suff):
        raise AssertionError(
            "headline 1 is FALSE: some exact-key-sufficient representation "
            "survives one quantum of measurement blur (eta = 1/2)")
    resp_coords = []
    for scope, res in (("evaluable_subpanel", results["evaluable_subpanel"]),):
        for key, rr in res.items():
            if not rr.get("exact_keys_sufficient"):
                continue
            seps = rr["critical_pair_separations"]
            if not seps:
                raise AssertionError(f"{key}: sufficient but no separating coordinate")
            resp_coords.append((key, [x["coordinate"] for x in seps]))
    float_only = all(
        all(c.startswith(("relation_features", "weak_prior_score",
                          "mechanism_features")) for c in cs)
        for _, cs in resp_coords)
    any_response = any(
        any(c.startswith(("c1[", "c2[")) for c in cs) for _, cs in resp_coords)
    any_geometry = any(
        any(c.startswith("privileged_geometry") for c in cs) for _, cs in resp_coords)
    print("\n   headline 2 -- which coordinate carries the tightest certificate:")
    print(f"      every critical pair separated ONLY by float model outputs: {float_only}")
    print(f"      any critical pair separated by a QUERY RESPONSE (c1/c2):   {any_response}")
    print(f"      any critical pair separated by privileged_geometry:        {any_geometry}")
    if not float_only:
        raise AssertionError(
            "headline 2 is FALSE: some critical pair is separated by a "
            "coordinate other than an undocumented float model output")
    headlines = {
        "no_sufficient_representation_survives_one_quantum_eta_half": True,
        "every_critical_pair_separated_only_by_float_model_outputs": float_only,
        "any_critical_pair_separated_by_query_response": any_response,
        "any_critical_pair_separated_by_privileged_geometry": any_geometry,
        "critical_coordinates_per_sufficient_subset": dict(resp_coords),
    }

    # ---- packing floor: the number every eta_crit must be read against ----
    g_eval = [u["ateT"] for u in evaluable]
    ceilings = {}
    print("\n   packing floor  (1/2)*min over ALL distinct-response pairs --")
    print("   eta_crit >= this for EVERY target relabelling; equality means the")
    print("   closest distinct pair in the representation is already a bad pair:")
    for extras in [(), ("privileged_geometry",), ("relation_features",),
                   ("privileged_geometry", "relation_features"),
                   ("privileged_geometry", "response_h2", "weak_prior_score"),
                   CATALOG]:
        key = "+".join(extras) if extras else "c1_only"
        Rk = [rep_vector(u, extras, sig) for u in evaluable]
        pc = packing_floor(Rk)
        e0k = legacy_exact_radius(Rk, g_eval)
        ec, _ = eta_crit(Rk, g_eval, Fr(0))
        ceilings[key] = {
            "exact_keys_sufficient": bool(e0k == 0),
            "packing_floor_distinct_responses": None if pc is None else str(pc),
            "packing_floor_distinct_responses_float": None if pc is None else float(pc),
            "eta_crit_eps0": None if ec is INF else str(ec),
            "eta_crit_equals_packing_floor": (pc is not None and ec is not INF
                                              and ec == pc)}
        # The floor bounds eta_crit only when there are no duplicate responses
        # among the bad pairs, i.e. exactly when the exact keys are sufficient.
        # Without that guard the inequality is simply false (c1_only has bad
        # pairs at distance 0 while its distinct-response floor is 1/2).
        if e0k == 0 and pc is not None and ec is not INF and ec < pc:
            raise AssertionError(
                f"eta_crit {ec} below the distinct-response packing floor {pc} "
                f"for the exact-key-sufficient representation {key}")
        print(f"      {key:<58} floor="
              f"{('%.6g' % float(pc)) if pc is not None else 'NA':>10}  "
              f"eta_crit(0)={('%.6g' % float(ec)) if ec is not INF else 'NO BAD PAIR':>10}"
              f"  suff={bool(e0k == 0)}"
              f"  on_floor={ceilings[key]['eta_crit_equals_packing_floor']}")

    # ---- eps-certifiable fraction curve ------------------------------------
    print("\n   fraction of eps-certifiable units (evaluable subpanel, n=%d)"
          % len(evaluable))
    eta_grid = [Fr(0), Fr(1, 200), Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 2), Fr(1)]
    eps_show = [Fr(0), Fr(1, 10), Fr(1, 5)]
    cert = {}
    Rrep = [rep_vector(u, CATALOG, sig) for u in evaluable]
    hdr = "      eta \\ eps  " + "".join(f"{str(e):>9}" for e in eps_show)
    print(hdr)
    for et in eta_grid:
        row = []
        for ep in eps_show:
            f = certifiable_fraction(Rrep, g_eval, et, ep)
            cert[f"eta={et};eps={ep}"] = str(f)
            row.append(f"{float(f):>9.3f}")
        print(f"      {str(et):>10}  " + "".join(row))
    print("      (representation = full catalog; the same table for c1 alone is")
    print("       in the JSON under certifiable_fraction_c1)")
    cert_c1 = {}
    Rc1 = [rep_vector(u, (), sig) for u in evaluable]
    for et in eta_grid:
        for ep in eps_show:
            cert_c1[f"eta={et};eps={ep}"] = str(
                certifiable_fraction(Rc1, g_eval, et, ep))

    # shuffle control: if eta_crit is the same after destroying the
    # representation/target relation, eta_crit measures nothing.
    import random
    extras = ("privileged_geometry", "relation_features")
    R = [rep_vector(u, extras, sig) for u in evaluable]
    obs, _ = eta_crit(R, g_eval, Fr(0))
    rnd = random.Random(20260913)
    shuf = []
    for _ in range(200):
        gp = g_eval[:]
        rnd.shuffle(gp)
        ec, _ = eta_crit(R, gp, Fr(0))
        shuf.append(float(ec) if ec is not INF else float("inf"))
    lo = min(shuf)
    hi = max(shuf)
    shuf.sort()
    frac_le = sum(1 for x in shuf if x <= float(obs)) / len(shuf)
    med = shuf[len(shuf) // 2]
    print(f"\n   shuffle control on {'+'.join(extras)} (200 target permutations):")
    print(f"      observed eta_crit(0) = {float(obs):.6g}")
    print(f"      shuffled range       = [{lo:.6g}, {hi:.6g}] median {med:.6g}  "
          f"fraction <= observed = {frac_le:.3f}")
    if lo == hi:
        raise AssertionError("shuffle control is degenerate (no variation): it "
                             "cannot discriminate and is not a control")
    print("      (a shuffled eta_crit as small as the observed one means the "
          "number\n       reflects the geometry of R, not a representation-target "
          "relation.)")
    return {"verdict": verdict,
            "headlines": headlines,
            "packing_floors": ceilings,
            "certifiable_fraction_full_catalog": cert,
            "certifiable_fraction_c1": cert_c1,
            "shuffle_control": {"representation": "+".join(extras),
                                "observed_eta_crit_eps0": str(obs),
                                "observed_float": float(obs),
                                "n_permutations": 200,
                                "shuffled_min": lo, "shuffled_max": hi,
                                "shuffled_median": med,
                                "fraction_shuffled_le_observed": frac_le},
            "eta_meas": str(ETA_MEAS), "eta_fine": str(ETA_FINE)}


def main():
    t0 = time.time()
    rows = part1()
    part1_controls()
    payload, units, evaluable, acct, audit, sig, rng, results = part3()
    dec = part4(units, evaluable, sig, results)
    report = {
        "protocol": "N5_resolution_minimax_v1",
        "statement": ("E*_eta = (1/2) max over pairs with ||R(a)-R(b)||_{w,inf} "
                      "<= 2 eta of |g(a)-g(b)|; eta_crit(eps) = (1/2) min over "
                      "pairs with |g(a)-g(b)| > 2 eps of ||R(a)-R(b)||_{w,inf}"),
        "nearest_prior": ("Donoho, optimal recovery / modulus of continuity; the "
                          "eta=0 case is CIGAMF.P13.QueryScalarMinimax.minimax_radius "
                          "in work/p13_conjectures/LeanQueryScalarMinimaxV1.lean "
                          "(no compile receipt exists for that module)"),
        "panel_artifact": str(PANEL.relative_to(ROOT)),
        "panel_script_sha256": payload["script_sha256"],
        "accounting": acct,
        "confound_filter_audit": audit,
        "declared_accuracies": {f"{b}[{d}]": str(v) for (b, d), v in sorted(sig.items(), key=str)},
        "observed_ranges": {f"{b}[{d}]": float(v) for (b, d), v in sorted(rng.items(), key=str)},
        "synthetic_identity_cells": rows,
        "results": results,
        "decision_inputs": dec,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=1, default=str) + "\n")
    print(f"\nwrote {OUT}")
    print(f"elapsed {time.time()-t0:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
