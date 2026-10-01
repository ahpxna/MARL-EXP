#!/usr/bin/env python3
"""Combinatorial obstruction diagnostic with ASSIGNED pairwise order indices.

The span vectors are constructed directly, not derived from the same world F
that generates a Gaussian-mixture query law. r_of is a predicted order, not an
observation-law computation: moment vanishing alone does not prove attainment.
Safe sets use the additive omitted-span formula. The Lean module proves abstract
safe-set combinatorics and a floor for a COMMON action distribution, not transcript
indistinguishability or sample complexity for this construction.

Any h^(-2r) values below are illustrative unit-constant exponent proxies, not sample
counts, algorithm outputs, or verified ratios of optimal statistical complexities.
"""

import json
import math
import sys
from itertools import combinations

import numpy as np

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def ceil_div(a, b):
    return -(-a // b)


def build_worlds(n, m, seed=11):
    """Worlds are subsets of [n]; each determines a component-span vector.

    The structure that makes this interesting is deliberate and is the scientific
    claim under test, not a fitted convenience: WHICH compression is right depends
    only on a coarse feature of the world -- whether the leaking set is small, and
    if so where it starts -- while the world's full IDENTITY involves its entire
    high-degree structure.  Worlds with a large leaking set all steer the
    compression the same way, so they never obstruct each other, yet telling them
    apart still requires resolving their top-order characters."""
    base = np.array([1.0 + 0.10 * i for i in range(m)])
    worlds = []
    for r in range(1, n + 1):
        for S in combinations(range(n), r):
            boost = (min(S) % m) if len(S) <= 2 else 0
            theta = base.copy()
            theta[boost] += 0.55
            worlds.append({"S": frozenset(S), "card": len(S), "theta": theta,
                           "boost": boost})
    return worlds


def safe_set(theta, eps):
    top = float(theta.max())
    return frozenset(i for i in range(len(theta)) if theta[i] >= top - 2 * eps - 1e-12)


def r_of(wF, wG, d):
    """Assigned order index; not certified from a common observation model."""
    return ceil_div(min(wF["card"], wG["card"]), d)


def has_common(idxs, safes):
    if not idxs:
        return True  # The action universe in this diagnostic is nonempty.
    inter = set(safes[idxs[0]])
    for i in idxs[1:]:
        inter &= safes[i]
    return len(inter) > 0


def minimal_obstructions(worlds, safes, max_size=3):
    """Enumerate obstructions minimal under inclusion, up to `max_size`."""
    N = len(worlds)
    obs = []
    for size in range(1, max_size + 1):
        for comb in combinations(range(N), size):
            if has_common(list(comb), safes):
                continue
            # minimal: every proper subset has a common answer
            minimal = True
            for drop in range(size):
                sub = [comb[k] for k in range(size) if k != drop]
                if len(sub) >= 1 and not has_common(sub, safes):
                    minimal = False
                    break
            if minimal:
                obs.append(comb)
    return obs


def main():
    print("=" * 78)
    print("Obstruction order: the cost of deciding against the cost of identifying")
    print("=" * 78)

    n, m, eps = 6, 4, 0.20
    degrees = [(1, "d=1"), (2, "d=2"), (3, "d=3")]
    worlds = build_worlds(n, m)
    safes = [safe_set(w["theta"], eps) for w in worlds]
    print(f"\n  {len(worlds)} worlds on n={n} latent bits, m={m} coordinates, eps={eps}")
    sizes = sorted({len(s) for s in safes})
    print(f"  safe-set sizes present: {sizes}")
    check("safe sets are non-empty (the best answer is always safe)",
          all(len(s) >= 1 for s in safes))
    check("safe sets genuinely overlap across worlds, so deciding is easier than identifying",
          any(len(set(safes[i]) & set(safes[j])) > 0
              for i in range(len(worlds)) for j in range(i + 1, len(worlds))
              if safes[i] != safes[j]))

    # --- obstructions
    # With m actions, every minimal obstruction has at most m worlds:
    # choose, for each action, one world excluding it. Do not silently stop at 3.
    obs = minimal_obstructions(worlds, safes, max_size=m)
    print(f"\n  minimal obstructions found (exhaustive up to m={m}): {len(obs)}")
    check("there is at least one obstruction (the task is not free)", len(obs) > 0)

    # upward closure: a superset of an obstruction is an obstruction
    rng = np.random.default_rng(5)
    up_ok = True
    for comb in obs[:40]:
        extra = int(rng.integers(0, len(worlds)))
        bigger = tuple(sorted(set(comb) | {extra}))
        if has_common(list(bigger), safes):
            up_ok = False
    check("obstructions are upward closed  [Lean: isObstruction_mono]", up_ok)

    # --- the two orders
    def min_over_queries(f, g):
        return min(r_of(worlds[f], worlds[g], d) for d, _ in degrees)

    r_safe = 0
    worst_H = None
    for comb in obs:
        inner = min(min_over_queries(f, g) for f, g in combinations(comb, 2))
        if inner > r_safe:
            r_safe, worst_H = inner, comb

    # identification must separate every pair of DISTINCT worlds, including those
    # whose decisions happen to agree -- that is exactly the work deciding avoids.
    r_id = 0
    for f, g in combinations(range(len(worlds)), 2):
        r_id = max(r_id, min_over_queries(f, g))

    print(f"\n  r_safe = {r_safe}   (worst obstruction: worlds "
          f"{[sorted(worlds[i]['S']) for i in worst_H]})")
    print(f"  r_id   = {r_id}")
    check("deciding needs a strictly lower order than identifying", r_safe < r_id,
          f"r_safe={r_safe} < r_id={r_id}")

    # --- classes_resolve_iff, transcribed
    def classes_at(r):
        """Worlds a learner cannot split at order r: those whose pairwise
        separation order EXCEEDS r are in the same class."""
        N = len(worlds)
        parent = list(range(N))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for f, g in combinations(range(N), 2):
            if min_over_queries(f, g) > r:
                a, b = find(f), find(g)
                if a != b:
                    parent[a] = b
        groups = {}
        for i in range(N):
            groups.setdefault(find(i), []).append(i)
        result = list(groups.values())
        # A connected component need not be a coefficient-equality class.
        # Refuse inconsistent assigned orders rather than merge by transitive closure.
        for group in result:
            for f, g in combinations(group, 2):
                if min_over_queries(f, g) <= r:
                    raise ValueError("Assigned indistinguishability is not transitive")
        return result

    at_r = all(has_common(cl, safes) for cl in classes_at(r_safe))
    at_rm1 = all(has_common(cl, safes) for cl in classes_at(r_safe - 1))
    print(f"\n  every class has a common safe answer at r={r_safe}: {at_r}")
    print(f"  every class has a common safe answer at r={r_safe-1}: {at_rm1}")
    check("classes resolve at r_safe but not below  [Lean: classes_resolve_iff]",
          at_r and not at_rm1)

    # --- the error floor, transcribed
    floor_ok = True
    worst_floor = None
    for comb in obs[:60]:
        H = list(comb)
        for _ in range(30):
            p = rng.random(m)
            p = p / p.sum()
            masses = [sum(p[a] for a in range(m) if a not in safes[F]) for F in H]
            if max(masses) < 1.0 / len(H) - 1e-9:
                floor_ok = False
            if worst_floor is None or max(masses) < worst_floor:
                worst_floor = max(masses)
    check("every randomized rule leaves unsafe mass >= 1/|H| somewhere in the obstruction"
          "  [Lean: obstruction_error_floor_randomized]", floor_ok,
          f"smallest observed worst-case mass {worst_floor:.4f}")

    # --- the cost consequence
    print("\n  illustrative exponent proxies at h (not sample counts)")
    print("  " + "-" * 72)
    rows = []
    for h in [0.3, 0.2, 0.1, 0.05, 0.02]:
        c_dec = h ** (-2 * r_safe)
        c_id = h ** (-2 * r_id)
        rows.append({"h": h, "cost_decide": c_dec, "cost_identify": c_id,
                     "ratio": c_id / c_dec})
        print(f"      h={h:5.3f}:  decide ~ {c_dec:12.1f}   identify ~ {c_id:16.1f}"
              f"   ratio {c_id/c_dec:12.1f}")
    check("the identification penalty diverges as h shrinks",
          rows[-1]["ratio"] > rows[0]["ratio"])

    # --- the degenerate case that must be excluded
    big_eps_safes = [safe_set(w["theta"], 1.0) for w in worlds]
    globally_common = has_common(list(range(len(worlds))), big_eps_safes)
    check("at a large enough eps there are no obstructions and the decision is free"
          "  [Lean: no_obstruction_iff_global_answer]", globally_common)

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_unified_obstruction_order.py").read_bytes()).hexdigest(),"evidence_class": "COMBINATORIAL_ASSIGNED_ORDER_DIAGNOSTIC",
           "same_world_loss_observation_join": False,
           "sample_complexity_proved": False,
           "cost_rows_meaning": "unit_constant_exponent_proxies_only",
           "obstruction_search_max_size": m, "n": n, "m": m, "eps": eps, "n_worlds": len(worlds),
           "n_minimal_obstructions": len(obs),
           "r_safe": r_safe, "r_id": r_id, "cost": rows, "checks": CHECKS,
           "all_passed": nfail == 0}
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    with open("research/unified_20260919/obstruction_order_corrected_v2.json", "w") as f:
        json.dump(out, f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
