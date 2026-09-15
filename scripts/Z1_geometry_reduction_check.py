#!/usr/bin/env python3
"""Z1 / PACKAGE 0 -- is the multi-tip support geometry more than a re-encoding of
a general finite decision-region problem?

This probe compares, on explicit small instances and with EXACT arithmetic, the
zero-error worst-case adaptive query cost of

  (A) an abstract finite decision-region problem  (worlds x decisions x binary
      tests, both tables arbitrary), and
  (B) the multi-tip support geometry instance obtained by the encoding
          W_theta = { d : d unsafe at theta } u { nD + e : test e answers 1 },
      with the PHYSICAL membership query `j in W` and safety `selectedRadius
      (components W) {j} = 0`, where selectedRadius is recomputed from its
      DEFINITION (max - min of the complement-sum over the actual support points,
      exact Fractions), never from the closed form.

CHECKS (every one raises AssertionError / RuntimeError on mismatch):

  Z0  selectedRadius computed from the definition equals ((m-1)/2)*[j in W] for
      every W and j on all m <= 6  (validates `radius_formula` numerically).
  Z1  safety faithfulness: radius(encode(P,theta), castAdd d) == 0  <=>  d safe.
  Z2  query faithfulness:  membership at coordinate nD+e  ==  test bit e.
  Z3  COST PRESERVATION: opt depth of the abstract problem == opt depth of the
      encoded geometry over RESTRICTED trees (query only test coordinates, output
      only decision coordinates), on an exhaustive sweep of small tables plus
      randomised tables.  Both computed by independent version-space DPs.
  Z4  the DECISION restriction is necessary: an instance where the unrestricted
      encoded geometry costs strictly less (0 vs 1).
  Z5  the QUERY restriction is necessary: an instance with NO feasible abstract
      strategy at all, whose unrestricted encoded geometry costs 1.
  Z6  unrestricted-geometry exact law: for the promise |W| <= s the optimal
      zero-error adaptive membership cost is exactly s (matches
      CardinalityQueryLaw.adaptive_cardinality_lower / _attained).
  Z7  the counting bound |family| <= 2^depth for pairwise-incompatible families,
      and the exponential GAP: the dense family costs m-1 in the m-coordinate
      geometry but ceil(log2 m) once ceil(log2 m) auxiliary bit-test coordinates
      are added -- i.e. the cost is a property of the QUERY SET, not of the
      decision problem.

WHAT THIS DOES NOT ESTABLISH.  Numerical evidence on the enumerated instances
only.  Nothing here is a proof; the proofs are in
work/p13_conjectures/LeanSupportGeometryReductionV1.lean.  Zero-error worst-case
DETERMINISTIC depth only: no prior, no expected cost, no randomised trees, no
noise, no approximation ratios.  Tests are binary and noiseless.  The sweeps are
exhaustive only in the stated ranges; every skipped configuration is listed in
the emitted artifact under "scope".
"""
from __future__ import annotations

import itertools
import json
import os
import random
import sys
from fractions import Fraction as F

PROTOCOL_VERSION = "z1_geometry_reduction_check_v1"
INF = None  # infeasible


# --------------------------------------------------------------- the geometry

def tip(m: int, w: int) -> tuple:
    """tip w j = 1 - (m-1) if j == w else 1  (LeanSupportUnboundedObstructionV1)."""
    return tuple(F(1) - (F(m - 1) if j == w else F(0)) for j in range(m))


def support_points(m: int, W: frozenset) -> list:
    """Points W = Option {w // w in W}: the anchor 0 and one tip per present w."""
    pts = [tuple(F(0) for _ in range(m))]
    pts.extend(tip(m, w) for w in sorted(W))
    return pts


def selected_radius(m: int, W: frozenset, j: int) -> F:
    """selectedRadius (components W) {j} straight from the definition:
    (max - min) / 2 of  x |-> sum_{i != j} x_i  over the actual support points."""
    vals = [sum((p[i] for i in range(m) if i != j), F(0)) for p in support_points(m, W)]
    return (max(vals) - min(vals)) / 2


def membership_query(m: int, W: frozenset, a: int) -> bool:
    """The physical membership query: is the point `tip a` in the actual support?"""
    return tip(m, a) in set(support_points(m, W))


# ------------------------------------------------------- abstract DR problems

class DR:
    """nW worlds, nD decisions, nE binary tests; both tables arbitrary."""

    def __init__(self, nW, nD, nE, unsafe, test):
        self.nW, self.nD, self.nE = nW, nD, nE
        self.unsafe = unsafe          # unsafe[theta][d] : bool
        self.test = test              # test[theta][e]   : bool
        assert len(unsafe) == nW and all(len(r) == nD for r in unsafe)
        assert len(test) == nW and all(len(r) == nE for r in test)


def opt_depth(worlds, nD, nE, unsafe_fn, test_fn, _memo=None):
    """Zero-error worst-case adaptive depth by version-space DP.

    `worlds` is a frozenset of world indices; returns an int, or None when no
    correct strategy exists at any depth.  A test that does not split the version
    space can never help, so it is skipped; if nothing splits and no decision is
    safe in the whole version space, the state is infeasible.
    """
    if _memo is None:
        _memo = {}
    if worlds in _memo:
        v = _memo[worlds]
        if v == "PENDING":
            raise RuntimeError("cyclic version-space recursion -- DP is wrong")
        return v
    _memo[worlds] = "PENDING"
    if any(all(not unsafe_fn(th, d) for th in worlds) for d in range(nD)):
        _memo[worlds] = 0
        return 0
    best = None
    for e in range(nE):
        yes = frozenset(th for th in worlds if test_fn(th, e))
        no = worlds - yes
        if not yes or not no:
            continue
        a = opt_depth(yes, nD, nE, unsafe_fn, test_fn, _memo)
        b = opt_depth(no, nD, nE, unsafe_fn, test_fn, _memo)
        if a is None or b is None:
            continue
        c = max(a, b) + 1
        if best is None or c < best:
            best = c
    _memo[worlds] = best
    return best


def abstract_cost(P: DR):
    return opt_depth(frozenset(range(P.nW)), P.nD, P.nE,
                     lambda th, d: P.unsafe[th][d], lambda th, e: P.test[th][e])


# ------------------------------------------------------------- the encoding

def encode(P: DR) -> list:
    """W_theta subset of Fin(nD+nE)."""
    out = []
    for th in range(P.nW):
        W = set(d for d in range(P.nD) if P.unsafe[th][d])
        W |= set(P.nD + e for e in range(P.nE) if P.test[th][e])
        out.append(frozenset(W))
    return out


def geometry_cost(m, worlds, decision_coords, query_coords):
    """Cost of the geometry instance with the given ALLOWED decision/query sets.

    Safety of decision coordinate j in world theta is `selectedRadius == 0`,
    recomputed from the definition; the query at a is the physical membership
    query, also recomputed from the actual support.
    """
    dc = list(decision_coords)
    qc = list(query_coords)
    safe = [[selected_radius(m, W, j) == 0 for j in dc] for W in worlds]
    ans = [[membership_query(m, W, a) for a in qc] for W in worlds]
    return opt_depth(frozenset(range(len(worlds))), len(dc), len(qc),
                     lambda th, d: not safe[th][d], lambda th, e: ans[th][e])


# ------------------------------------------------------------------- checks

def check_Z0(report):
    n = 0
    for m in range(2, 7):
        for r in range(0, m + 1):
            for W in itertools.combinations(range(m), r):
                Wf = frozenset(W)
                for j in range(m):
                    got = selected_radius(m, Wf, j)
                    want = F(m - 1, 2) if j in Wf else F(0)
                    if got != want:
                        raise AssertionError(
                            f"Z0 radius mismatch m={m} W={sorted(Wf)} j={j} "
                            f"got={got} want={want}")
                    if membership_query(m, Wf, j) != (j in Wf):
                        raise AssertionError(f"Z0 membership mismatch m={m} j={j}")
                    n += 1
    report["Z0_radius_and_membership_checks"] = n
    report["Z0_note"] = ("selectedRadius from the DEFINITION equals ((m-1)/2)*[j in W] "
                         "and physical membership equals set membership, m=2..6, all W")


def sweep_problems(nW, nD, nE, exhaustive_limit=4096, rng=None, samples=200):
    """All (or a random sample of) unsafe/test tables for the given shape."""
    total = (2 ** (nW * nD)) * (2 ** (nW * nE))
    if total <= exhaustive_limit:
        for ubits in range(2 ** (nW * nD)):
            unsafe = [[bool((ubits >> (th * nD + d)) & 1) for d in range(nD)]
                      for th in range(nW)]
            for tbits in range(2 ** (nW * nE)):
                test = [[bool((tbits >> (th * nE + e)) & 1) for e in range(nE)]
                        for th in range(nW)]
                yield DR(nW, nD, nE, unsafe, test), True
    else:
        for _ in range(samples):
            unsafe = [[rng.random() < 0.5 for _ in range(nD)] for _ in range(nW)]
            test = [[rng.random() < 0.5 for _ in range(nE)] for _ in range(nW)]
            yield DR(nW, nD, nE, unsafe, test), False


def check_Z1_Z2_Z3(report):
    rng = random.Random(20260913)
    shapes = [(2, 2, 1), (2, 2, 2), (3, 2, 2), (3, 3, 2), (2, 3, 3), (4, 3, 2), (3, 3, 3)]
    n_inst = 0
    n_exh = 0
    n_feasible = 0
    n_infeasible = 0
    for (nW, nD, nE) in shapes:
        for P, exhaustive in sweep_problems(nW, nD, nE, rng=rng):
            m = nD + nE
            if m < 2:
                continue
            worlds = encode(P)
            # Z1 safety faithfulness
            for th in range(nW):
                for d in range(nD):
                    got = (selected_radius(m, worlds[th], d) == 0)
                    want = (not P.unsafe[th][d])
                    if got != want:
                        raise AssertionError(f"Z1 safety mismatch shape={(nW,nD,nE)} "
                                             f"theta={th} d={d}")
                # Z2 query faithfulness
                for e in range(nE):
                    got = membership_query(m, worlds[th], nD + e)
                    if got != P.test[th][e]:
                        raise AssertionError(f"Z2 query mismatch shape={(nW,nD,nE)} "
                                             f"theta={th} e={e}")
            # Z3 cost preservation
            ca = abstract_cost(P)
            cg = geometry_cost(m, worlds, range(nD), range(nD, nD + nE))
            if ca != cg:
                raise AssertionError(
                    f"Z3 COST NOT PRESERVED shape={(nW,nD,nE)} abstract={ca} "
                    f"restricted-geometry={cg} unsafe={P.unsafe} test={P.test}")
            # the unrestricted geometry can only be cheaper, never dearer
            cu = geometry_cost(m, worlds, range(m), range(m))
            if cu is None and ca is not None:
                raise AssertionError("Z3 unrestricted geometry infeasible while "
                                     "abstract feasible -- impossible")
            if ca is not None and cu is not None and cu > ca:
                raise AssertionError(
                    f"Z3 unrestricted geometry dearer than abstract: {cu} > {ca}")
            n_inst += 1
            n_exh += int(exhaustive)
            if ca is None:
                n_infeasible += 1
            else:
                n_feasible += 1
    report["Z1_Z2_Z3_instances"] = n_inst
    report["Z1_Z2_Z3_exhaustive_instances"] = n_exh
    report["Z3_feasible_instances"] = n_feasible
    report["Z3_infeasible_instances"] = n_infeasible
    report["Z3_shapes"] = [list(s) for s in shapes]
    report["Z3_verdict"] = ("abstract cost == restricted-geometry cost on EVERY "
                            "instance checked (including the infeasible ones, where "
                            "both are None)")


def check_Z4(report):
    """badDecision: 2 worlds, 2 decisions, test 0 informative, test 1 constant 0."""
    unsafe = [[True, False], [False, True]]
    test = [[False, False], [True, False]]
    P = DR(2, 2, 2, unsafe, test)
    m = 4
    worlds = encode(P)
    ca = abstract_cost(P)
    cr = geometry_cost(m, worlds, range(2), range(2, 4))
    cu = geometry_cost(m, worlds, range(m), range(m))
    if ca != 1:
        raise AssertionError(f"Z4 abstract cost expected 1, got {ca}")
    if cr != 1:
        raise AssertionError(f"Z4 restricted-geometry cost expected 1, got {cr}")
    if cu != 0:
        raise AssertionError(f"Z4 unrestricted-geometry cost expected 0, got {cu}")
    # the witness: coordinate nD+1 is absent from every encoded world
    for th in range(2):
        if selected_radius(m, worlds[th], 3) != 0:
            raise AssertionError("Z4 auxiliary coordinate 3 is not safe everywhere")
    report["Z4_abstract_cost"] = ca
    report["Z4_restricted_geometry_cost"] = cr
    report["Z4_unrestricted_geometry_cost"] = cu
    report["Z4_verdict"] = ("dropping the ALLOWED-DECISION restriction breaks cost "
                            "preservation: 1 -> 0 by selecting the auxiliary "
                            "coordinate of a constantly-0 test")


def check_Z5(report):
    """noTest: 2 worlds, 2 decisions, NO tests."""
    unsafe = [[True, False], [False, True]]
    test = [[], []]
    P = DR(2, 2, 0, unsafe, test)
    m = 2
    worlds = encode(P)
    ca = abstract_cost(P)
    cr = geometry_cost(m, worlds, range(2), [])
    cu = geometry_cost(m, worlds, range(m), range(m))
    if ca is not None:
        raise AssertionError(f"Z5 abstract problem should be infeasible, got {ca}")
    if cr is not None:
        raise AssertionError(f"Z5 restricted geometry should be infeasible, got {cr}")
    if cu != 1:
        raise AssertionError(f"Z5 unrestricted-geometry cost expected 1, got {cu}")
    report["Z5_abstract_cost"] = "INFEASIBLE"
    report["Z5_restricted_geometry_cost"] = "INFEASIBLE"
    report["Z5_unrestricted_geometry_cost"] = cu
    report["Z5_verdict"] = ("dropping the ALLOWED-QUERY restriction breaks cost "
                            "preservation: an unsolvable problem becomes solvable in "
                            "1 query, because querying a DECISION coordinate is a "
                            "direct safety oracle")


def check_Z6(report):
    """Unrestricted geometry, promise |W| <= s: the exact cost is s."""
    rows = []
    for m in range(2, 7):
        for s in range(0, m):
            worlds = [frozenset(c) for r in range(0, s + 1)
                      for c in itertools.combinations(range(m), r)]
            c = geometry_cost(m, worlds, range(m), range(m))
            if c != s:
                raise AssertionError(
                    f"Z6 exact-cost law violated m={m} s={s}: got {c}, expected {s}")
            rows.append({"m": m, "s": s, "cost": c})
    report["Z6_rows"] = rows
    report["Z6_verdict"] = ("cost == s for the promise |W| <= s on every m=2..6, "
                            "s=0..m-1; matches adaptive_cardinality_lower/_attained")


def check_Z7(report):
    rows = []
    for m in range(2, 8):
        dense = [frozenset(set(range(m)) - {w}) for w in range(m)]
        # pairwise incompatible
        for i in range(m):
            for j in range(i + 1, m):
                if dense[i] | dense[j] != frozenset(range(m)):
                    raise AssertionError("Z7 dense family is not pairwise incompatible")
        c_geom = geometry_cost(m, dense, range(m), range(m))
        if c_geom != m - 1:
            raise AssertionError(f"Z7 dense geometry cost expected {m-1}, got {c_geom}")
        if len(dense) > 2 ** c_geom:
            raise AssertionError("Z7 counting bound |family| <= 2^depth violated")
        # same decision problem, but with ceil(log2 m) BIT tests added as auxiliary
        nbits = max(1, (m - 1).bit_length())
        unsafe = [[not (d == w) for d in range(m)] for w in range(m)]
        test = [[bool((w >> k) & 1) for k in range(nbits)] for w in range(m)]
        P = DR(m, m, nbits, unsafe, test)
        ca = abstract_cost(P)
        worlds = encode(P)
        cr = geometry_cost(m + nbits, worlds, range(m), range(m, m + nbits))
        if ca != cr:
            raise AssertionError(f"Z7 cost preservation failed m={m}: {ca} vs {cr}")
        if ca != nbits:
            raise AssertionError(f"Z7 bit-test cost expected {nbits}, got {ca}")
        if m >= 4 and not (cr < c_geom):
            raise AssertionError("Z7 expected a strict gap once m >= 4")
        rows.append({"m": m, "dense_cost_on_m_coords": c_geom,
                     "ceil_log2_m": nbits,
                     "cost_with_bit_test_coordinates": cr,
                     "counting_bound_2_pow_depth": 2 ** c_geom,
                     "family_size": len(dense)})
    report["Z7_rows"] = rows
    report["Z7_verdict"] = ("the SAME decision problem costs m-1 with the m physical "
                            "membership coordinates and ceil(log2 m) once bit-test "
                            "coordinates are added: the cost is a property of the "
                            "allowed QUERY SET, not of the geometry")


def main():
    out_dir = "/Users/phanan/cig-amf-main/research/worker_geometry_reduction_20260913"
    os.makedirs(out_dir, exist_ok=True)
    report = {"protocol_version": PROTOCOL_VERSION}
    check_Z0(report)
    check_Z1_Z2_Z3(report)
    check_Z4(report)
    check_Z5(report)
    check_Z6(report)
    check_Z7(report)
    report["scope"] = {
        "exact_arithmetic": "fractions.Fraction throughout; selectedRadius recomputed "
                            "from its definition on the actual support points",
        "Z0_range": "m = 2..6, all 2^m worlds, all coordinates",
        "Z3_shapes_exhaustive": "(2,2,1),(2,2,2),(3,2,2) tables enumerated exhaustively; "
                                "(3,3,2),(2,3,3),(4,3,2),(3,3,3) sampled at 200 random "
                                "tables each with seed 20260913",
        "Z6_range": "m = 2..6, s = 0..m-1",
        "Z7_range": "m = 2..7",
        "SKIPPED": ["randomised strategies (deterministic trees only)",
                    "priors / expected cost (worst case only)",
                    "noisy or many-valued tests",
                    "m > 7 for the dense-family gap (the geometry DP is exponential "
                    "in the number of worlds)"],
    }
    report["verdict"] = (
        "THE REDUCTION HOLDS and is exactly cost-preserving, but ONLY when both the "
        "allowed decision set and the allowed query set are restricted to disjoint "
        "coordinate blocks (Z3). Both restrictions are individually necessary (Z4, "
        "Z5). Without them the geometry is STRICTLY EASIER than the general "
        "decision-region problem, with a fully known exact cost s for the promise "
        "|W| <= s (Z6).")
    path = os.path.join(out_dir, "Z1_geometry_reduction_check.json")
    with open(path, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("Z6_rows", "Z7_rows")}, indent=2, sort_keys=True))
    print("artifact:", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
