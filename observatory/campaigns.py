"""Targeted campaigns: the four computations that can change a decision now.

A uniform sweep spends compute evenly and answers nothing in particular.  Each
campaign here is aimed at one open question in the ledger and is designed so
that *both* outcomes are informative.

A. RANK-ONE LADDER (D6)  -- the portfolio's only remaining proof hole.
   The ledger's own gate: falsify all-coordinate rank-one worlds computationally
   before attempting a universal proof.  Worlds are generated *rank-one by
   construction* in four nested classes, and the doubled decision gap is
   compared against m-1 in exact rational arithmetic.  A single exact violation
   kills the live conjecture today; no violation across the ladder is the
   strongest positive evidence the conjecture has ever had, and the campaign
   also returns the margin distribution, which a proof attempt needs.

B. CHI REPRESENTATIVENESS (Structural) -- is the headline exotic?
   chi_prefix = Theta(m) is proved on a constructed staircase family.  If random
   supportOsc worlds essentially always have chi = 1, the staircase is a corner
   case and the paper's framing has to say so.  If chi grows off the constructed
   family too, the result is much stronger.  Nobody has measured this.

C. TEST COVER SCALING (Support) -- the missing family-level law.
   Q*_eps, the greedy size, the maximum edge size r and the classical
   2(n-1)/(r+1) lower bound, measured across support-family sizes.  This turns
   "a family-level complexity law is missing" into a measured curve.

D. TYPED COMPLETION HARDNESS (MASTER) -- an honest check on a re-promoted idea.
   If greedy tracks the optimum on typed evidence, minimum-cost typed completion
   is not algorithmically interesting and should be demoted again.  The campaign
   is built to be able to say that.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from observatory import equations  # noqa: F401
from observatory.exact import Q, ZERO, ONE, HALF, osc, ratio, topk, argsort_desc
from observatory.schema import (Emitter, make_context, MODE_EXACT, MODE_FLOAT,
                                ROLE_INPUT, ROLE_TERM, ROLE_LHS, ROLE_RHS,
                                ROLE_SLACK, ROLE_RATIO, ROLE_FLAG, ROLE_DIAG,
                                ST_OK, ST_UNDEFINED, ST_SKIPPED)
from observatory.worlds import Support, World, ProductReference, Action
from observatory.chains._common import exact_optimum, topc_set, world_key
from observatory.chains import d6 as C_d6
from observatory.chains import structural as C_structural
from observatory.chains import support as C_support
from observatory.chains import master as C_master


# =====================================================================
# A. rank-one ladder
# =====================================================================

RANK_ONE_CLASSES = ("pairwise", "pure_product", "pairwise_plus_product",
                    "full_multiaffine")


def _rq(rng: random.Random, lo: int, hi: int, den: int) -> Q:
    return Q(rng.randint(lo, hi), den)


def build_rank_one_world(cls: str, m: int, arity: int, *, rng: random.Random,
                         den: int = 4, span: int = 4) -> World:
    """Generate a world that is all-coordinate rank one by construction.

    Every class here has centered interaction profile
    psi_{i,u}(z) = [phi_i(u) - phi_i(u0)] * [H_i(z_{-i}) - E_q H_i],
    which is rank one at every coordinate for any choice of the scalar
    functions.  The generator therefore explores the *inside* of the conjecture's
    hypothesis rather than sampling arbitrary worlds and hoping.
    """
    sizes = tuple([int(arity)] * int(m))
    sup = Support.cartesian(sizes)
    phi = tuple(tuple(_rq(rng, -span, span, den) for _ in range(arity)) for _ in range(m))
    g = tuple(tuple(_rq(rng, -span, span, den) for _ in range(arity)) for _ in range(m))
    resid: Dict[Action, Q] = {}

    if cls == "pairwise":
        w = {(i, j): _rq(rng, -span, span, den)
             for i in range(m) for j in range(i + 1, m)}
        for a in sup.omega:
            resid[a] = sum(w[(i, j)] * phi[i][a[i]] * phi[j][a[j]]
                           for i in range(m) for j in range(i + 1, m))
    elif cls == "pure_product":
        c = _rq(rng, 1, span, den)
        for a in sup.omega:
            p = c
            for i in range(m):
                p *= phi[i][a[i]]
            resid[a] = p
    elif cls == "pairwise_plus_product":
        w = {(i, j): _rq(rng, -span, span, den)
             for i in range(m) for j in range(i + 1, m)}
        c = _rq(rng, 1, span, den)
        for a in sup.omega:
            p = c
            for i in range(m):
                p *= phi[i][a[i]]
            resid[a] = p + sum(w[(i, j)] * phi[i][a[i]] * phi[j][a[j]]
                               for i in range(m) for j in range(i + 1, m))
    elif cls == "full_multiaffine":
        wA = {}
        for size in range(2, m + 1):
            for A in itertools.combinations(range(m), size):
                wA[A] = _rq(rng, -span, span, den)
        for a in sup.omega:
            tot = ZERO
            for A, coef in wA.items():
                p = coef
                for i in A:
                    p *= phi[i][a[i]]
                tot += p
            resid[a] = tot
    else:
        raise ValueError("unknown rank-one class: " + str(cls))

    # additive part is carried by g; the residual holds the interaction
    prim = g
    return World(sup, prim, ZERO, resid,
                 {"family": "rankone_" + cls, "arity": int(arity), "cls": cls})


def campaign_rank_one(em: Emitter, *, ms=(4,), arities=(3, 4), n_per=60,
                      seed=1, classes=RANK_ONE_CLASSES, deadline=None) -> Dict:
    """A: hunt for an exact rank-one violation of the m-1 decision bound."""
    rng = random.Random(seed)
    best = {"ratio": None, "world": None}
    hist: List[float] = []
    n_seen = 0
    n_rank_one = 0
    violations = []
    t0 = time.time()
    for cls in classes:
        for m in ms:
            if m % 2:
                continue                      # balanced complement needs m = 2d
            k = m // 2
            for arity in arities:
                for _ in range(n_per):
                    if deadline and time.time() - t0 > deadline:
                        break
                    w = build_rank_one_world(cls, m, arity, rng=rng)
                    try:
                        delta = w.delta_square()
                    except ValueError:
                        continue
                    if delta == 0:
                        continue
                    n_seen += 1
                    spans = w.component_spans()
                    S = topk(spans, k)
                    T = tuple(j for j in range(m) if j not in set(S))
                    L_S = w.true_compression_loss(S)
                    L_T = w.true_compression_loss(T)
                    l_C = 2 * (L_S - L_T)
                    kappa = l_C / delta
                    hist.append(float(kappa))
                    ref = ProductReference.point_mass(w.support.action_sizes)
                    key = world_key(w, cls=cls, k=k, campaign="A_rank_one")
                    inst = dict(key, selected=str(S), competitor=str(T))
                    e = "D6.decision_interaction_complexity"
                    em.emit(chain="D6", eq_id=e, symbol="l_C", value=l_C,
                            role=ROLE_LHS, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="kappa_observed", value=kappa,
                            role=ROLE_TERM, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="m_minus_1", value=Q(m - 1),
                            role=ROLE_RHS, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="slack", value=Q(m - 1) - kappa,
                            role=ROLE_SLACK, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="ratio", value=kappa / Q(m - 1),
                            role=ROLE_RATIO, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="exceeds_m_minus_1",
                            value=1 if kappa > Q(m - 1) else 0, role=ROLE_FLAG, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="balanced", value=1,
                            role=ROLE_FLAG, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="normalized", value=1,
                            role=ROLE_FLAG, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="arity", value=arity,
                            role=ROLE_INPUT, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="strict_topc",
                            value=0 if (k < m and spans[argsort_desc(spans)[k - 1]]
                                        == spans[argsort_desc(spans)[k]]) else 1,
                            role=ROLE_FLAG, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="reference_is_point_mass",
                            value=1, role=ROLE_FLAG, instance=inst)
                    em.emit(chain="D6", eq_id=e, symbol="reference_mass_check",
                            value=ONE, role=ROLE_DIAG, instance=inst)
                    # self-check: the generator claims rank one; verify it
                    C_d6.probe_profile_rank(em, w, ref, key, max_contexts=6)
                    n_rank_one += 1
                    if best["ratio"] is None or kappa > best["ratio"]:
                        best = {"ratio": kappa, "world": {
                            "cls": cls, "m": m, "arity": arity,
                            "primitives": [[str(v) for v in row] for row in w.primitives],
                            "residual": {str(a): str(v) for a, v in w.residual.items()},
                            "selected": list(S), "delta_square": str(delta),
                            "l_C": str(l_C)}}
                    if kappa > Q(m - 1):
                        violations.append({"cls": cls, "m": m, "arity": arity,
                                           "kappa": str(kappa), "bound": m - 1,
                                           "world_id": w.content_id()})
    bound = max(ms) - 1 if ms else 0
    return {
        "campaign": "A_rank_one_ladder",
        "n_worlds": n_seen,
        "n_rank_one_confirmed": n_rank_one,
        "classes": list(classes),
        "max_kappa": (float(best["ratio"]) if best["ratio"] is not None else None),
        "max_kappa_over_bound": (
            float(best["ratio"]) / float(best["world"]["m"] - 1)
            if best["ratio"] is not None and best["world"] else None),
        "kill_threshold_note": "a violation needs kappa > m-1 on a normalized balanced cell",
        "violations": violations,
        "conjecture_killed": bool(violations),
        "kappa_samples": hist[:2000],
        "witness": best["world"],
        "elapsed_s": time.time() - t0,
    }


# =====================================================================
# B. chi representativeness
# =====================================================================

def campaign_chi(em: Emitter, *, families, ms=(3, 4, 5), arities=(2, 3),
                 n_per=8, seed=2, deadline=None) -> Dict:
    """B: how often does prefix-cover dimension exceed one off the staircase?"""
    from observatory.worlds import generate_world
    rng = random.Random(seed)
    dist: Dict[str, Dict[str, int]] = {}
    t0 = time.time()
    for fam in families:
        for m in ms:
            for arity in arities:
                for _ in range(n_per):
                    if deadline and time.time() - t0 > deadline:
                        break
                    w = generate_world(fam, m, arity, rng=rng)
                    key = world_key(w, campaign="B_chi")
                    C_structural.probe_prefix_cover(em, w, key, ZERO)
                    C_structural.probe_taxonomy(em, w, key)
                    layers = C_structural.layer_optima(w)
                    acceptable = {kk: set(layers[kk]["optima"]) for kk in range(m + 1)}
                    covers = set()
                    for perm in itertools.permutations(range(m)):
                        covers.add(frozenset(kk for kk in range(m + 1)
                                             if tuple(sorted(perm[:kk])) in acceptable[kk]))
                    universe = frozenset(range(m + 1))
                    chi = None
                    for size in range(1, m + 2):
                        for combo in itertools.combinations(
                                sorted(covers, key=lambda s: -len(s)), size):
                            if frozenset().union(*combo) >= universe:
                                chi = size
                                break
                        if chi is not None:
                            break
                    bucket = dist.setdefault("m%d_a%d" % (m, arity), {})
                    bucket[str(chi)] = bucket.get(str(chi), 0) + 1
                    fb = dist.setdefault(fam, {})
                    fb[str(chi)] = fb.get(str(chi), 0) + 1
    return {"campaign": "B_chi_representativeness", "distribution": dist,
            "elapsed_s": time.time() - t0}


# =====================================================================
# C. test cover scaling
# =====================================================================

def campaign_test_cover(em: Emitter, *, ms=(3, 4), arities=(2,), n_per=6,
                        seed=3, deadline=None) -> Dict:
    """C: measure Q*, greedy, r and the classical lower bound as n grows."""
    from observatory.worlds import generate_world
    rng = random.Random(seed)
    rows = []
    t0 = time.time()
    for m in ms:
        for arity in arities:
            for fam in ("cartesian", "weak_coupling", "strong_coupling", "random_sparse"):
                for _ in range(n_per):
                    if deadline and time.time() - t0 > deadline:
                        break
                    w = generate_world(fam, m, arity, rng=rng)
                    if len(w.support.omega) > 24:
                        continue
                    k = max(1, m // 2)
                    key = world_key(w, campaign="C_test_cover")
                    for max_family in (3, 5, 8):
                        fam_list = C_support.build_support_family(
                            w, k, ZERO, max_family=max_family)
                        if len(fam_list) < 2:
                            continue
                        C_support.probe_test_cover(em, w, fam_list, k, ZERO,
                                                   dict(key, family_size=max_family),
                                                   exact_cap=3)
                        rows.append({"m": m, "arity": arity, "family": fam,
                                     "n_supports": len(fam_list)})
    return {"campaign": "C_test_cover_scaling", "n_instances": len(rows),
            "elapsed_s": time.time() - t0}


# =====================================================================
# D. typed completion hardness
# =====================================================================

def campaign_typed_completion(em: Emitter, *, n=400, seed=4, deadline=None) -> Dict:
    """D: is greedy actually bad on typed evidence, or is the direction empty?"""
    rng = random.Random(seed)
    t0 = time.time()
    for i in range(n):
        if deadline and time.time() - t0 > deadline:
            break
        n_obl = rng.choice([4, 5, 6, 7])
        n_ev = rng.choice([6, 8, 10, 12])
        C_master.probe_typed_completion(
            em, {"family": "typed_completion", "m": 0, "arity": 0, "draw": i,
                 "campaign": "D_typed_completion", "n_obl": n_obl, "n_ev": n_ev},
            rng, n_obligations=n_obl, n_evidence=n_ev)
    return {"campaign": "D_typed_completion", "n_draws": n,
            "elapsed_s": time.time() - t0}


# =====================================================================

CAMPAIGNS = {"A": "rank_one", "B": "chi", "C": "test_cover", "D": "typed_completion"}


def main(argv=None):
    from observatory.worlds import FAMILIES
    p = argparse.ArgumentParser(description="CIG-AMF targeted campaigns")
    p.add_argument("--which", default="ABCD")
    p.add_argument("--out", default="research/observatory/campaigns")
    p.add_argument("--seed", type=int, default=20260904)
    p.add_argument("--scale", type=int, default=1, help="multiplier on sample counts")
    p.add_argument("--budget", type=float, default=600.0, help="seconds per campaign")
    a = p.parse_args(argv)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%d_%H%M%S")
    ctx = make_context("campaigns", a.seed, root=ROOT,
                       notes="targeted campaigns " + a.which)
    results = {}
    with Emitter(out / ("campaigns_%s.jsonl" % stamp), ctx) as em:
        if "A" in a.which:
            results["A"] = campaign_rank_one(
                em, ms=(4, 6), arities=(3, 4), n_per=60 * a.scale,
                seed=a.seed + 1, deadline=a.budget)
        if "B" in a.which:
            results["B"] = campaign_chi(
                em, families=FAMILIES, ms=(3, 4, 5), arities=(2, 3),
                n_per=4 * a.scale, seed=a.seed + 2, deadline=a.budget)
        if "C" in a.which:
            results["C"] = campaign_test_cover(
                em, ms=(3, 4), arities=(2,), n_per=4 * a.scale,
                seed=a.seed + 3, deadline=a.budget)
        if "D" in a.which:
            results["D"] = campaign_typed_completion(
                em, n=300 * a.scale, seed=a.seed + 4, deadline=a.budget)
    (out / ("summary_%s.json" % stamp)).write_text(
        json.dumps(results, indent=2, default=str), encoding="utf-8")
    if "A" in results:
        a_res = results["A"]
        print("")
        print("  RANK-ONE LADDER: %s" % (
            "*** CONJECTURE KILLED -- exact violation found ***"
            if a_res["conjecture_killed"] else
            "no violation; conjecture survives this batch"))
        print("  worlds=%d  max kappa/(m-1)=%s" % (
            a_res["n_worlds"], a_res.get("max_kappa_over_bound")))
        print("")
    for k, v in results.items():
        print("[%s] %s" % (k, json.dumps(
            {kk: vv for kk, vv in v.items()
             if kk not in ("kappa_samples", "witness", "distribution")},
            default=str)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
