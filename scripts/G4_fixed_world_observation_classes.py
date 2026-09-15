#!/usr/bin/env python3
"""G4 -- Query/MASTER: classify worlds by MEASUREMENT TYPE on ONE fixed world.

The world is the corpus's own compensated world

    F_{A,T,j,rho,t0}(x) = gate_A(x) + linear(compensation)(x) - shift

(`centeredWorld` of work/p13_conjectures/LeanD6ReferenceCenteredCompensatedV1.lean,
identical to `build_world(...)["Fworld"]` of scripts/MASTER_fixed_world_acquisition.py).
T, j = z, rho and the reference t0 are held FIXED; the hidden world is the set A.

THREE EXPERIMENTS, same world, different measurement:

  E_mean : observe the response levels Q_i(u) = E_{t0}[F | X_i = u]  (+ Gaussian noise).
  E_raw  : observe Y = F_A(X) + Z,  X ~ Bernoulli(t0)^m HIDDEN,  Z ~ N(0, sigma^2).
  E_ctx  : observe the pair (X, Y), same X and Z.

E_raw is E_ctx with X deleted.  NOTHING here asserts that E_mean is a free
post-processing of an E_raw sample: E_mean is a DIFFERENT instrument (it reads
conditional levels, which a raw sample with X hidden cannot form), and the only
claims made about it are about its own observable.

WHAT IS COMPUTED (all exact `fractions.Fraction`; every closed form is checked
against brute force on the full cube and the script RAISES on any mismatch):

  P0  self-checks: gateMass / slopeBval / gateSlope vs brute-force conditional
      expectations; `centered_response`; `actual_full_count_loss`.
  P1  E_mean equivalence classes (from the exact response function).
  P2  E_raw equivalence classes, from the EXACT weighted histogram
          H_A(z) = sum_{x : F_A(x) = z} t0^{|x|} (1-t0)^{m-|x|},
      grouped as exact rational dictionaries -- NOT by a few moments.
      Compared against the orbit partition by h = |A cap T|.
  P3  E_ctx separation, from the exact contextual KL
          KL = (1/(2 sigma^2)) sum_x p_{t0}(x) (F_A(x) - F_B(x))^2.
  P4  THE DECIDING PART.  Decisions are retained sets S under a cardinality
      budget; the loss is the corpus's OWN `productCompressionLoss`
          L_A(S) = osc_x( F_A(x) - sum_{i in S} Q_i^A(x_i) ) / 2,
      computed directly on the cube (and cross-checked against `countLoss`).
      For every pair of worlds with the SAME raw histogram we ask whether a
      single decision can be eps-safe for both.

WHAT THIS DOES NOT ESTABLISH: nothing here is a proof.  Every number below is
NUMERICAL EVIDENCE on the enumerated configurations only (see `scope` in the
artifact).  No claim is made for k outside the enumerated range, for
non-product references, for adaptive queries, or for any sample-size/regret
theorem.  `H_A = H_B  <=>  equal law of Y` uses the standard injectivity of
Gaussian convolution; that direction is a cited textbook fact, not proved here.
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
from fractions import Fraction as Fr

PROTOCOL_VERSION = "g4_fixed_world_observation_classes_v1"


class ProbeMismatch(RuntimeError):
    """Raised whenever a closed form disagrees with brute force."""


def _require(cond, msg):
    if not cond:
        raise ProbeMismatch(msg)


# --------------------------------------------------------------- the world
def make_cfg(k, t0, rho):
    """The D6 instance: m = 2k coordinates, j = z = m-1, |A| = k, |others| = k-1,
    T = {0, ..., k-1} (so j not in T)."""
    m = 2 * k
    return {"k": k, "m": m, "j": m - 1, "T": frozenset(range(k)), "t0": t0, "rho": rho}


def worlds(cfg):
    """Every hidden set: A subset of univ \\ {j}, |A| = k."""
    ground = [i for i in range(cfg["m"]) if i != cfg["j"]]
    return [frozenset(c) for c in itertools.combinations(ground, cfg["k"])]


def others(cfg, A):
    return frozenset(i for i in range(cfg["m"]) if i != cfg["j"] and i not in A)


def gate(cfg, A, x):
    """`gate A j` of LeanD6ThresholdConstructionV1."""
    j = cfg["j"]
    if x[j]:
        return Fr(0)
    if any(x[i] for i in A):
        return Fr(1)
    B = others(cfg, A)
    return Fr(1) if sum(1 for i in B if x[i]) >= 2 else Fr(0)


def tail_factor(t, card):
    return (1 - t) ** card + Fr(card) * t * (1 - t) ** (card - 1)


def gate_mass(cfg, A, t):
    return (1 - t) ** len(A) * tail_factor(t, len(others(cfg, A)))


def slope_b(cfg, A, t):
    nb = len(others(cfg, A))
    return (Fr(nb) - 1) * t * (1 - t) ** (len(A) + nb - 1)


def gate_slope(cfg, A, t, i):
    if i == cfg["j"]:
        return gate_mass(cfg, A, t) - 1
    if i in A:
        return gate_mass(cfg, A, t)
    return slope_b(cfg, A, t)


def target(cfg, i):
    return cfg["rho"] if i in cfg["T"] else Fr(0)


def compensation(cfg, A, t, i):
    return target(cfg, i) - gate_slope(cfg, A, t, i)


def shift(cfg, A, t):
    return (1 - t) * (1 - gate_mass(cfg, A, t)) + t * sum(
        compensation(cfg, A, t, i) for i in range(cfg["m"]))


def cube(m):
    return list(itertools.product((0, 1), repeat=m))


def world_fn(cfg, A):
    """F_A on the whole cube, as a dict x -> Fraction."""
    t = cfg["t0"]
    comp = [compensation(cfg, A, t, i) for i in range(cfg["m"])]
    sh = shift(cfg, A, t)
    out = {}
    for x in cube(cfg["m"]):
        out[x] = gate(cfg, A, x) + sum(comp[i] for i in range(cfg["m"]) if x[i]) - sh
    return out


def bern_w(x, t):
    w = Fr(1)
    for xi in x:
        w *= t if xi else (1 - t)
    return w


def cube_weights(m, t):
    return {x: bern_w(x, t) for x in cube(m)}


# --------------------------------------- brute-force response / expectation
def response_levels(cfg, F, i):
    """productResponse(bern t0, F, i, u): E over the OTHER coordinates with
    coordinate i pinned to u.  Matches `productResponse` (Function.update)."""
    t = cfg["t0"]
    m = cfg["m"]
    out = {}
    for u in (0, 1):
        s = Fr(0)
        for x in cube(m):
            w = bern_w(x, t)
            y = F[tuple(u if jj == i else x[jj] for jj in range(m))]
            s += w * y
        out[u] = s
    return out


def osc(vals):
    return max(vals) - min(vals)


def compression_loss(cfg, F, Q, S):
    """productCompressionLoss: osc_x( F(x) - sum_{i in S} Q_i(x_i) ) / 2."""
    vals = []
    for x, y in F.items():
        vals.append(y - sum(Q[i][x[i]] for i in S))
    return osc(vals) / 2


def count_loss(a, b, rho, na, nb, u, v):
    """`countLoss` of LeanD6ReferenceFullCountLossV1, verbatim."""
    corr = min(a, 2 * b) if (u == 0 and v == 0) else (b if (u == 0 and v == 1) else Fr(0))
    upper = 1 + (rho - a) * Fr(u) + (rho - b) * Fr(v) - corr
    lo1 = (1 - a) - a * (Fr(na) - Fr(u)) - b * (Fr(nb) - Fr(v))
    lo2 = -b if v < nb else Fr(0)
    return (upper - min(lo1, lo2)) / 2


# ------------------------------------------------------------ P0 self-check
def self_checks(cfg):
    t = cfg["t0"]
    m, j, T, rho = cfg["m"], cfg["j"], cfg["T"], cfg["rho"]
    n_slope = n_resp = n_loss = 0
    for A in worlds(cfg):
        F = world_fn(cfg, A)
        B = others(cfg, A)
        # (a) closed-form gate slope vs brute force on the BARE gate
        G = {x: gate(cfg, A, x) for x in cube(m)}
        for i in range(m):
            lv = response_levels(cfg, G, i)
            _require(lv[1] - lv[0] == gate_slope(cfg, A, t, i),
                     f"gateSlope mismatch A={sorted(A)} i={i}")
            n_slope += 1
        # (b) centered_response: both LEVELS equal target * (bit u - t)
        Q = {}
        for i in range(m):
            lv = response_levels(cfg, F, i)
            for u in (0, 1):
                _require(lv[u] == target(cfg, i) * (Fr(u) - t),
                         f"centered_response mismatch A={sorted(A)} i={i} u={u}")
                n_resp += 1
            Q[i] = lv
        # (c) actual_full_count_loss on EVERY subset of T
        a_, b_ = gate_mass(cfg, A, t), slope_b(cfg, A, t)
        for r in range(len(T) + 1):
            for S in itertools.combinations(sorted(T), r):
                Sset = frozenset(S)
                D = T - Sset
                u = len(D & A)
                v = len(D & B)
                lhs = compression_loss(cfg, F, Q, Sset)
                rhs = count_loss(a_, b_, rho, len(A), len(B), u, v)
                _require(lhs == rhs,
                         f"countLoss mismatch A={sorted(A)} S={S}: {lhs} vs {rhs}")
                n_loss += 1
    return {"gate_slope_cells": n_slope, "centered_response_cells": n_resp,
            "count_loss_cells": n_loss, "all_pass": True}


# ------------------------------------------------------------------ P1 mean
def mean_classes(cfg):
    """E_mean observable = the whole response function i |-> (Q_i(0), Q_i(1))."""
    sig = {}
    for A in worlds(cfg):
        F = world_fn(cfg, A)
        key = tuple((str(response_levels(cfg, F, i)[0]), str(response_levels(cfg, F, i)[1]))
                    for i in range(cfg["m"]))
        sig.setdefault(key, []).append(sorted(A))
    return {"n_worlds": len(worlds(cfg)), "n_classes": len(sig),
            "classes": [{"observable": list(k), "worlds": v} for k, v in sig.items()]}


# ------------------------------------------------------------------- P2 raw
def histogram(cfg, F, W):
    h = {}
    for x, y in F.items():
        h[y] = h.get(y, Fr(0)) + W[x]
    tot = sum(h.values())
    _require(tot == 1, f"histogram mass {tot} != 1")
    return h


def hist_key(h):
    return tuple(sorted((str(z), str(p)) for z, p in h.items()))


def raw_moments(h, upto=6):
    return [sum(p * z ** r for z, p in h.items()) for r in range(1, upto + 1)]


def raw_classes(cfg):
    W = cube_weights(cfg["m"], cfg["t0"])
    hs, buckets = {}, {}
    for A in worlds(cfg):
        h = histogram(cfg, world_fn(cfg, A), W)
        hs[A] = h
        buckets.setdefault(hist_key(h), []).append(A)
    orbit = {}
    for A in worlds(cfg):
        orbit.setdefault(len(A & cfg["T"]), []).append(A)
    raw_part = {frozenset(v) for v in buckets.values()}
    orb_part = {frozenset(v) for v in orbit.values()}
    # where two classes differ, exhibit a separating moment
    sep = []
    keys = sorted(buckets)
    for ia in range(len(keys)):
        for ib in range(ia + 1, len(keys)):
            ha = hs[buckets[keys[ia]][0]]
            hb = hs[buckets[keys[ib]][0]]
            ma, mb = raw_moments(ha), raw_moments(hb)
            order = next((r + 1 for r in range(len(ma)) if ma[r] != mb[r]), None)
            sep.append({"class_a": [sorted(x) for x in buckets[keys[ia]]][:1],
                        "class_b": [sorted(x) for x in buckets[keys[ib]]][:1],
                        "lowest_differing_moment_of_F": order})
    return {
        "n_worlds": len(worlds(cfg)),
        "n_raw_classes": len(buckets),
        "raw_classes": [{"h_of_representative": len(v[0] & cfg["T"]),
                         "size": len(v), "worlds": [sorted(a) for a in v],
                         "support_size": len(hs[v[0]])}
                        for v in buckets.values()],
        "orbit_partition_by_h": {str(hh): [sorted(a) for a in v] for hh, v in orbit.items()},
        "raw_partition_equals_orbit_partition": raw_part == orb_part,
        "cross_class_separating_moments": sep,
        "note": "classes are exact rational histograms, not moment digests",
    }, hs


# ------------------------------------------------------------------- P3 ctx
def ctx_separation(cfg, sigma):
    W = cube_weights(cfg["m"], cfg["t0"])
    Ws = worlds(cfg)
    Fs = {A: world_fn(cfg, A) for A in Ws}
    rows, zero_pairs = [], 0
    for ia in range(len(Ws)):
        for ib in range(ia + 1, len(Ws)):
            A, Bw = Ws[ia], Ws[ib]
            d2 = sum(W[x] * (Fs[A][x] - Fs[Bw][x]) ** 2 for x in W)
            kl = d2 / (2 * sigma ** 2)
            differs = any(Fs[A][x] != Fs[Bw][x] for x in W)
            _require((kl > 0) == differs,
                     f"KL/pointwise-difference disagree for {sorted(A)},{sorted(Bw)}")
            if kl == 0:
                zero_pairs += 1
            rows.append({"A": sorted(A), "B": sorted(Bw), "kl_per_sample": float(kl),
                         "same_raw_hist": None})
    return {"sigma": str(sigma), "n_pairs": len(rows),
            "pairs_with_zero_ctx_KL": zero_pairs,
            "min_positive_kl_per_sample": min((r["kl_per_sample"] for r in rows
                                               if r["kl_per_sample"] > 0), default=None),
            "n_ctx_classes": len(Ws) - 0 if zero_pairs == 0 else None,
            "all_distinct_worlds_separated_by_context": zero_pairs == 0,
            "pairs": rows}


# -------------------------------------------------------------- P4 deciding
def decisions(cfg, budget, full_ground=False):
    """Retained sets under the cardinality budget |S| = budget.

    Only S cap T can affect the loss (Q_i == 0 off T).  An exact-size retained
    set on the full ground can use zero-response coordinates as padding, so its
    intersection with T may have ANY size at most `budget`.  The reduced space
    must therefore enumerate all subsets of T of size <= budget;
    `full_ground=True` enumerates exact-size full-ground decisions as a check."""
    src = sorted(range(cfg["m"])) if full_ground else sorted(cfg["T"])
    sizes = (budget,) if full_ground else range(budget + 1)
    return [frozenset(c) for r in sizes for c in itertools.combinations(src, r)]


def losses_table(cfg):
    out = {}
    for A in worlds(cfg):
        F = world_fn(cfg, A)
        Q = {i: response_levels(cfg, F, i) for i in range(cfg["m"])}
        out[A] = (F, Q)
    return out


def deciding(cfg, tabs, hs):
    """For every pair of worlds with the SAME raw histogram, under every budget:
    does a single decision exist that is as safe as each world's own optimum?"""
    T = cfg["T"]
    Ws = worlds(cfg)
    L = {}
    for A in Ws:
        F, Q = tabs[A]
        for q in range(len(T) + 1):
            for S in decisions(cfg, q):
                L[(A, S)] = compression_loss(cfg, F, Q, S)
    # Cross-check the padding reduction: exact-size full-ground decisions and
    # at-most-size decisions inside T have the same optimum.
    xcheck = []
    for A in Ws[: min(3, len(Ws))]:
        F, Q = tabs[A]
        for q in range(len(T) + 1):
            best_T = min(L[(A, S)] for S in decisions(cfg, q))
            best_all = min(compression_loss(cfg, F, Q, S)
                           for S in decisions(cfg, q, full_ground=True))
            _require(best_T == best_all,
                     f"a retained set outside T beat the T-only optimum: A={sorted(A)} q={q}")
            xcheck.append({"A": sorted(A), "budget": q, "min_over_T": str(best_T)})
    rows = []
    same_hist_pairs = 0
    for ia in range(len(Ws)):
        for ib in range(ia + 1, len(Ws)):
            A, Bw = Ws[ia], Ws[ib]
            if hist_key(hs[A]) != hist_key(hs[Bw]):
                continue
            same_hist_pairs += 1
            for q in range(len(T) + 1):
                Ds = decisions(cfg, q)
                own_a = min(L[(A, S)] for S in Ds)
                own_b = min(L[(Bw, S)] for S in Ds)
                minmax = min(max(L[(A, S)], L[(Bw, S)]) for S in Ds)
                floor = max(own_a, own_b)
                gap = minmax - floor
                rows.append({
                    "A": sorted(A), "B": sorted(Bw), "h": len(A & T), "budget": q,
                    "own_optimum_A": str(own_a), "own_optimum_B": str(own_b),
                    "best_common_worst_case": str(minmax),
                    "separation_gap": str(gap), "separation_gap_float": float(gap),
                    "no_common_eps_safe_decision": bool(gap > 0),
                    "eps_witness": str(floor) if gap > 0 else None,
                })
    pos = [r for r in rows if r["no_common_eps_safe_decision"]]
    # `rows` has ONE ENTRY PER (pair, budget), so len(pos) is a count of
    # (pair, budget) combinations, NOT of pairs. Reporting it under a key named
    # `pairs_...` made it exceed `same_raw_histogram_pairs`, which looked like a
    # contradiction. Both numbers are now reported under honest names.
    pos_pairs = {(tuple(r["A"]), tuple(r["B"])) for r in pos}
    # class-level (not just pairwise) version
    cls = {}
    for A in Ws:
        cls.setdefault(hist_key(hs[A]), []).append(A)
    class_rows = []
    for key, members in cls.items():
        if len(members) < 2:
            continue
        for q in range(len(T) + 1):
            Ds = decisions(cfg, q)
            # DETERMINISTIC min-max.  This is NOT a floor for randomized
            # procedures: a mixed decision rule can do strictly better, and on
            # the k=3 witness it does (13983/32768 deterministic against
            # 2401/8192 randomized).  Keyed as `..._deterministic_...` so the
            # number cannot be quoted as a bound for every algorithm.  The
            # randomized value is computed exactly for two-member classes below
            # and in scripts/Q1_intervention_regret_floor.py.
            minmax = min(max(L[(A, S)] for A in members) for S in Ds)
            floor = max(min(L[(A, S)] for S in Ds) for A in members)
            rand_minmax = None
            if len(members) == 2:
                rand_minmax = _randomized_minimax_two_rows(
                    [[L[(w, S)] for S in Ds] for w in members])
            class_rows.append({
                "h": len(members[0] & T), "class_size": len(members), "budget": q,
                "raw_deterministic_minimax_loss": str(minmax),
                "raw_randomized_minimax_loss":
                    str(rand_minmax) if rand_minmax is not None else None,
                "randomized_note": None if rand_minmax is not None else
                    "exact randomized value implemented only for two-member "
                    "classes; larger classes need an LP and are left null "
                    "rather than reported as the deterministic number",
                "ctx_worst_case_loss": str(floor),
                "regret_floor_drop_ctx_vs_raw_DETERMINISTIC": str(minmax - floor),
                "regret_floor_drop_float": float(minmax - floor),
            })
    return {
        "decision_space": "full decisions have |S| = budget; the exact reduced "
                          "space is S subset T with |S| <= budget because "
                          "zero-response coordinates outside T provide padding; "
                          "loss = productCompressionLoss(F_A,Q_A,S)",
        "outside_T_cross_check": xcheck,
        "same_raw_histogram_pairs": same_hist_pairs,
        "pair_budget_combinations_tested": len(rows),
        "pair_budget_combinations_with_no_common_eps_safe_decision": len(pos),
        "distinct_pairs_with_no_common_eps_safe_decision": len(pos_pairs),
        "eps_reading": "a row is counted when min_S max(L_A(S), L_B(S)) > "
                       "max(min_S L_A(S), min_S L_B(S)), i.e. at eps equal to the "
                       "best either world could achieve alone, NO single retained "
                       "set is eps-safe for both",
        "max_separation_gap": max([r["separation_gap_float"] for r in rows], default=None),
        "pair_rows": rows,
        "class_rows": class_rows,
        "max_regret_floor_drop": max([r["regret_floor_drop_float"] for r in class_rows],
                                     default=None),
    }


def _randomized_minimax_two_rows(rows):
    """Exact value of min over mixed column strategies of max over two rows.

    For two rows an optimal mixed column strategy has support at most two, so
    enumerating pure columns and pairs is exact.  Returns a `Fraction`.
    """
    import itertools as _it
    a, b = rows
    n = len(a)
    best = min(max(a[i], b[i]) for i in range(n))
    for i, j in _it.combinations(range(n), 2):
        den = (a[i] - a[j]) - (b[i] - b[j])
        if den == 0:
            continue
        p = (b[j] - a[j]) / den
        if not (0 <= p <= 1):
            continue
        v = p * a[i] + (1 - p) * a[j]
        _require(v == p * b[i] + (1 - p) * b[j], "equalisation failed")
        best = min(best, v)
    return best


# ----------------------------------------------------------- permutation law
def perm_transport_check(cfg):
    """Route 1, numerically: for pi fixing j and preserving T,
    F_{pi A}(pi x) = F_A(x) pointwise."""
    m, j, T = cfg["m"], cfg["j"], cfg["T"]
    inT = sorted(T)
    outT = sorted(i for i in range(m) if i != j and i not in T)
    cells = 0
    for A in worlds(cfg):
        F = world_fn(cfg, A)
        for pa in itertools.permutations(inT):
            for pb in itertools.permutations(outT):
                pi = {}
                for s, d in zip(inT, pa):
                    pi[s] = d
                for s, d in zip(outT, pb):
                    pi[s] = d
                pi[j] = j
                A2 = frozenset(pi[i] for i in A)
                F2 = world_fn(cfg, A2)
                for x in cube(m):
                    xx = [0] * m
                    for i in range(m):
                        xx[pi[i]] = x[i]
                    _require(F2[tuple(xx)] == F[x],
                             f"perm transport failed A={sorted(A)} pi={pi}")
                    cells += 1
    return {"transported_cells": cells, "all_pass": True,
            "group": "Sym(T) x Sym(ground \\ T) fixing j"}


# ------------------------------------------------------------------- driver
def run_cfg(k, t0, rho, sigma, do_perm, do_ctx):
    cfg = make_cfg(k, t0, rho)
    out = {"k": k, "m": cfg["m"], "j": cfg["j"], "T": sorted(cfg["T"]),
           "t0": str(t0), "rho": str(rho)}
    out["p0_self_checks"] = self_checks(cfg)
    out["p1_E_mean"] = mean_classes(cfg)
    rc, hs = raw_classes(cfg)
    out["p2_E_raw"] = rc
    if do_ctx:
        out["p3_E_ctx"] = ctx_separation(cfg, sigma)
    if do_perm:
        out["p_route1_permutation_transport"] = perm_transport_check(cfg)
    out["p4_deciding"] = deciding(cfg, losses_table(cfg), hs)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--ks", type=int, nargs="+", default=[3, 4])
    ap.add_argument("--sigma", default="1/10")
    a = ap.parse_args()
    if os.path.exists(a.out) and not a.overwrite:
        sys.exit(f"refusing to overwrite {a.out}; pass --overwrite")
    sigma = Fr(a.sigma)

    res = {"protocol_version": PROTOCOL_VERSION,
           "arithmetic": "exact fractions.Fraction everywhere; floats only in "
                         "reported summaries",
           "world": "centeredWorld A T j rho t0 (LeanD6ReferenceCenteredCompensatedV1); "
                    "identical to build_world() of MASTER_fixed_world_acquisition.py",
           "does_not_establish": [
               "no proof of anything; numerical evidence on the enumerated grid only",
               "no claim that E_mean is a post-processing of an E_raw sample",
               "H_A = H_B <=> equal law of Y uses injectivity of Gaussian "
               "convolution, a cited fact, not checked here",
               "no sample-size, no adaptive-query, no minimax-over-priors theorem"],
           "scope": {"ks": a.ks, "t0_grid": ["1/8", "1/4", "1/3"],
                     "rho_grid": ["1", "3/2"], "sigma": a.sigma},
           "cases": []}

    for k in a.ks:
        for t0 in (Fr(1, 8), Fr(1, 4), Fr(1, 3)):
            for rho in (Fr(1), Fr(3, 2)):
                do_perm = (k == 3 and t0 == Fr(1, 4) and rho == Fr(1))
                do_ctx = (k <= 4)
                print(f"  k={k} t0={t0} rho={rho} ...", flush=True)
                res["cases"].append(run_cfg(k, t0, rho, sigma, do_perm, do_ctx))

    # ---------------- global summary
    summ = {
        "E_mean_classes_per_case": sorted({c["p1_E_mean"]["n_classes"] for c in res["cases"]}),
        "E_raw_classes_per_case": {f"k={c['k']},t0={c['t0']},rho={c['rho']}":
                                   c["p2_E_raw"]["n_raw_classes"] for c in res["cases"]},
        "raw_partition_equals_orbit_partition_everywhere":
            all(c["p2_E_raw"]["raw_partition_equals_orbit_partition"] for c in res["cases"]),
        "E_ctx_separates_all_worlds_everywhere":
            all(c["p3_E_ctx"]["all_distinct_worlds_separated_by_context"]
                for c in res["cases"] if "p3_E_ctx" in c),
        "same_raw_histogram_pairs_total":
            sum(c["p4_deciding"]["same_raw_histogram_pairs"] for c in res["cases"]),
        "distinct_pairs_with_no_common_eps_safe_decision_total":
            sum(c["p4_deciding"]["distinct_pairs_with_no_common_eps_safe_decision"]
                for c in res["cases"]),
        "pair_budget_combinations_with_no_common_eps_safe_decision_total":
            sum(c["p4_deciding"]["pair_budget_combinations_with_no_common_eps_safe_decision"]
                for c in res["cases"]),
        "max_regret_floor_drop_over_cases":
            max([c["p4_deciding"]["max_regret_floor_drop"] for c in res["cases"]
                 if c["p4_deciding"]["max_regret_floor_drop"] is not None] or [None]),
    }
    summ["DECIDING_VERDICT"] = (
        f"POSITIVE: "
        f"{summ['distinct_pairs_with_no_common_eps_safe_decision_total']} of the "
        f"{summ['same_raw_histogram_pairs_total']} DISTINCT same-raw-histogram pairs "
        f"admit NO common eps-safe decision at the real compensated-world loss "
        f"(counted over "
        f"{summ['pair_budget_combinations_with_no_common_eps_safe_decision_total']} "
        f"(pair, budget) combinations)"
        if summ["distinct_pairs_with_no_common_eps_safe_decision_total"] > 0 else
        "NEGATIVE: every pair of worlds with the same raw law shares a safe "
        "decision at every budget; not learning all of A is NOT a "
        "decision-theoretic obstruction on this grid")
    res["summary"] = summ

    with open(a.out, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)

    print("\n=== G4 SUMMARY ===")
    for kk, vv in summ.items():
        print(f"  {kk}: {vv}")
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
