#!/usr/bin/env python3
"""Q-Intervention: the RANDOMIZED minimax regret floor under raw measurement.

The supervisor's audit found that G4's class-level number at
`scripts/G4_fixed_world_observation_classes.py:412` is

    min over decisions S of  max over worlds A of  L_A(S),

a DETERMINISTIC minimax.  It is not a bound for randomized algorithms, so it may
not be quoted as a floor for "every algorithm".  This probe computes the
randomized quantity instead, on the corpus's own compensated world, with exact
rational arithmetic and BOTH directions:

    upper : an explicit mixed decision rule attaining the value on both worlds;
    lower : an explicit prior on the two worlds whose Bayes regret equals it.

Because the two worlds have the SAME raw law, any procedure that sees only raw
observations induces the same decision distribution on both, so its worst-case
regret is at least this value -- however many samples it takes, adaptively or not.

Configuration (the supervisor's witness):  k = 3, t0 = 1/8, rho = 1,
T = {0,1,2}, j = 5, A = {0,1,3}, B = {0,2,3}, retained budget 1.

Raises on any mismatch.   python3 scripts/Q1_intervention_regret_floor.py
"""
from __future__ import annotations

import importlib.util
import itertools
import json
from fractions import Fraction as Fr
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
G4 = REPO / "scripts" / "G4_fixed_world_observation_classes.py"


def load_g4():
    spec = importlib.util.spec_from_file_location("g4", G4)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def two_row_game_value(reg):
    """Exact value of a 2-row zero-sum game, columns = decisions.

    `reg[w]` is the list of regrets of world `w`.  Returns (value, mix), the mix
    being a dict column -> Fraction.  For two rows an optimal mixed column
    strategy has support at most two, so enumerating pairs is exact.
    """
    a, b = reg
    n = len(a)
    best = None
    for i in range(n):                      # pure columns
        v = max(a[i], b[i])
        if best is None or v < best[0]:
            best = (v, {i: Fr(1)})
    for i, j in itertools.combinations(range(n), 2):
        # p on i, 1-p on j;  equalise  p a_i + (1-p) a_j  =  p b_i + (1-p) b_j
        den = (a[i] - a[j]) - (b[i] - b[j])
        if den == 0:
            continue
        p = (b[j] - a[j]) / den
        if not (0 <= p <= 1):
            continue
        v = p * a[i] + (1 - p) * a[j]
        if v != p * b[i] + (1 - p) * b[j]:
            raise AssertionError("equalisation failed")
        if v < best[0]:
            best = (v, {i: p, j: 1 - p})
    return best


def bayes_lower(reg, q):
    """Bayes regret under prior q = (qA, qB): min over columns of the mixture."""
    a, b = reg
    return min(q[0] * a[i] + q[1] * b[i] for i in range(len(a)))


def main():
    g4 = load_g4()
    k, t0, rho = 3, Fr(1, 8), Fr(1)
    cfg = g4.make_cfg(k, t0, rho)
    T = sorted(cfg["T"])
    A = frozenset({0, 1, 3})
    B = frozenset({0, 2, 3})
    assert cfg["j"] == 5 and cfg["m"] == 6, (cfg["j"], cfg["m"])

    F = {w: g4.world_fn(cfg, w) for w in (A, B)}
    Q = {w: {i: g4.response_levels(cfg, F[w], i) for i in range(cfg["m"])}
         for w in (A, B)}

    # --- the two worlds share the exact raw histogram ------------------------
    def hist(w):
        h = {}
        for x in g4.cube(cfg["m"]):
            h[F[w][x]] = h.get(F[w][x], Fr(0)) + g4.bern_w(x, t0)
        return h
    hA, hB = hist(A), hist(B)
    if hA != hB:
        raise AssertionError("the two worlds do NOT share a raw histogram")
    if sum(hA.values()) != 1:
        raise AssertionError("histogram is not a probability distribution")
    print(f"raw histograms agree exactly: {len(hA)} atoms, total mass 1")

    # --- the loss table at budget 1 -----------------------------------------
    # decisions: subsets of T of size <= 1 (coordinates outside T have zero
    # response, so they only pad the cardinality)
    decs = [frozenset()] + [frozenset({i}) for i in T]
    L = {(w, S): g4.compression_loss(cfg, F[w], Q[w], S) for w in (A, B) for S in decs}

    print(f"\n{'decision':>12}{'L_A':>18}{'L_B':>18}")
    for S in decs:
        nm = "{}" if not S else "{" + ",".join(map(str, sorted(S))) + "}"
        print(f"{nm:>12}{str(L[(A,S)]):>18}{str(L[(B,S)]):>18}")

    optA = min(L[(A, S)] for S in decs)
    optB = min(L[(B, S)] for S in decs)
    reg = [[L[(A, S)] - optA for S in decs], [L[(B, S)] - optB for S in decs]]

    # --- deterministic vs randomized ----------------------------------------
    det_loss = min(max(L[(A, S)], L[(B, S)]) for S in decs)
    det_regret = min(max(reg[0][i], reg[1][i]) for i in range(len(decs)))
    value, mix = two_row_game_value(reg)
    print(f"\nown optimum        A = {optA}   B = {optB}")
    print(f"deterministic minimax regret (what G4:412 computes) = {det_regret}"
          f"  = {float(det_regret):.6f}")
    print(f"RANDOMIZED minimax regret                           = {value}"
          f"  = {float(value):.6f}")
    mixs = {("{}" if not decs[i] else "{" + ",".join(map(str, sorted(decs[i]))) + "}"): str(p)
            for i, p in mix.items()}
    print(f"  attained by the mixed rule {mixs}")

    # matching lower bound from an explicit prior
    prior = (Fr(1, 2), Fr(1, 2))
    lb = bayes_lower(reg, prior)
    print(f"  Bayes regret under the uniform prior {tuple(map(str, prior))} = {lb}")
    if lb != value:
        raise AssertionError(f"prior does not match the value: {lb} vs {value}")
    if value != Fr(2401, 8192):
        raise AssertionError(f"randomized minimax regret is {value}, expected 2401/8192")
    # the mixed rule really does attain it on BOTH worlds
    for r in range(2):
        got = sum(p * reg[r][i] for i, p in mix.items())
        if got != value:
            raise AssertionError(f"mixed rule gives {got} on row {r}, not {value}")
    print(f"\nboth directions agree: randomized minimax regret = {value} exactly")

    # --- what breaks the blindness: the contextual separation ---------------
    diff2 = sum(g4.bern_w(x, t0) * (F[A][x] - F[B][x]) ** 2 for x in g4.cube(cfg["m"]))
    print(f"E[(F_A - F_B)^2] = {diff2} = {float(diff2):.8e}   (context separates; "
          f"KL = that / (2 sigma^2))")
    if diff2 <= 0:
        raise AssertionError("contextual separation is not positive")

    out = REPO / "research/worker_Q_intervention_20260914/Q1_intervention_regret_floor.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "config": {"k": k, "t0": str(t0), "rho": str(rho), "T": T, "j": cfg["j"],
                   "A": sorted(A), "B": sorted(B), "budget": 1},
        "raw_histograms_equal": True,
        "loss_table": {("{}" if not S else "{" + ",".join(map(str, sorted(S))) + "}"):
                       {"L_A": str(L[(A, S)]), "L_B": str(L[(B, S)])} for S in decs},
        "own_optimum": {"A": str(optA), "B": str(optB)},
        "deterministic_minimax_regret": str(det_regret),
        "randomized_minimax_regret": str(value),
        "attaining_mixed_rule": mixs,
        "matching_prior": [str(prior[0]), str(prior[1])],
        "contextual_separation_E_sq_diff": str(diff2),
        "scope": "one configuration (k=3, t0=1/8, rho=1, budget 1) and one pair of "
                 "worlds. NOT a law in k, not a sample-size statement, and the "
                 "lower bound is for procedures whose observable is the raw law only.",
        "corrects": "scripts/G4_fixed_world_observation_classes.py:412 computes a "
                    "DETERMINISTIC min-max and may not be quoted as a floor for "
                    "randomized algorithms.",
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
