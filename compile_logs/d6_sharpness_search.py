#!/usr/bin/env python3
"""Exact integer search for D6 approximation and decision constants.

The reference q is the point mass at the all-zero anchor.  This is a valid
product law and makes every calculation exact over integers/halves.
"""
from itertools import product, combinations
from fractions import Fraction
import json


def actions(m):
    return list(product((0, 1), repeat=m))


def update(x, i, u):
    y = list(x); y[i] = u; return tuple(y)


def delta_square(F, m):
    aa = actions(m)
    return max(abs(F[x] - F[update(x, i, c[i])] -
                   F[update(c, i, x[i])] + F[c])
               for i in range(m) for x in aa for c in aa)


def responses(F, m):
    z = (0,) * m
    return [[F[update(z, i, u)] for u in (0, 1)] for i in range(m)]


def surrogate(F, m):
    z = (0,) * m
    Q = responses(F, m)
    b = F[z]
    return {x: sum(Q[i][x[i]] for i in range(m)) - (m - 1) * b
            for x in actions(m)}


def osc(vals):
    return max(vals) - min(vals)


def compression(F, Q, selected, m):
    vals = [F[x] - sum(Q[i][x[i]] for i in selected) for x in actions(m)]
    return Fraction(osc(vals), 2)


def evaluate(F, m):
    d = delta_square(F, m)
    A = surrogate(F, m)
    sup = max(abs(F[x] - A[x]) for x in actions(m))
    Q = responses(F, m)
    spans = [osc(q) for q in Q]
    records = []
    for k in range(1, m):
        sets = list(combinations(range(m), k))
        top = max(sets, key=lambda S: (sum(spans[i] for i in S), tuple(-i for i in S)))
        losses = {S: compression(F, Q, S, m) for S in sets}
        regret = losses[top] - min(losses.values())
        records.append({"k": k, "top": top, "regret": regret,
                        "losses": losses})
    return d, sup, records


def search(m, alphabet):
    aa = actions(m)
    z = (0,) * m
    free = [x for x in aa if x != z]
    best_approx = None
    best_decision = None
    joint = None
    count = 0
    for values in product(alphabet, repeat=len(free)):
        F = {z: 0, **dict(zip(free, values))}
        d, sup, records = evaluate(F, m)
        if d == 0:
            continue
        count += 1
        ar = Fraction(sup, (m - 1) * d)
        if best_approx is None or ar > best_approx[0]:
            best_approx = (ar, F, d, sup)
        for rec in records:
            rr = rec["regret"] / ((m - 1) * d)
            if best_decision is None or rr > best_decision[0]:
                best_decision = (rr, F, d, rec)
            if ar == 1 and rr == 2:
                joint = (F, d, rec)
                break
        if joint:
            break
    def enc(item, kind):
        if item is None: return None
        if kind == "approx":
            ratio, F, d, sup = item
            return {"ratio": str(ratio), "F": {str(k): v for k,v in F.items()},
                    "delta": d, "sup": sup}
        ratio, F, d, rec = item
        return {"ratio_to_n_delta": str(ratio),
                "ratio_to_2n_delta": str(ratio / 2),
                "F": {str(k): v for k,v in F.items()}, "delta": d,
                "k": rec["k"], "top": list(rec["top"]),
                "regret": str(rec["regret"]),
                "losses": {str(k): str(v) for k,v in rec["losses"].items()}}
    return {"m":m, "tested_nonzero_delta":count,
            "best_approx":enc(best_approx,"approx"),
            "best_decision":enc(best_decision,"decision"),
            "joint_saturation_found": joint is not None}


if __name__ == "__main__":
    results = [search(2, range(-4,5)), search(3, range(-1,2))]
    with open("compile_logs/d6_sharpness_results.json", "w") as f:
        json.dump(results, f, indent=2)
    print(json.dumps(results, indent=2))
