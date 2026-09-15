#!/usr/bin/env python3
"""Does the full-extrema effect occur in worlds the ACTUAL v4 generator draws,
or only in hand-built witnesses?

EVIDENCE CLASS: NUMERICAL EVIDENCE.

The hand-built cases in f05_full_extrema_alternative_probe_v1.py show the
phenomenon EXISTS. That is not the same as it MATTERING for the panel. This
samples worlds from the generator's own recipe and measures how often the true
minimum over the full alternative differs from the fixed-extrema (pair-flip)
value, and how often the minimiser moves an extremum.

Generator recipe copied from run_functional_variance_stopping_lab_v4.py:
    capacities = sort(uniform(.35, 2.0, R))[::-1]
    truth[r]   = uniform(center - cap/2, center + cap/2, K)
    sigma      = uniform(.15, .85, K)          # per ACTION, shared across relations

Only the deciding pair matters: the weakest relation inside Top-k and the
strongest outside it. Every other relation can stay put, so the alternative
reduces to a two-relation problem on the real K.
"""
from __future__ import annotations
import itertools, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from f05_full_extrema_alternative_probe_v1 import (  # noqa: E402
    capacity, cost, fixed_extrema_pair_flip, region_qp,
)


def draw_world(rng, R=5, K=6):
    caps = np.sort(rng.uniform(.35, 2.0, size=R))[::-1]
    truth = np.empty((R, K))
    for r in range(R):
        center = rng.uniform(-1.0, 1.0)
        truth[r] = rng.uniform(center - caps[r] / 2, center + caps[r] / 2, size=K)
    sigma = rng.uniform(.15, .85, size=K)
    return truth, np.tile(sigma ** 2, (R, 1))


def main(n_worlds=12, R=5, K=6, k=2, seed=7):
    rng = np.random.default_rng(seed)
    pairs = [p for p in itertools.permutations(range(K), 2)]
    rows = []
    for i in range(n_worlds):
        truth, s2 = draw_world(rng, R, K)
        w = np.ones((R, K))
        c = capacity(truth)
        order = np.argsort(-c, kind="stable")
        r_in, r_out = int(order[k - 1]), int(order[k])      # deciding pair
        idx = [r_in, r_out]
        t2, s22, w2 = truth[idx], s2[idx], w[idx]
        pf, gap, v, wv = fixed_extrema_pair_flip(t2, w2, s22, 0, 1)
        best = None
        for hl in itertools.product(pairs, repeat=2):
            got = region_qp(t2, w2, s22, 0, 1, hl, eta=0.0)
            if got and (best is None or got[0] < best[0]):
                best = got
        if best is None:
            continue
        bv, bx = best
        old = [(int(np.argmax(t2[r])), int(np.argmin(t2[r]))) for r in range(2)]
        new = [(int(np.argmax(bx[r])), int(np.argmin(bx[r]))) for r in range(2)]
        rows.append({"world": i, "gap": gap, "pair_flip": pf, "true_min": bv,
                     "ratio": bv / pf if pf else None,
                     "extrema_changed": new != old, "old": old, "new": new})
        print(f"  world {i:2d}  gap={gap:.4f}  pair_flip={pf:.6f}  true={bv:.6f}  "
              f"ratio={bv/pf:.4f}  extrema {'CHANGED' if new!=old else 'same'}")
        sys.stdout.flush()

    rr = np.array([r["ratio"] for r in rows])
    ch = sum(r["extrema_changed"] for r in rows)
    print(f"\n  worlds analysed        : {len(rows)}")
    print(f"  extrema changed        : {ch}/{len(rows)}")
    print(f"  ratio true/pair_flip   : min {rr.min():.4f}  median {np.median(rr):.4f}  max {rr.max():.4f}")
    print(f"  pair_flip OVER-prices  : {(rr < 0.999).sum()}/{len(rows)}  (true min cheaper)")
    print(f"  pair_flip UNDER-prices : {(rr > 1.001).sum()}/{len(rows)}  (true min dearer)")
    print(f"  pair_flip within 0.1%  : {((rr>=0.999)&(rr<=1.001)).sum()}/{len(rows)}")
    out = ROOT / "research" / "high_risk_20260910" / "f05_generator_incidence_v1.json"
    out.write_text(json.dumps({"evidence_class": "NUMERICAL_EVIDENCE",
                               "R": R, "K": K, "k": k, "seed": seed,
                               "n_worlds": len(rows), "rows": rows}, indent=1))
    print(f"\nwritten: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
