"""Exact finite menu--tolerance curve; no floating point optimization.

Enumerates all permutations, forms their covered-budget masks, and solves
minimum set cover by DP over the (m+1)-bit budget universe. The artifact is
finite exhaustive evidence, not a Lean proof or an asymptotic family result.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import combinations, permutations
import hashlib
import json
from pathlib import Path


def run(weights):
    weights = tuple(weights)
    m = len(weights)
    if not 1 <= m <= 8:
        raise ValueError('Exhaustive runner supports 1..8 components')
    total, scale = sum(weights), sum(map(abs, weights))
    if not scale:
        raise ValueError('Normalization requires nonzero total component radius')
    optimum = [min(abs(total-sum(weights[i] for i in s))
                   for s in combinations(range(m), k)) for k in range(m+1)]
    profiles = []
    for ranking in permutations(range(m)):
        partial, excess = 0, [0]
        for k, i in enumerate(ranking, 1):
            partial += weights[i]
            excess.append(abs(total-partial)-optimum[k])
        assert all(x >= 0 for x in excess)
        profiles.append((ranking, tuple(excess)))
    thresholds = sorted({x for _, p in profiles for x in p})
    full = (1 << (m+1))-1
    curve = []
    previous = None
    for threshold in thresholds:
        representatives = {}
        for ranking, excess in profiles:
            mask = sum(1 << k for k, x in enumerate(excess) if x <= threshold)
            representatives.setdefault(mask, ranking)
        maximal = [a for a in representatives
                   if not any(a != b and a | b == b for b in representatives)]
        dp = {0: []}
        for covered in range(full+1):
            if covered not in dp:
                continue
            for mask in maximal:
                nxt = covered | mask
                if nxt not in dp or len(dp[nxt]) > len(dp[covered])+1:
                    dp[nxt] = dp[covered]+[representatives[mask]]
        witnesses = dp[full]
        covered = 0
        for ranking in witnesses:
            partial = 0
            for k in range(m+1):
                if k:
                    partial += weights[ranking[k-1]]
                if abs(total-partial)-optimum[k] <= threshold:
                    covered |= 1 << k
        assert covered == full
        if len(witnesses) != previous:
            curve.append(dict(epsilon=str(Fraction(threshold,scale)),
                              excess_numerator=threshold, minimum_rankings=len(witnesses),
                              witness_rankings=witnesses,
                              maximal_coverage_masks=maximal,
                              distinct_coverage_masks=len(representatives)))
            previous = len(witnesses)
    return dict(evidence_class='EXHAUSTIVE_FINITE_INTEGER_COMPUTATION',
                theorem_scope='Single finite two-support-point scalar instance only',
                normalization='Divide original functions by sum(abs(weights))/2; total component radius equals 1',
                weights=weights, excess_denominator=scale,
                optimum_absolute_omitted_sum=optimum,
                permutations_enumerated=len(profiles), thresholds_evaluated=len(thresholds),
                intervals='Each row applies from its epsilon inclusively to the next epsilon exclusively',
                curve=curve, lean_proof=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--weights', type=int, nargs='+', default=[-32,7,29,-7,-8,-13,18])
    parser.add_argument('--out', default='research/structural_tolerance_20260910/scalar_chi5_exact_curve.json')
    args = parser.parse_args()
    result = run(args.weights)
    result['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['evidence_class','permutations_enumerated','curve']},indent=2))

if __name__ == '__main__':
    main()
