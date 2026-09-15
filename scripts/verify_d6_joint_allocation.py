#!/usr/bin/env python3
"""Exact primal/dual certificates for D6 joint-measurement allocation.

Observation model: Y_G = F_A(1_{G union {j}}) + N(0, sigma^2), G subset U,
|G| <= r, independent noise, unit query cost. Here mu=0 and U excludes j.
We verify the oracle (known true A) max-min squared-mean-separation game,
whose value is r/(k-1) for 1 <= r <= k-1. Divide by 2*sigma^2 for KL.
This is not an end-to-end sample-complexity or novelty claim.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from verify_d6_information_limit_bridge import family_world, masks, observed_slopes


def verify(m):
    k = m // 2
    j = 1 << k
    full = (1 << m)-1
    U = full ^ j
    A = (1 << k)-1
    B = U ^ A
    labels = [a for a in masks(m, k) if not a & j]
    queries = [q for q in range(1 << m) if not q & j]
    base = family_world(m, Fraction(0), A)
    means = {}
    for a in labels:
        table = family_world(m, Fraction(0), a)
        assert observed_slopes(table, m) == observed_slopes(base, m)
        means[a] = {g: table[g | j] for g in queries}
        for g in queries:
            assert table[g | j] == (g & (U ^ a)).bit_count()-1
    alts = [a for a in labels if a != A]
    adjacent = [a for a in alts if (A ^ a).bit_count() == 2]
    assert len(adjacent) == k*(k-1)
    sq = {g: {a: (means[A][g]-means[a][g])**2 for a in alts} for g in queries}
    rows = []
    for r in range(1, k):
        legal = [g for g in queries if g.bit_count() <= r]
        design = [g for g in legal if not g & ~B and g.bit_count() == r]
        primal = {a: Fraction(sum(sq[g][a] for g in design), len(design)) for a in alts}
        dual = {g: Fraction(sum(sq[g][a] for a in adjacent), len(adjacent)) for g in legal}
        value = Fraction(r, k-1)
        assert min(primal.values()) == value
        assert max(dual.values()) == value
        assert all(primal[a] == value for a in adjacent)
        rows.append({'m': m, 'r': r, 'worlds': len(labels), 'queries': len(legal),
                     'oracle_design_queries': len(design), 'exact_squared_separation': str(value),
                     'gaussian_KL_at_variance_one': str(value/2),
                     'primal_all_alternatives': True, 'dual_all_legal_queries': True})
    # Actual support realization with a distinguished always-omitted residual coordinate:
    # F - sum_selected Q = interaction + sum_omitted Q, pointwise.
    slopes = observed_slopes(base, m)
    for x, fx in enumerate(base):
        interaction = fx-sum(slopes[i] for i in range(m) if x & (1 << i))
        for s in masks(m, k):
            left = fx-sum(slopes[i] for i in range(m) if x & s & (1 << i))
            right = interaction+sum(slopes[i] for i in range(m) if x & ~s & (1 << i))
            assert left == right
    return rows


def verify_margin_transition(m, r, mu, q_cost=Fraction(1), joint_cost=Fraction(1)):
    k = m//2
    j = 1 << k
    U = ((1 << m)-1) ^ j
    A = (1 << k)-1
    B = U ^ A
    labels = [a for a in masks(m, k) if not a & j]
    alts = [a for a in labels if a != A]
    adjacent = [a for a in alts if (A ^ a).bit_count() == 2]
    positive = [i for i in range(m) if i != k]
    groups = [g for g in range(1 << m) if not g & j and 1 <= g.bit_count() <= r]
    table = {a: family_world(m, mu, a) for a in labels}
    den = mu.denominator
    measurements = [('Q', i) for i in positive] + [('joint', g) for g in groups]
    def observed(a, query):
        kind, q = query
        return Fraction(table[a][(1 << q) if kind == 'Q' else q | j], den)
    def info(query, alt):
        c = q_cost if query[0] == 'Q' else joint_cost
        return (observed(A, query)-observed(alt, query))**2/c
    qrate = mu**2/q_cost
    jrate = r*(1-mu)**2/joint_cost
    rate = max(qrate, jrate)/((k-1)*2)
    chosen = 'Q' if qrate >= jrate else 'joint'
    design = [('Q', i) for i in positive if (1 << i) & B] if chosen == 'Q' else [
        ('joint', g) for g in groups if not g & ~B and g.bit_count() == r]
    primal = min(sum(info(q, alt) for q in design)/len(design)/2 for alt in alts)
    dual = max(sum(info(q, alt) for alt in adjacent)/len(adjacent)/2 for q in measurements)
    assert primal == rate == dual
    return {'m': m, 'r': r, 'mu': str(mu), 'q_cost': str(q_cost), 'joint_cost': str(joint_cost),
            'exact_KL_per_cost_variance_one': str(rate), 'oracle_optimal_type': chosen,
            'tie_between_types': qrate == jrate, 'primal_all_alternatives': True,
            'dual_all_measurements': True}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--m', nargs='+', type=int, default=[6, 8, 10])
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    if any(m < 6 or m % 2 for m in args.m):
        p.error('m must be even and >=6')
    rows = [row for m in args.m for row in verify(m)]
    transitions = [verify_margin_transition(m, r, mu, qc, jc)
                   for m in args.m for r in range(1, m//2)
                   for mu in map(Fraction, ['0', '1/4', '1/2', '2/3', '3/4', '1'])
                   for qc, jc in [(Fraction(1), Fraction(1)), (Fraction(1), Fraction(4))]]
    out = {'evidence_class': 'EXACT_FINITE_PRIMAL_DUAL_CERTIFICATES',
           'model': 'mu=0; known true A for oracle allocation; independent Gaussian count queries; unit cost',
           'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
           'all_widths_lean_proved': False, 'adaptive_algorithm_optimality_proved': False,
           'novelty_established': False, 'certificates': rows,
           'margin_transition_certificates': transitions}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(out, indent=2)+'\n')
    for row in rows:
        print(f'm={row["m"]} r={row["r"]}: primal=dual={row["exact_squared_separation"]}; KL={row["gaussian_KL_at_variance_one"]}')
    print(f'{len(transitions)} exact margin/cost phase certificates passed.')
    print('PASS: actual joint observations, all-alternative primal, all-query dual, actual support lift.')


if __name__ == '__main__':
    main()
