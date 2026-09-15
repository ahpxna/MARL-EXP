#!/usr/bin/env python3
"""Exact finite checks for an explicit D6 family, not a Lean proof.

For m=2k>=6, partition coordinates into A (k coordinates), j (one
coordinate), and B (k-1 coordinates). With a=sum_A x, b=sum_B x, z=x_j:
    H(x) = (1-z) * 1[a>=1 or b>=2]
    F_mu(x) = (1-mu)*(b-z) + H(x),  0<=mu<=1.
The reference is the point mass at the zero corner. This script computes
responses from the evaluated table, and every k-subset's residual range
independently of the proposed closed form. Binary coordinate-derivative
spreads compute the full mixed-difference modulus in O(m*2**m).

The information game is checked at mu=0 only: permute the positive-slope
coordinates while fixing j. Its actual optimal retained sets contain j.
The finite game certificate uses the base world's checked distance formula
and coordinate-permutation equivariance, not an LP over arbitrary losses.
No claim about all widths, Lean formalization, or the full-class minimax
upper bound follows from these finite checks.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path


def masks(m, k):
    return [sum(1 << i for i in c) for c in combinations(range(m), k)]


def observed_slopes(world, m):
    return [world[1 << i] - world[0] for i in range(m)]


def all_losses(world, m, actions):
    # Each subset sum comes from the actual corner responses, not the claim.
    slopes = observed_slopes(world, m)
    sums = [0] * (1 << m)
    for x in range(1, 1 << m):
        bit = x & -x
        sums[x] = sums[x ^ bit] + slopes[bit.bit_length() - 1]
    result = {}
    for selected in actions:
        offset = selected.bit_count() * world[0]
        residual = [v - sums[x & selected] - offset for x, v in enumerate(world)]
        result[selected] = max(residual) - min(residual)
    return result


def family_world(m, mu, selected_a=None):
    k = m // 2
    j = 1 << k
    a_mask = (1 << k) - 1 if selected_a is None else selected_a
    b_mask = ((1 << m) - 1) ^ a_mask ^ j
    num, den = mu.numerator, mu.denominator
    # Store den * F_mu, so every computation below uses integers.
    return [
        (den - num) * ((x & b_mask).bit_count() - bool(x & j))
        + den * int(not (x & j) and (bool(x & a_mask) or (x & b_mask).bit_count() >= 2))
        for x in range(1 << m)
    ]


def verify_case(m, mu):
    k = m // 2
    j = 1 << k
    a_mask = (1 << k) - 1
    target = ((1 << m) - 1) ^ a_mask
    num, den = mu.numerator, mu.denominator
    world = family_world(m, mu)
    slopes = observed_slopes(world, m)
    expected_slopes = [den if i < k else (-(den-num) if i == k else den-num) for i in range(m)]
    assert slopes == expected_slopes
    derivative_intervals = []
    for i in range(m):
        bit = 1 << i
        diffs = [world[x | bit] - world[x] for x in range(1 << m) if not x & bit]
        derivative_intervals.append((min(diffs), max(diffs)))
    delta_scaled = max(hi-lo for lo, hi in derivative_intervals)
    assert delta_scaled == den
    actions = masks(m, k)
    loss = all_losses(world, m, actions)
    optimum = min(loss.values())
    assert optimum == den and loss[target] == den
    for selected, doubled in loss.items():
        d = (selected & a_mask).bit_count()
        assert doubled == den + d * (2*den-num), (m, str(mu), selected, doubled)
    top_doubled_regret = Fraction(loss[a_mask]-optimum, den)
    assert top_doubled_regret == k*(2-mu)
    return {
        'm': m, 'k': k, 'mu': str(mu), 'reference': 'point_mass_at_zero',
        'cube_points_checked': 1 << m, 'decisions_checked': len(actions),
        'delta_square_exact': str(Fraction(delta_scaled, den)),
        'response_slopes_exact': [str(Fraction(s, den)) for s in slopes],
        'minimum_doubled_loss': str(Fraction(optimum, den)),
        'top_c_doubled_regret_exact': str(top_doubled_regret),
        'all_decision_loss_identity': True,
        'scaled_world_sha256': sha256(json.dumps(world).encode()).hexdigest(),
        'doubled_losses_exact': {str(s): str(Fraction(v, den)) for s, v in loss.items()},
    }


def verify_information_game(m):
    k = m // 2
    j = 1 << k
    actions = masks(m, k)
    targets = [a for a in actions if a & j]
    positive = [i for i in range(m) if i != k]
    base = family_world(m, Fraction(0))
    expected_q = [base[0]] + observed_slopes(base, m)
    # Each adjacent transposition in the positive-coordinate list is a
    # generator of the entire admissible permutation group.
    for i, l in zip(positive, positive[1:]):
        def swap(x):
            return x ^ ((1 << i) | (1 << l)) if bool(x & (1 << i)) != bool(x & (1 << l)) else x
        permuted = [base[swap(x)] for x in range(1 << m)]
        assert [permuted[0]] + observed_slopes(permuted, m) == expected_q
    value = Fraction(k*(k-1), 2*k-1)
    # Uniform adversary: a lower bound against EVERY pure action, hence
    # against every mixture. Uniform feasible strategy: matching upper bound
    # on this constructed family. Neither checks the full-class upper bound.
    numerators = [sum((s & ~t).bit_count() for t in targets) for s in actions]
    assert min(numerators) == value * len(targets)
    for t in targets:
        assert sum((s & ~t).bit_count() for s in targets) == value * len(targets)
    # Negative control: same response profile does not by itself imply the
    # distance formula. An additive world has the same Q and zero regret.
    slopes = observed_slopes(base, m)
    additive = [sum(slopes[i] for i in range(m) if x & (1 << i)) for x in range(1 << m)]
    assert observed_slopes(additive, m) == slopes
    additive_losses = all_losses(additive, m, actions)
    assert len(set(additive_losses.values())) == 1
    return {
        'm': m, 'world_labels': len(targets), 'all_algorithm_actions': len(actions),
        'optimal_retained_sets_contain_coordinate': k,
        'exact_constructed_game_value': str(value),
        'uniform_adversary_checked_against_all_actions': True,
        'matching_uniform_strategy_checked': True,
        'same_full_corner_profile_under_all_group_generators': True,
        'negative_control_same_profile_but_zero_regret': True,
        'bridge_scope': 'base-world exhaustive loss verification plus coordinate-permutation equivariance',
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--m', nargs='+', type=int, default=[6, 8, 10, 12])
    p.add_argument('--mu', nargs='+', type=Fraction, default=[Fraction(0), Fraction(1,2), Fraction(1)])
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    if any(m < 6 or m % 2 for m in args.m):
        p.error('m must be even and at least 6')
    if any(mu < 0 or mu > 1 for mu in args.mu):
        p.error('mu must lie in [0,1]')
    cases = []
    for m in args.m:
        for mu in args.mu:
            row = verify_case(m, mu)
            cases.append(row)
            print(f'm={m} mu={mu}: every k-subset checked; 2*TopC regret={row["top_c_doubled_regret_exact"]}', flush=True)
    # Ensure the representative mu=0 world is checked even if omitted in CLI.
    if Fraction(0) not in args.mu:
        cases.extend(verify_case(m, Fraction(0)) for m in args.m)
    games = [verify_information_game(m) for m in args.m]
    out = {
        'evidence_class': 'EXACT_INTEGER_FINITE_CHECKS_AND_FINITE_GAME_CERTIFICATES',
        'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'all_widths_lean_proved': False, 'full_class_minimax_solved': False,
        'frontier_cases': cases, 'information_games_at_mu_zero': games,
    }
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(games, indent=2))
    print('PASS: all requested finite checks; no all-width Lean claim.')


if __name__ == '__main__':
    main()
