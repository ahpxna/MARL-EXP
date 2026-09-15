#!/usr/bin/env python3
"""Actual-D6 Gaussian joint-query experiment with one common stopping rule.

Finite hypotheses are the mu=0 threshold worlds. Query G observes the actual
F_A(1_{G union {j}})+N(0,sigma^2). The learner knows the family, j and variance.
Adaptive policy: MLE plug-in oracle design, uniform r-subsets of estimated B,
with sqrt(t) forced singleton queries cycling across U. Oracle mode is an
explicit unattainable benchmark that knows A. Uniform mode samples r-subsets
of U. All use the same likelihood-ratio threshold log((M-1)/delta).
For finite simple hypotheses this stopping rule is time-uniform: a wrong
answer crosses a true-vs-wrong likelihood-ratio martingale boundary; Ville
plus the union bound gives error <=delta under the stated Gaussian model.
The script is experimental evidence, not a Lean statistical proof.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
import math
from pathlib import Path
import numpy as np
from verify_d6_information_limit_bridge import family_world, masks


def setup(m, r):
    k = m//2
    j = 1 << k
    U = [i for i in range(m) if i != k]
    labels = [a for a in masks(m, k) if not a & j]
    queries = sorted(set(1 << i for i in U) | {
        sum(1 << i for i in group) for group in combinations(U, r)})
    lookup = {g: idx for idx, g in enumerate(queries)}
    means = np.array([[family_world(m, Fraction(0), a)[g | j] for g in queries]
                      for a in labels], dtype=float)
    designs = [[lookup[g] for g in queries if g.bit_count() == r and not g & a]
               for a in labels]
    uniform = [idx for idx, g in enumerate(queries) if g.bit_count() == r]
    return labels, means, designs, uniform, [lookup[1 << i] for i in U]


def trial(data, r, sigma, delta, seed, max_steps, mode):
    labels, means, designs, uniform, singletons = data
    truth_rng = np.random.default_rng(seed)
    truth = int(truth_rng.integers(len(labels)))
    policy_rng = np.random.default_rng(seed+10_000_000)
    noise_rng = np.random.default_rng(seed+20_000_000)
    scores = np.zeros(len(labels))
    threshold = math.log((len(labels)-1)/delta)
    forced = 0
    for t in range(1, max_steps+1):
        nominee = int(np.argmax(scores))
        if mode == 'adaptive' and forced < math.isqrt(t):
            query = singletons[forced % len(singletons)]
            forced += 1
        else:
            pool = uniform if mode == 'uniform' else designs[truth if mode == 'oracle' else nominee]
            query = int(policy_rng.choice(pool))
        mu = means[:, query]
        y = mu[truth] + sigma*noise_rng.standard_normal()
        scores += (y*mu-mu*mu/2)/(sigma*sigma)
        best = int(np.argmax(scores))
        second = np.partition(scores, -2)[-2]
        if scores[best]-second >= threshold:
            return {'steps': t, 'stopped': True, 'correct': best == truth,
                    'forced': forced, 'true_label': labels[truth], 'answer_label': labels[best]}
    return {'steps': max_steps, 'stopped': False, 'correct': None, 'forced': forced,
            'true_label': labels[truth], 'answer_label': None}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--m', nargs='+', type=int, default=[6, 10])
    p.add_argument('--delta', nargs='+', type=float, default=[0.05, 0.001, 0.000001])
    p.add_argument('--sigma', type=float, default=1.0)
    p.add_argument('--seeds', type=int, default=100)
    p.add_argument('--seed-start', type=int, default=840100)
    p.add_argument('--max-steps', type=int, default=20000)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    if any(m < 6 or m % 2 for m in a.m) or not a.sigma > 0 or a.seeds < 1:
        p.error('even m>=6, sigma>0 and seeds>=1 required')
    if any(not 0 < d < 1 for d in a.delta):
        p.error('delta must lie strictly between zero and one')
    records = []
    for m in a.m:
        for r in sorted({1, m//2-1}):
            data = setup(m, r)
            for delta in a.delta:
                for mode in ['adaptive', 'uniform', 'oracle']:
                    runs = [trial(data, r, a.sigma, delta, seed, a.max_steps, mode)
                            for seed in range(a.seed_start, a.seed_start+a.seeds)]
                    steps = np.array([x['steps'] for x in runs])
                    row = {'m': m, 'r': r, 'delta': delta, 'sigma': a.sigma, 'mode': mode,
                           'n': a.seeds, 'stopped': sum(x['stopped'] for x in runs),
                           'errors': sum(x['correct'] is False for x in runs),
                           'mean_capped_steps': float(steps.mean()),
                           'median_capped_steps': float(np.median(steps)),
                           'asymptotic_oracle_leading_term': 2*a.sigma**2*(m//2-1)/r*math.log(1/delta),
                           'runs': runs}
                    records.append(row)
                    print(f'm={m} r={r} delta={delta:g} {mode}: mean={steps.mean():.1f}; '
                          f'stopped={row["stopped"]}/{a.seeds}; errors={row["errors"]}', flush=True)
    output = {'script_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'known_family': True, 'oracle_benchmark_uses_truth': True,
              'adaptive_policy_uses_truth': False, 'common_stopping_rule': True,
              'all_width_lean_allocation_proof': False,
              'adaptive_asymptotic_optimality_lean_proof': False,
              'seed_start': a.seed_start, 'records': records}
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
