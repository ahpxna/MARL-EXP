#!/usr/bin/env python3
"""P26 v2: Top-1 instrument-cost sensitivity, explicitly a SIDE model.

Infeasible setup budgets are never replaced by positive sample budgets. Contrast
allocations have a closed form; scalar allocations remain numerical candidates.
The pairwise variance threshold 4 is not a multi-alternative theorem.
Outputs are versioned and exclusive: no historical artifact is overwritten.
"""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

OUT = 'research/worker_P26_functional_corrected_20260915/P26_functional_contrast_cost_v2.json'


def sample_budget(total, setup, channels):
    total, setup = F(str(total)), F(str(setup))
    assert total >= 0 and setup >= 0 and channels >= 0
    remaining = total - setup * channels
    if remaining < 0:
        return {'status': 'INFEASIBLE_SETUP', 'sample_budget': None,
                'setup_cost': float(setup * channels)}
    return {'status': 'NO_SAMPLING_BUDGET' if remaining == 0 else 'FEASIBLE',
            'sample_budget': float(remaining), 'setup_cost': float(setup * channels)}


def scalar_value(w, theta):
    if np.any(w <= 0):
        return 0.0
    return min((theta[0] - theta[j])**2 / (2 * (1/w[0] + 1/w[j]))
               for j in range(1, len(theta)))


def scalar_candidate(theta):
    """A feasible lower bound; no global-optimum certificate is claimed."""
    rng = np.random.default_rng(20260915)
    def weights(z):
        w = np.abs(z) + 1e-14
        return w / w.sum()
    starts = [np.ones(len(theta))] + [rng.random(len(theta)) + .1 for _ in range(30)]
    best_w = weights(starts[0])
    best_value = scalar_value(best_w, theta)
    successes = 0
    for z in starts:
        result = minimize(lambda z: -scalar_value(weights(z), theta), z,
                          method='Nelder-Mead',
                          options={'maxiter': 60000, 'maxfev': 60000,
                                   'xatol': 1e-12, 'fatol': 1e-14})
        successes += int(result.success)
        w = weights(result.x)
        value = scalar_value(w, theta)
        if np.isfinite(value) and value > best_value:
            best_w, best_value = w, value
    return {'value_lower_bound_numerical': float(best_value),
            'weights': best_w.tolist(), 'converged_starts': successes,
            'starts': len(starts), 'global_optimality_certified': False}


def scaled_information(budget, unit_value):
    return (None if budget['sample_budget'] is None
            else budget['sample_budget'] * unit_value)


def ratio(a, b):
    return a / b if a is not None and b is not None and b > 0 else None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', default=OUT)
    args = parser.parse_args()
    path = Path(args.out)
    if path.exists():
        raise SystemExit(f'Refusing to overwrite {path}')
    rows = []
    for k in (3, 4, 5):
        theta = np.array([1.] + [1. - .3 * (i+1) for i in range(k-1)])
        gaps = theta[0] - theta[1:]
        # max min_j gap_j^2*w_j/2, sum_j w_j=1: all constraints equal.
        unit_contrast = float(1 / (2 * np.sum(1 / gaps**2)))
        scalar = scalar_candidate(theta)
        unit_scalar_lower = scalar['value_lower_bound_numerical']
        for setup in (0., .1, .3):
            ba = sample_budget(1., setup, k-1)
            bc = sample_budget(1., setup, k)
            va = scaled_information(ba, unit_contrast)
            vb = scaled_information(ba, unit_contrast / 4)  # price 2, variance 2
            vc = scaled_information(bc, unit_scalar_lower)
            # D controls the remaining budget, matching C; it is NOT A's setup model.
            sweep = {str(v): scaled_information(bc, unit_contrast / v)
                     for v in (1., 2., 4., 8.)}
            d_ratios = {v: ratio(info, vc) for v, info in sweep.items()}
            rows.append({
                'K': k, 'setup_per_channel': setup,
                'A_budget': ba, 'B_budget': ba, 'C_budget': bc, 'D_budget': bc,
                'A_primitive_contrast': va, 'B_two_reads_discarded': vb,
                'C_retained_scalar_candidate_lower': vc,
                'scalar_unit_candidate': scalar,
                'A_over_C_candidate': ratio(va, vc),
                'D_information_by_variance': sweep,
                'D_over_C_candidate_by_variance': d_ratios,
                'D_break_even_against_candidate': d_ratios['1.0'],
                'comparison_certified_against_scalar_optimum': False,
            })
    result = {
        'script': 'P26_functional_contrast_cost.py', 'version': 2,
        'model_scope': 'Top-1 identification; no transfer to group-range Functional',
        'rows': rows,
        'reading': 'Setup feasibility is checked before information is computed. '
                   'A and C pay their own support setup; D matches the remaining '
                   'sample budget of C to isolate contrast variance. The two-cell '
                   'unit-variance threshold 4 does not apply to all alternatives. '
                   'The scalar optimiser supplies only a numerical feasible lower '
                   'bound: D/C_candidate is not a certificate that D beats Gamma_C.',
        'not_established': ['The real instrument noise and setup cost.',
                            'The global scalar optimum or a certified break-even.',
                            'The actual group-range alternative oracle (F5).'],
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print(f'{len(rows)} rows written to {path}; infeasible cells remain explicit')


if __name__ == '__main__':
    main()
