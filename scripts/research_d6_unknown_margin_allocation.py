#!/usr/bin/env python3
"""Numerical, symmetry-reduced allocation with unknown D6 margin.

All possible alternative margins lie in [0,1]. For each alternative hidden-set
orbit d and each measurement orbit under permutations within the true A/B,
the squared difference of actual world observations is an exact quadratic in
lambda'=1-mu'. Minimize that quadratic analytically, then maximize the worst
rate over allocations. This is an oracle characteristic-value calculation,
not a learning algorithm and not an all-width Lean theorem.
A finite adversary mixture supplies an independent numerical upper bound.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize, linprog
from verify_d6_information_limit_bridge import family_world


def analyze(m, r, mu, joint_cost, include_unanchored=False):
    k = m//2
    Acoords = list(range(k))
    jidx = k
    Bcoords = list(range(k+1, m))
    A = (1 << k)-1
    j = 1 << jidx
    def mask(group): return sum(1 << i for i in group)
    orbits = [('Q_A', [('Q', i) for i in Acoords], 1),
              ('Q_B', [('Q', i) for i in Bcoords], 1),
              ('Q_j', [('Q', jidx)], 1)]
    for s in range(r+1):
        for t in range(r+1-s):
            if s+t == 0 or s > k or t > k-1: continue
            group = [('J', mask(a)|mask(b)) for a in combinations(Acoords, s)
                     for b in combinations(Bcoords, t)]
            orbits.append((f'J_A{s}_B{t}', group, joint_cost))
            if include_unanchored and s+t >= 2:
                plain = [('J0', mask(a)|mask(b)) for a in combinations(Acoords, s)
                         for b in combinations(Bcoords, t)]
                orbits.append((f'J0_A{s}_B{t}', plain, joint_cost))
    truth = family_world(m, Fraction(str(mu)), A)
    den = Fraction(str(mu)).denominator
    def observation(table, query):
        kind, q = query
        return table[(1 << q) if kind == 'Q' else (q if kind == 'J0' else q | j)]
    coeff = []
    for d in range(1, k):
        altA = (A ^ mask(Acoords[:d])) | mask(Bcoords[:d])
        at0 = family_world(m, Fraction(1), altA)  # lambda'=0
        at1 = family_world(m, Fraction(0), altA)  # lambda'=1
        row = []
        for name, queries, cost in orbits:
            a0 = np.array([observation(at0, q) for q in queries], dtype=float)
            b0 = np.array([observation(at1, q) for q in queries], dtype=float)-a0
            target = np.array([observation(truth, q)/den for q in queries])
            u = a0-target
            row.append([np.mean(b0*b0)/(2*cost), np.mean(2*b0*u)/(2*cost),
                        np.mean(u*u)/(2*cost)])
        coeff.append(row)
    coeff = np.array(coeff)
    D, E, _ = coeff.shape
    def evaluate(w):
        aa, bb, cc = (coeff[:, :, idx] @ w for idx in range(3))
        lam = np.divide(-bb, 2*aa, out=np.zeros(D), where=aa > 1e-14)
        lam = np.clip(lam, 0, 1)
        vals = aa*lam**2+bb*lam+cc
        gradient = coeff[:, :, 0]*lam[:, None]**2 + coeff[:, :, 1]*lam[:, None]+coeff[:, :, 2]
        return vals, gradient, lam
    def cons(v): return evaluate(v[:-1])[0]-v[-1]
    def jac(v): return np.column_stack((evaluate(v[:-1])[1], -np.ones(D)))
    result = minimize(lambda v: -v[-1], np.r_[np.ones(E)/E, 0.0],
        jac=lambda v: np.r_[np.zeros(E), -1.0], method='SLSQP',
        bounds=[(0, 1)]*E+[(0, None)],
        constraints=[{'type':'eq', 'fun':lambda v: v[:-1].sum()-1,
                      'jac':lambda v: np.r_[np.ones(E), 0]},
                     {'type':'ineq', 'fun':cons, 'jac':jac}],
        options={'ftol':1e-12, 'maxiter':4000})
    # A boundary optimum can trigger SLSQP status 8 despite a valid design.
    # Accept only if the independent primal/dual certificate below closes.
    if not result.success and result.status != 8: raise RuntimeError(result.message)
    w = np.maximum(result.x[:-1], 0)
    w /= w.sum()
    vals, matrix, lambdas = evaluate(w)
    # Dual distribution over the most confusing alternatives, averaged within
    # each hidden-set orbit; matrix already includes every query in each orbit.
    lp = linprog(np.r_[np.zeros(D), 1.0],
        A_ub=np.column_stack((matrix.T, -np.ones(E))), b_ub=np.zeros(E),
        A_eq=np.array([np.r_[np.ones(D), 0]]), b_eq=[1],
        bounds=[(0,None)]*D+[(None,None)], method='highs')
    if not lp.success: raise RuntimeError(lp.message)
    q = np.maximum(lp.x[:D], 0); q /= q.sum()
    lower, upper = float(vals.min()), float((q @ matrix).max())
    if not np.isfinite([lower, upper]).all() or upper-lower > 1e-7 or upper-lower < -1e-8:
        raise RuntimeError(f'Unclosed numerical primal/dual certificate: {lower=}, {upper=}; {result.message}')
    known = max(mu**2, r*(1-mu)**2/joint_cost)/(2*(k-1))
    return {'m':m, 'r':r, 'mu':mu, 'joint_cost':joint_cost,
            'unknown_margin_lower':lower, 'unknown_margin_upper':upper,
            'numerical_certificate_gap':upper-lower, 'known_margin_value':known,
            'include_unanchored':include_unanchored,
            'solver_success':bool(result.success),'solver_status':int(result.status),
            'solver_message':str(result.message),
            'allocation_cost_fractions':{orbits[e][0]:float(w[e]) for e in range(E) if w[e]>1e-6},
            'worst_alternative_margin_by_distance':(1-lambdas).tolist(),
            'dual_alternative_orbit_weights':q.tolist(),
            'single_orbit_rates':{orbits[e][0]:float(evaluate(np.eye(E)[e])[0].min()) for e in range(E)}}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--m', type=int, default=10)
    p.add_argument('--r', type=int, default=4)
    p.add_argument('--mu', nargs='+', type=float, default=[0, .25, .5, 2/3, .75, .9, 1])
    p.add_argument('--include-unanchored', action='store_true',
                   help='Also allow joint queries without the distinguished coordinate j.')
    p.add_argument('--joint-cost', type=float, default=1)
    p.add_argument('--out', type=Path, required=True)
    a=p.parse_args()
    rows=[analyze(a.m,a.r,mu,a.joint_cost,a.include_unanchored) for mu in a.mu]
    for row in rows:
        print(json.dumps(row), flush=True)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps({'evidence_class':'NUMERICAL_ORBIT_PRIMAL_DUAL_BOUNDS',
        'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'unknown_margin_formal_theorem':False, 'rows':rows},indent=2)+'\n')


if __name__=='__main__': main()
