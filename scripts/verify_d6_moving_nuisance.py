#!/usr/bin/env python3
"""Verify the moving-nuisance midpoint on actual world tables and re-evaluate
existing growing-q results. No Monte Carlo rerun. Exact rational checks are
independent of the allocation polynomial. Growing-q oracle rates remain numerical.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information
from verify_d6_information_limit_bridge import family_world


def verify(q):
    m=2*(q+1); A=(1<<(q+1))-1; j=1<<(q+1)
    B=((1<<m)-1)^A^j
    groups=[g for g in range(1<<m) if not g&j and g.bit_count()<=q]
    queries=[1<<i for i in range(m)]+[g|j for g in groups]+[g for g in groups if g.bit_count()>=2]
    mu,nu,eps=F(13,20),F(3,5),F(1,100)
    def world(label,x): return [F(v,x.denominator) for v in family_world(m,x,label)]
    truth=[world(A,mu+s*eps) for s in [-1,0,1]]
    ncheck=0; maxrelative=F(0)
    for a in range(q+1):
        for b in range(q+2,m):
            alt=A^(1<<a)^(1<<b)
            alternatives=[world(alt,nu+s*eps) for s in [-1,0,1]]
            for e in queries:
                minus=truth[0][e]-alternatives[0][e]
                center=truth[1][e]-alternatives[1][e]
                plus=truth[2][e]-alternatives[2][e]
                rel=(plus-minus)/(2*eps)
                assert rel*rel<=1
                assert (minus*minus+plus*plus)/2==center*center+eps*eps*rel*rel
                maxrelative=max(maxrelative,rel*rel);ncheck+=1
    return dict(q=q,exact_rational_query_swap_checks=ncheck,max_relative_slope_squared=str(maxrelative))


def main():
    base=Path('research/d6_phase_boundary_20260908')
    src=base/'growing_q_pilot.json';old=json.loads(src.read_text())
    checks=[verify(q) for q in [3,4,5]]
    rows=[]
    for row in old['rows']:
        q,eps=row['q'],row['epsilon']; p=phase_parameters(q)
        gs=[information(q,p['mu_U']+s*eps,oracle(q,p['mu_U']+s*eps,p))[0] for s in [-1,1]]
        nu0=1-(1-p['mu_U'])*p['T']
        assert 0<=nu0-eps<=nu0+eps<=1
        sep=max(0.,sum(gs)-2*p['gamma_boundary']-eps*eps)
        refined=sep*row['known_label_error']
        upper=max(s['achievable_risk_upper'] for s in row['sides']) if row['pilot_fits'] else None
        if upper is not None: assert refined<=upper+1e-10
        rows.append(dict(q=q,N=row['N'],epsilon=eps,pilot_fraction=row['pilot_fraction'],
            coarse_lower_over_leading=row['coarse_separation_over_Jepsilon'],
            moving_lower_over_leading=refined/row['leading'],
            unknown_A_upper_over_leading=upper/row['leading'] if upper is not None else None,
            moving_lower=refined,unknown_A_upper=upper))
    out=base/'moving_nuisance_evidence.json'
    out.write_text(json.dumps(dict(script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        growing_q_input_sha256=sha256(src.read_bytes()).hexdigest(),exact_table_checks=checks,rows=rows,
        scope=['Moving true and alternative margins together gives relative adjacent-world slope at most 1.',
        'All actual legal queries checked in rational arithmetic for q=3,4,5.',
        'The lower expression is Gamma_minus+Gamma_plus-2*Gamma0-epsilon^2.',
        'Oracle formulas and growing-q uniform asymptotics still need complete certification.',
        'Unknown-A upper is for the concrete pilot, not a matching discovery lower bound.']),indent=2)+'\n')
    print(checks)
    for row in rows:
        if row['N']==8192*row['q']: print(row)
    print(out)

if __name__=='__main__':main()
