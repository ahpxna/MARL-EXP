#!/usr/bin/env python3
"""Exact algebraic certificate for unknown-margin D6 with both joint query types.

Rational true mu in the proposed interior regime, m=2(q+1), q>=3, unit-cost independent variance-one Gaussian
measurements. Library: every scalar Q_i and every nonempty G in U of size <=q
with j on; additionally every G of size 2..q with j off. Singletons with j off
are already Q_i. This is NOT unrestricted cube access: |G|<=q is retained.
Primal and dual evaluate actual construction tables, not orbit-polynomial
assumptions. Nuisance lambda is minimized over the continuous interval [0,1].
"""
import argparse
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sympy as sp
from verify_d6_information_limit_bridge import family_world, masks
from fractions import Fraction


def certify(m, mu=Fraction(1,2)):
    k,q=m//2,m//2-1
    assert m%2==0 and q>=3
    A=(1<<k)-1
    j=1<<k
    U=((1<<m)-1)^j
    B=U^A
    groups=[g for g in range(1<<m) if not g&j and 1<=g.bit_count()<=q]
    queries=[('Q',i) for i in range(m)]+[('J',g) for g in groups]+[
        ('J0',g) for g in groups if g.bit_count()>=2]
    alternatives=[a for a in masks(m,k) if not a&j and a!=A]
    adjacent=[a for a in alternatives if (a^A).bit_count()==2]
    c=sp.sqrt(sp.Rational(q,q+1))
    w=sp.simplify(c/(q-2+c))
    lam=sp.Rational(1)-sp.Rational(mu.numerator,mu.denominator)
    nu=sp.simplify(lam*(q-1)/(q-2+c))
    gamma=sp.simplify(lam**2*c*c*(q-1)**2/(2*(q-2+c)**2))
    assert 0<w<1 and 0<=nu<=1
    Aqueries=[('J0',sum(1<<i for i in group)) for group in combinations(range(k),q)]
    design={('J',B):w, **{g:(1-w)/k for g in Aqueries}}
    def obs(table, query):
        kind,g=query
        return table[(1<<g) if kind=='Q' else (g|j if kind=='J' else g)]
    truth=family_world(m,mu,A)
    den=mu.denominator
    kl_den=2*den*den
    # Endpoint tables are integral; actual truth table is scaled by its exact rational denominator.
    endpoint_tables={a:(family_world(m,Fraction(1),a),family_world(m,Fraction(0),a))
                     for a in alternatives}
    @lru_cache(None)
    def sign(expr):
        expr=sp.simplify(expr)
        result=sp.sign(expr)
        assert result in (-1,0,1), (expr,result)
        return int(result)
    @lru_cache(None)
    def minimum(signature):
        # Separate the B query and uniform-A orbit before algebraic operations.
        coeff=[]
        for n in range(3):
            coeff.append(sp.simplify(w*sp.Rational(signature[n],kl_den) +
                         (1-w)*sp.Rational(signature[n+3],kl_den*k)))
        aa,bb,cc=coeff
        at=sp.simplify(-bb/(2*aa)) if sign(aa)>0 else sp.Integer(0)
        at=sp.Integer(0) if sign(at)<0 else (sp.Integer(1) if sign(at-1)>0 else at)
        value=sp.simplify(aa*at**2+bb*at+cc)
        assert sign(value-gamma)>=0, (signature,value,gamma)
        return {'quadratic':[str(x) for x in coeff], 'minimizing_lambda':str(at),
                'minimum_KL':str(value), 'equals_gamma':sign(value-gamma)==0}
    primal_by_distance={}
    for alt in alternatives:
        at0,at1=endpoint_tables[alt]
        signature=[]
        for orbit in [[('J',B)],Aqueries]:
            aa=bb=cc=0
            for g in orbit:
                u=den*obs(at0,g)-obs(truth,g)
                v=den*(obs(at1,g)-obs(at0,g))
                aa+=v*v; bb+=2*u*v; cc+=u*u
            signature.extend((aa,bb,cc))
        cert=minimum(tuple(signature))
        distance=(alt^A).bit_count()//2
        if distance in primal_by_distance: assert primal_by_distance[distance]==cert
        primal_by_distance[distance]=cert
    @lru_cache(None)
    def dual_value(aa,bb,cc):
        value=sp.simplify((aa*nu**2+bb*nu+cc)/(kl_den*len(adjacent)))
        assert sign(gamma-value)>=0, (value,gamma)
        return value
    dual_orbits={}
    for g in queries:
        aa=bb=cc=0
        for alt in adjacent:
            at0,at1=endpoint_tables[alt]
            u=den*obs(at0,g)-obs(truth,g)
            v=den*(obs(at1,g)-obs(at0,g))
            aa+=v*v; bb+=2*u*v; cc+=u*u
        value=dual_value(aa,bb,cc)
        kind,mask=g
        name=(f'Q:{"j" if 1<<mask==j else "A" if (1<<mask)&A else "B"}' if kind=='Q'
              else f'{kind}:A{(mask&A).bit_count()}:B{(mask&B).bit_count()}')
        if name in dual_orbits: assert dual_orbits[name]==str(value)
        dual_orbits[name]=str(value)
    assert primal_by_distance[1]['equals_gamma']
    assert sign(sp.sympify(dual_orbits[f'J:A0:B{q}'])-gamma)==0
    assert sign(sp.sympify(dual_orbits[f'J0:A{q}:B0'])-gamma)==0
    return {'m':m,'q':q,'true_mu':str(mu),'actual_measurements_checked':len(queries),
            'alternative_sets_checked':len(alternatives),'dual_adjacent_sets':len(adjacent),
            'gamma_exact':str(gamma),'gamma_decimal':float(gamma),
            'all_B_anchored_weight':str(w),'uniform_A_unanchored_weight':str(sp.simplify(1-w)),
            'dual_alternative_lambda':str(nu),'primal_by_distance':primal_by_distance,
            'dual_orbits':dual_orbits,'PASS':True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--case',nargs='+',default=['8:1/10','8:3/5','10:1/25','10:3/5','12:13/20'],help='m:mu as rational, e.g. 10:3/5')
    p.add_argument('--out',type=Path,default=Path('research/d6_information_limit_20260908/margin_regime_exact.json'))
    args=p.parse_args()
    rows=[]
    for case in args.case:
        m,mu=case.split(':'); m=int(m); mu=Fraction(mu)
        row=certify(m,mu); rows.append(row)
        print(f'PASS m={m}, mu={mu}: Gamma={row["gamma_exact"]}; {row["actual_measurements_checked"]} queries, {row["alternative_sets_checked"]} alternatives, continuous nuisance.',flush=True)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps({'evidence_class':'EXACT_MARGIN_REGIME_ACTUAL_WORLD_CERTIFICATE',
        'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'query_size_bound':'|G| <= k-1','alternative_mu':'[0,1]',
        'margin_grid_for_alternatives':False,'rows':rows},indent=2)+'\n')


if __name__=='__main__': main()
