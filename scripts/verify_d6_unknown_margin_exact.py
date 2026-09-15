#!/usr/bin/env python3
"""Exact certificate at m=10, mu=1/2 with unknown alternative mu in [0,1].
All observations are evaluated from actual threshold worlds. The primal is
170/171 on uniform 4-subsets of A, 1/171 on B. The dual is uniform on the
20 adjacent hidden sets, all with alternative mu=9/19. Both equal 289/2888.
Every alternative margin is minimized as a real convex quadratic, with exact
rational minimizer clipped to [0,1]; no margin grid is used for this check.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from verify_d6_information_limit_bridge import family_world, masks


def main():
    m,k=10,5
    j=1 << k
    A=(1 << k)-1
    U=((1 << m)-1)^j
    B=U^A
    labels=[a for a in masks(m,k) if not a & j]
    alts=[a for a in labels if a != A]
    adjacent=[a for a in alts if (a^A).bit_count()==2]
    queries=[('Q',i) for i in range(m)]+[
        ('J',g) for g in range(1 << m) if not g & j and 1 <= g.bit_count() <=4]
    design={('J',B):F(1,171)}
    design.update({('J',sum(1 << i for i in group)):F(34,171)
                   for group in combinations(range(k),4)})
    assert sum(design.values())==1
    def observations(a, mu):
        table=family_world(m,mu,a)
        return {q:F(table[(1 << q[1]) if q[0]=='Q' else q[1]|j],mu.denominator) for q in queries}
    truth=observations(A,F(1,2))
    gamma=F(289,2888)
    primal=[]
    for alt in alts:
        at0,at1=observations(alt,F(1)),observations(alt,F(0))
        aa=bb=cc=F(0)
        for q,w in design.items():
            intercept=at0[q]-truth[q]
            slope=at1[q]-at0[q]
            aa+=w*slope*slope/2
            bb+=w*slope*intercept
            cc+=w*intercept*intercept/2
        lam=max(F(0),min(F(1),-bb/(2*aa))) if aa else F(0)
        value=aa*lam*lam+bb*lam+cc
        assert value>=gamma
        primal.append({'alt':alt,'distance':(alt^A).bit_count()//2,
                       'quadratic':[str(x) for x in (aa,bb,cc)],
                       'minimizing_lambda':str(lam),'minimum_KL':str(value)})
    dualobs={alt:observations(alt,F(9,19)) for alt in adjacent}
    dual={f'{q[0]}:{q[1]}':sum((truth[q]-dualobs[alt][q])**2/2 for alt in adjacent)/len(adjacent)
          for q in queries}
    assert max(dual.values())==gamma==min(F(x['minimum_KL']) for x in primal)
    # A concrete confounder for the formerly optimal all-B joint query:
    # the same response arises after one swap if lambda' changes from 1/2 to 3/4.
    confounded=observations(adjacent[0],F(1,4))
    assert truth[('J',B)]==confounded[('J',B)]==F(3,2)
    out={'evidence_class':'EXACT_RATIONAL_CONTINUOUS_NUISANCE_CERTIFICATE',
         'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
         'm':m,'true_mu':'1/2','allowed_alternative_mu':'[0,1]',
         'all_legal_measurements':len(queries),'all_alternative_hidden_sets':len(alts),
         'sharp_KL_per_unit_cost':'289/2888','known_margin_KL':'1/8',
         'primal_weight_all_B':'1/171','primal_weight_uniform_A_four_subsets':'170/171',
         'dual_adjacent_worlds':len(adjacent),'dual_margin':'9/19',
         'all_B_alone_confounded':True,'margin_grid_used':False,
         'full_Lean_measurement_allocation_bridge':False,
         'primal':primal,'dual_rates':{q:str(v) for q,v in dual.items()}}
    path=Path('research/d6_information_limit_20260908/unknown_margin_exact_m10.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(f'PASS: primal=dual={gamma}; {len(queries)} measurements, {len(alts)} alternative sets, all real margins in [0,1].')
    print('Optimal known-margin all-B measurement has ZERO discrimination when margin is unknown.')


if __name__=='__main__': main()
