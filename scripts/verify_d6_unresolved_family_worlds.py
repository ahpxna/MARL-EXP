#!/usr/bin/env python3
"""Check unresolved-family orbit quadratics against literal constructed worlds."""
import itertools,json
from fractions import Fraction
from pathlib import Path
from hashlib import sha256
import numpy as np
from experiment_d6_unresolved_label_family import arrays
from verify_d6_information_limit_bridge import family_world

def masks(items,k):
    return [sum(1<<i for i in z) for z in itertools.combinations(items,k)]

def verify(q,r):
    m=2*(q+1);j=q+1
    coords=[i for i in range(m) if i!=j]
    C=coords[:q+1-r];D=coords[len(C):len(C)+q-r]
    U=coords[len(C)+len(D):];UA=U[:r];UB=U[r:]
    A=sum(1<<i for i in C+UA);mu=Fraction(13,20)
    truth=np.asarray(family_world(m,mu,A),float)/mu.denominator
    aa,bb,cc,groups=arrays(q,r,float(mu));orbits=[]
    for g in groups:
        if g[0]=='s':idx=[1<<i for i in [C,D,U,[j]][g[1]]]
        else:
            _,s,t,u,h=g;idx=[a|b|c|(h<<j) for a in masks(C,s) for b in masks(D,t) for c in masks(U,u)]
        assert idx;orbits.append(idx)
    alts=[(c,d,a,b) for c in range(len(C)+1) for d in range(len(D)+1)
          for a in range(r+1) for b in range(r+1) if c+d+a+b==q+1 and (c,d,a,b)!=(len(C),0,r,0)]
    error=0.;checks=0
    for row,(c,d,a,b) in enumerate(alts):
        alt=sum(1<<i for i in C[:c]+D[:d]+UA[:a]+UB[:b])
        f0=np.asarray(family_world(m,Fraction(0),alt),float)
        f1=np.asarray(family_world(m,Fraction(1),alt),float)
        diff=truth-f0;slope=f0-f1
        for col,idx in enumerate(orbits):
            actual=[float(np.mean(slope[idx]**2)),float(np.mean(2*diff[idx]*slope[idx])),float(np.mean(diff[idx]**2))]
            expected=[aa[row,col],bb[row,col],cc[row,col]]
            error=max(error,max(abs(a-b) for a,b in zip(actual,expected)))
            checks+=len(idx)
    assert error<3e-13,(q,r,error)
    return dict(q=q,r=r,query_world_pairs=checks,orbit_quadratics=len(alts)*len(groups),max_coefficient_error=error)

def main():
    rows=[verify(q,r) for q,r in [(3,1),(3,2),(3,3),(4,2)]]
    p=Path('research/d6_phase_boundary_20260908/unresolved_family_world_check.json')
    p.write_text(json.dumps(dict(rows=rows,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        experiment_sha256=sha256(Path('scripts/experiment_d6_unresolved_label_family.py').read_bytes()).hexdigest(),
        scope='Every query within every orbit, representative of every alternative orbit, at rational mu=13/20; literal world tables.'),indent=2)+'\n')
    print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
