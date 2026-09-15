#!/usr/bin/env python3
"""80-digit deterministic checks for frozen allocations, all alternative distances.
The exact orbit identities have separate Lean proofs. These numerical checks
locate usable neighborhoods and quantify finite-epsilon remainders; no seeds.
"""
from decimal import Decimal as D, getcontext
from pathlib import Path
from hashlib import sha256
import json, math
getcontext().prec=80

def run(qi,fraction):
    q=D(qi);c=(q/(q+1)).sqrt();z=(1-c)/(q-2+c);T=1+z
    R=((q*q+2*q*q*z+z*z)/(q+1)).sqrt();m0=R/(1+R);l0=1-m0
    mh=q.sqrt()/(1+q.sqrt());ep=(mh-m0)*D(fraction)
    K=q*(q-2)**2-q+1
    def oracle_shift(m):
        lam=1-m;rad=(q*(q-1)*lam*lam+K*m*m).sqrt()
        return (q*lam*lam-m*m)/(q*(q-2)*lam+rad),rad
    s0,rad0=oracle_shift(m0);w=(q-1)*s0/rad0
    C=(1-w)*(q-1)/q+w*(q-2)**2
    p=(1-w)/q;beta=(1-w)*(q-1)*w/(q*C)
    Lcoef=c*c*T*T
    frozen=lambda m:(p*m*m+beta*(1-m)**2)/2
    left=lambda m:Lcoef*(1-m)**2/2
    J=p*m0/l0;directJ=p*m0-beta*l0+Lcoef*l0
    worsterr=abs(J-directJ);sides=[]
    for side in [-1,1]:
        m=m0+side*ep;lam=1-m;vals=[]
        for di in range(1,qi+1):
            d=D(di);aa=(1-w)*(q-d)/q+w*(q-d-1)**2
            h=(1-w)*(q-d)*lam/q+w*lam*(q-1)*(q-d-1)
            u=max(D(0),min(D(1),h/aa)) if aa else D(0)
            val=((1-w)*(d*m*m+(q-d)*(u-lam)**2)/q+w*(lam*(q-1)-(q-d-1)*u)**2)/2
            vals.append((val,di))
        actual,d=min(vals);s,rad=oracle_shift(m)
        gamma=left(m) if side<0 else (m*m+(q-1)*s*s)/(2*q)
        frozen_shift=w*(q-2)*lam/C
        remainder=C*(s-frozen_shift)**2/2
        expected=(m*m+(q-1)*s*s)/(2*q)-frozen(m)
        worsterr=max(worsterr,abs(actual-frozen(m)),abs(expected-remainder))
        guard=p*m*m-beta*lam*lam
        assert guard>0 and 0<=m-frozen_shift<=1 and d==1
        sides.append(dict(side=side,nearest_distance=d,guard_margin=float(guard),
            nuisance=float(m-frozen_shift),oracle=float(gamma),frozen_value=float(actual),
            oracle_regret=float(gamma-actual),oracle_regret_over_eps2=float((gamma-actual)/(ep*ep))))
    tail=D(str(math.erfc(1/math.sqrt(2))/2))
    rm=(left(m0-ep)-frozen(m0-ep))*tail
    gp=((m0+ep)**2+(q-1)*oracle_shift(m0+ep)[0]**2)/(2*q)
    rp=(gp-frozen(m0+ep))+(frozen(m0+ep)-left(m0+ep))*tail
    lower=(left(m0-ep)+gp-2*left(m0)-ep*ep)*tail
    leading=J*ep*tail
    assert worsterr<D('1e-60')
    return dict(q=qi,width_fraction=float(fraction),epsilon=float(ep),slope_jump=float(J),
        effective_N=float(1/(q*q*ep*ep)),lower_over_leading=float(lower/leading),
        attainable_upper_over_leading=float(max(rm,rp)/leading),
        max_80digit_identity_error=str(worsterr),sides=sides)

def main():
    rows=[run(q,f) for q in [3,4,8,16,64,256,1024] for f in ['.1','.01','.001']]
    path=Path('research/d6_phase_boundary_20260908/frozen_allocation_gap.json')
    path.write_text(json.dumps(dict(evidence_class='HIGH_PRECISION_FROZEN_ALLOCATION_IDENTITIES',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
        scope=['Known A; 80-digit arithmetic; every hidden-alternative distance, continuous nuisance.',
               'The attainable upper uses B-off sign testing and fixed boundary allocations.',
               'effective_N is real-valued for the displayed asymptotic scaling, not an executed integer trial budget.',
               'Numerical evidence is separate from Lean certificates and does not prove unknown-A optimality.']),indent=2)+'\n')
    for r in rows:print({k:r[k] for k in ['q','width_fraction','lower_over_leading','attainable_upper_over_leading']},flush=True)
if __name__=='__main__':main()
