#!/usr/bin/env python3
"""Can a single allocation be good for two adjacent hidden sets?

All actual legal queries and every competing hidden set, continuous nuisance.
A cutting-plane LP gives a sandwich for the best common allocation value.
The dual LP bound is an upper bound for the unrestricted continuous-nuisance
problem; evaluating all alternative quadratics gives a feasible lower bound.
This is numerical evidence, not a universal-q decoder proof.
"""
import argparse,itertools,json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information


def model(q):
    k=q+1;m=2*q+2;j=1<<k;full=(1<<m)-1
    ground=[i for i in range(m) if (1<<i)!=j]
    labels=[sum(1<<i for i in c) for c in itertools.combinations(ground,k)]
    queries=[('s',i,False) for i in range(m)]
    for d in range(q+1):
        for c in itertools.combinations(ground,d):
            g=sum(1<<i for i in c);queries.append(('g',g,True))
            if d>=2:queries.append(('g',g,False))
    off=np.zeros((len(labels),len(queries)));slope=np.zeros_like(off)
    for row,A in enumerate(labels):
        B=full^A^j
        for col,(kind,g,h) in enumerate(queries):
            if kind=='s':off[row,col]=-1 if (1<<g)==j else 1;slope[row,col]=0 if A&(1<<g) else (1 if (1<<g)==j else -1)
            else:
                slope[row,col]=-((B&g).bit_count()-int(h));off[row,col]=(0 if h else 1)-slope[row,col]
    A=(1<<k)-1;Aprime=(A^1)|(1<<(k+1))
    return labels.index(A),labels.index(Aprime),off,slope


def solve(q,position,tol,max_iter):
    i,j,off,slope=model(q);p=phase_parameters(q);width=p['mu_H']-p['mu_U']
    mu=p['mu_U']+position*width/3
    gamma=information(q,mu,oracle(q,mu,p))[0]
    constraints=[];groups=[]
    for truth in [i,j]:
        targets=[r for r in range(len(off)) if r!=truth]
        d=off[targets]-(off[truth]+mu*slope[truth]);b=slope[targets]
        groups.append((d,b))
        for v in [0.,mu,1.]:constraints.extend(.5*(d+v*b)**2)
    Q=off.shape[1]; objective=np.zeros(Q+1);objective[-1]=-1
    trace=[]
    for iteration in range(max_iter):
        matrix=np.asarray(constraints)
        result=linprog(objective,A_ub=np.column_stack([-matrix,np.ones(len(matrix))]),b_ub=np.zeros(len(matrix)),
            A_eq=np.array([[*np.ones(Q),0.]]),b_eq=[1.],bounds=[(0,None)]*Q+[(None,None)],method='highs',
            options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not result.success:raise RuntimeError(result.message)
        w=result.x[:-1];upper=float(result.x[-1]);lower=float('inf');added=0
        for d,b in groups:
            aa=(b*b)@w;bb=(d*b)@w;cc=(d*d)@w
            nuisance=np.clip(np.divide(-bb,aa,out=np.zeros_like(bb),where=aa>0),0,1)
            val=.5*(cc+2*bb*nuisance+aa*nuisance*nuisance)
            lower=min(lower,float(val.min()))
            bad=np.flatnonzero(val<upper-tol)
            for r in bad:
                constraints.append(.5*(d[r]+nuisance[r]*b[r])**2);added+=1
        trace.append(dict(iteration=iteration,lower=lower,upper=upper,added=added))
        if upper-lower<=tol:break
    return dict(q=q,position=position,mu=mu,gamma=gamma,query_count=Q,hidden_set_count=len(off),
        common_value_lower=lower,common_value_upper=upper,decoder_gap_lower=gamma-upper,decoder_gap_upper=gamma-lower,
        q2_gap_lower=q*q*(gamma-upper),q3_gap_lower=q**3*(gamma-upper),converged=(upper-lower<=tol),
        tolerance=tol,iterations=len(trace),trace=trace)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--q',type=int,nargs='+',default=[3,4,5])
    ap.add_argument('--tolerance',type=float,default=1e-9);ap.add_argument('--max-iter',type=int,default=100)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/allocation_label_decoder.json'))
    args=ap.parse_args();rows=[]
    for q in args.q:
        for pos in [-1,0,1]:
            row=solve(q,pos,args.tolerance,args.max_iter);rows.append(row)
            print({k:row[k] for k in ['q','position','gamma','decoder_gap_lower','decoder_gap_upper','q2_gap_lower','converged','iterations']},flush=True)
    args.out.write_text(json.dumps(dict(evidence_class='ADJACENT_LABEL_COMMON_ALLOCATION_NUMERICAL_SANDWICH',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
        limitations=['Only tested q, all adjacent pairs equivalent by permutation.',
        'Floating-point LP bound is numerical, not a rationally certified or Lean-proved inequality.',
        'Pairwise incompatibility does not by itself establish a decoder for the entire label family.']),indent=2)+'\n')
if __name__=='__main__':main()
