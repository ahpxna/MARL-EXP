"""Exhaustive exact-rational search for the D6 decision-factor conjecture.

The search enumerates a finite integer lattice of binary-action worlds under a
uniform product reference and computes every quantity with fractions.Fraction.
This is a falsification tool, not a proof of worlds outside the enumerated
lattice.
"""
from __future__ import annotations
import argparse, itertools, json
from fractions import Fraction
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='d6_exact_integer_search_v1'


def _mean(vals): return sum(vals,Fraction(0))/len(vals)
def _half_range(vals): return (max(vals)-min(vals))/2


def evaluate(values,m,k):
    actions=tuple(itertools.product((0,1),repeat=m)); F={a:Fraction(int(v)) for a,v in zip(actions,values)}
    baseline=_mean([F[a] for a in actions])
    rows=[]
    for j in range(m):
        row=[]
        for aj in (0,1): row.append(_mean([F[a] for a in actions if a[j]==aj]))
        rows.append(tuple(row))
    surrogate={a:sum((rows[j][a[j]] for j in range(m)),Fraction(0))-(m-1)*baseline for a in actions}
    sup=max(abs(F[a]-surrogate[a]) for a in actions)
    delta=Fraction(0)
    for i in range(m):
        for x in actions:
            for c in actions:
                ci=list(x);ci[i]=c[i]; xc=list(c);xc[i]=x[i]
                d=F[x]-F[tuple(ci)]-F[tuple(xc)]+F[c]
                delta=max(delta,abs(d))
    score=[max(row)-min(row) for row in rows]
    order=sorted(range(m),key=lambda j:(-score[j],j)); chosen=tuple(sorted(order[:k]))
    components=[tuple(v-baseline for v in row) for row in rows]
    def loss(S):
        S=set(S); vals=[]
        for a in actions: vals.append(F[a]-sum((components[j][a[j]] for j in S),Fraction(0)))
        return _half_range(vals)
    subset_losses=[(S,loss(S)) for S in itertools.combinations(range(m),k)]; optimum=min(v for _,v in subset_losses); regret=loss(chosen)-optimum
    approx_rhs=Fraction(m-1)*delta; candidate=approx_rhs/2
    ratio=(regret/approx_rhs) if approx_rhs else Fraction(0)
    return {'delta':delta,'sup_error':sup,'approx_rhs':approx_rhs,'regret':regret,'candidate_rhs':candidate,'ratio':ratio,'chosen':chosen,'optimum':optimum}


def fs(x): return f'{x.numerator}/{x.denominator}'


def run(m=3,k_values=(1,2),value_radius=1,anchor_zero=True,stop_on_counterexample=False):
    m=int(m); cells=2**m; vals=range(-int(value_radius),int(value_radius)+1); total=0; best=None; killed=False; witness=None
    iterator=itertools.product(vals,repeat=cells-1 if anchor_zero else cells)
    for tail in iterator:
        values=(0,)+tuple(tail) if anchor_zero else tuple(tail); total+=1
        for k in k_values:
            if not 1<=int(k)<m: continue
            r=evaluate(values,m,int(k)); ratio=r['ratio']
            if best is None or ratio>best[0]: best=(ratio,values,int(k),r)
            if r['regret']>r['candidate_rhs']:
                killed=True; witness=(values,int(k),r)
                if stop_on_counterexample: break
        if killed and stop_on_counterexample: break
    def pack(item):
        if item is None:return None
        values,k,r=(item[1],item[2],item[3]) if len(item)==4 else item
        return {'values':list(map(int,values)),'shape':[2]*m,'k':int(k),'delta':fs(r['delta']),'surrogate_sup_error':fs(r['sup_error']),'approximation_rhs':fs(r['approx_rhs']),'decision_regret':fs(r['regret']),'candidate_half_rhs':fs(r['candidate_rhs']),'ratio_regret_over_approx_rhs':fs(r['ratio']),'chosen_topc':list(r['chosen']),'optimum_loss':fs(r['optimum'])}
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'EXHAUSTIVE_FINITE_EXACT_RATIONAL','m':m,'k_values':list(map(int,k_values)),'value_radius':int(value_radius),'anchor_zero':bool(anchor_zero),'worlds_enumerated':int(total),'candidate':'decision_regret <= (m-1)*delta_square/2','candidate_killed':bool(killed),'counterexample':pack(witness),'best_ratio_witness':pack(best)}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--m',type=int,default=3); p.add_argument('--k-values',nargs='+',type=int,default=[1,2]); p.add_argument('--value-radius',type=int,default=1); p.add_argument('--no-anchor-zero',action='store_true'); p.add_argument('--stop-on-counterexample',action='store_true'); p.add_argument('--out',default='research/high_value_extensions/d6/exact_small.json'); a=p.parse_args(argv)
    payload=run(a.m,tuple(a.k_values),a.value_radius,not a.no_anchor_zero,a.stop_on_counterexample); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 2 if payload['candidate_killed'] else 0
if __name__=='__main__': raise SystemExit(main())
