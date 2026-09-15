"""R3 exact rational support-radius layers and minimax transition DP.
Finite search only: neither growing lower bound nor epsilon-only bound inferred.
"""
from fractions import Fraction as F
from pathlib import Path
import random,json,hashlib

def run(matrix,eps):
    m=len(matrix);h=len(matrix[0]);U=(1<<m)-1
    denom=sum(max(row)-min(row) for row in matrix)
    if not denom:raise ValueError('zero normalization')
    vals=[];layers=[[] for _ in range(m+1)]
    for S in range(1<<m):
        residual=[sum(matrix[i][a] for i in range(m) if not S>>i&1) for a in range(h)]
        vals.append(F(max(residual)-min(residual),denom))
    for k in range(m+1):
        layer=[S for S in range(1<<m) if S.bit_count()==k];opt=min(vals[S] for S in layer)
        layers[k]=[S for S in layer if vals[S]<=opt+eps]
    D={0:0};parents=[]
    for layer in layers[1:]:
        new={};parent={}
        for T in layer:
            value,S=min((max(v,(S&~T).bit_count()),S) for S,v in D.items())
            new[T]=value;parent[T]=S
        D=new;parents.append(parent)
    T=U;path=[T]
    for parent in reversed(parents):T=parent[T];path.append(T)
    path.reverse();value=D[U]
    assert max((S&~T).bit_count() for S,T in zip(path,path[1:]))==value
    assert all(S in layer for S,layer in zip(path,layers))
    return {'epsilon':str(eps),'R_epsilon':value,'normalization_sum_spans':denom,
            'good_layer_sizes':list(map(len,layers)),'optimal_path_masks':path,
            'path_radius':[str(vals[S]) for S in path]}

if __name__=='__main__':
    rows=[]
    for m in [6,8,10]:
        for seed in range(8):
            rng=random.Random(20260913+100*m+seed)
            matrix=[[0]+[rng.randint(-4,4) for _ in range(5)] for i in range(m)]
            for eps in [F(1,20),F(1,10),F(1,4)]:
                out=run(matrix,eps);out.update({'m':m,'seed':seed,'integer_support_matrix':matrix});rows.append(out)
    Path(__file__).with_suffix('.json').write_text(json.dumps({'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'scope':'72 finite exact DP searches, fixed seeded integer support matrices; no asymptotic conclusion',
      'normalization':'support radius divided by sum of component radii = residual oscillation / sum component oscillations',
      'results':rows},indent=2)+'\n')
    print('PASS',len(rows),'exact DP cells; maximum recourse',max(x['R_epsilon'] for x in rows),flush=True)
