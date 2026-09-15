"""Small research probe of the compiled m=6 cell; not a global frontier claim.

Uses the same corner reference, response signs, S/T and four extrema as
LeanD6M6SharpnessBridgeV1. Rational primal/dual certificates are checked against
every generated constraint; no floating-point result is promoted on its own.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from fractions import Fraction as Q
import json
import numpy as np
from scipy.optimize import linprog

ROOT = Path('/Users/phanan/cig-amf-main')
sys.path.insert(0, str(ROOT / 'scripts'))
from run_d6_binary_exact_lp_ascent import build

P = build(6)
N, nv = 64, 78
S, T = (0, 4, 5), (1, 2, 3)
sign = (1, 1, 1, -1, 1, 1)

def solve(margin):
    A, b, E, e = [], [], [], []
    def row(v=None):
        r = np.zeros(nv, dtype=int)
        if v is not None:
            r[:N] = v
        return r
    for i in range(6):
        for v in P['rho'][i]:
            r = row(v); r[N+i] = -1
            A.append(r); b.append(Q(0))
            r = row(-v); r[N+6+i] = 1
            A.append(r); b.append(Q(0))
        r = row(); r[N+i] = 1; r[N+6+i] = -1
        A.append(r); b.append(Q(1))
    for a in range(N):
        A.append(row(P['G'][S][a] - P['G'][S][6])); b.append(Q(0))
        A.append(row(P['G'][S][57] - P['G'][S][a])); b.append(Q(0))
        r = row(P['G'][T][a]); r[76] = -1
        A.append(r); b.append(Q(0))
        r = row(-P['G'][T][a]); r[77] = 1
        A.append(r); b.append(Q(0))
    r = row(P['G'][T][6]); r[76] = -1; E.append(r); e.append(Q(0))
    r = row(P['G'][T][9]); r[77] = -1; E.append(r); e.append(Q(0))
    for i in range(6):
        A.append(row(-sign[i]*P['comp'][i])); b.append(Q(0))
    for i in S:
        for j in T:
            A.append(row(sign[j]*P['comp'][j] - sign[i]*P['comp'][i]))
            b.append(-margin)
    r = row(); r[0] = 1; E.append(r); e.append(Q(0))
    obj = row(P['G'][S][6] - P['G'][S][57]); obj[76] = -1; obj[77] = 1
    AA, EE = np.array(A), np.array(E)
    res = linprog(-obj, A_ub=AA, b_ub=np.array(b, float),
                  A_eq=EE, b_eq=np.array(e, float), bounds=[(None,None)]*nv,
                  method='highs')
    out = dict(margin=str(margin), status=int(res.status), message=res.message)
    if not res.success:
        return out
    rat = lambda xs: np.array([Q(float(x)).limit_denominator(1000000) for x in xs], dtype=object)
    x = rat(res.x)
    lam = rat(-res.ineqlin.marginals)
    nu = rat(-res.eqlin.marginals)
    primal = all(AA @ x <= np.array(b, object)) and all(EE @ x == np.array(e, object))
    dual = all(lam >= 0) and all(AA.T @ lam + EE.T @ nu == obj)
    val, upper = obj @ x, np.array(b, object) @ lam + np.array(e, object) @ nu
    assert primal and dual and val == upper, 'No exact primal/dual equality'
    scores = [abs(v) for v in P['comp'] @ x[:N]]
    delta = max(max(R @ x[:N])-min(R @ x[:N]) for R in P['rho'])
    out.update(exact_cell_optimum=str(val), exact_primal_valid=bool(primal),
               exact_dual_valid=bool(dual), exact_duality_gap=str(upper-val),
               actual_margin=str(min(scores[i] for i in S)-max(scores[j] for j in T)),
               actual_delta=str(delta), scores=list(map(str,scores)),
               old_family_gap=str(6*(1-margin)),
               world=list(map(str,x[:N])), primal_variables=list(map(str,x)),
               dual_inequalities=list(map(str,lam)), dual_equalities=list(map(str,nu)))
    return out

if __name__ == '__main__':
    rows = [solve(Q(g)) for g in ['0','1/20','1/10','1/4','1/2']]
    out = Path(__file__).with_suffix('.json')
    out.write_text(json.dumps(dict(scope='ONE_FIXED_COMPILED_M6_CELL_ONLY',
                                  evidence='EXACT_RATIONAL_PRIMAL_DUAL_LP', rows=rows), indent=2))
    for r in rows:
        print({k:v for k,v in r.items() if k not in {'world','primal_variables','dual_inequalities','dual_equalities'}}, flush=True)
