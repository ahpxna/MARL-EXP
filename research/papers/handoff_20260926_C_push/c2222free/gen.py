"""Generate LeanPaperCTwoMag2222FreeV1.lean"""
import itertools
from fractions import Fraction as Fr
from certs import REG, cost, certs, dp, padd, pneg, nonneg_coeffs, ev
from verify_r2 import PATHS, parse
ST=list(itertools.product(range(3),repeat=4))
def p2(p):
    keys=[(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]
    vals=[p.get(k,Fr(0)) for k in keys]
    for (i,j) in p: assert i+j<=2, p
    assert all(v.denominator==1 for v in vals), p
    return "⟨" + ", ".join(str(int(v)) if v>=0 else f"({int(v)})" for v in vals) + "⟩"
def table(name, f, doc):
    lines=[f"/-- {doc} -/", f"def {name} : ℕ → ℕ → ℕ → ℕ → P2"]
    for v in ST:
        lines.append(f"  | {v[0]}, {v[1]}, {v[2]}, {v[3]} => {p2(f(v))}")
    lines.append("  | _, _, _, _ => ⟨0, 0, 0, 0, 0, 0⟩")
    return "\n".join(lines)
def mutable(name, mu, doc):
    lines=[f"/-- {doc} -/", f"def {name} : ℕ → P2"]
    for k in range(1,8):
        if k in mu: lines.append(f"  | {k} => {p2(mu[k])}")
    lines.append("  | _ => ⟨0, 0, 0, 0, 0, 0⟩")
    return "\n".join(lines)
out=[]
# cost tables
for rn in ['R1','R2','R3']:
    R=REG[rn]
    out.append(table(f"kap{rn}", lambda v,R=R,rn=rn: cost(R,rn,v), f"The raw cost of each count state on region {rn}, in its `(s,t)` coordinates."))
certdata={}
for rn in ['R1','R2','R3']:
    for cn,(mu,W) in certs(rn).items():
        phi,bad,start=dp(rn,mu,W)
        assert not bad and not start
        Z={}
        for k,p in mu.items(): Z=padd(Z,p)
        certdata[cn]=(rn,mu,W,Z,phi)
        out.append(mutable(f"mu{cn}", mu, f"Budget weights (numerators) of certificate {cn}."))
        out.append(table(f"psi{cn}", lambda v,phi=phi: phi[v], f"Potentials of certificate {cn}."))
        print(cn, "Z=",Z, "W=",W)
open("gen_tables.lean","w").write("\n\n".join(out)+"\n")
# flow tables
TN="AaBb"
def states(s):
    v=[0,0,0,0]; outs=[tuple(v)]
    for x in s: v[x]+=1; outs.append(tuple(v))
    return outs
FLOWS={
 'R1':[ [1,0,3,2,3,2,1,0], [2,1,2,1,0,3,0,3] ],   # aAbBbBaA, BaBaAbAb
 'R3':[ [0,1,2,1,0,3,2,3], [1,0,3,2,3,2,1,0], [3,0,1,2,3,0,1,2], [3,2,1,0,1,0,3,2], [3,2,3,0,1,2,1,0] ],
 'A':[parse(PATHS[x]) for x in ['P1','Pc','P3']],
 'B':[parse(PATHS[x]) for x in ['Pa','Pb','Pd','Pe','Pf','Pg','P3','P1']],
 'C':[parse(PATHS[x]) for x in ['Pa','Pb','Pd','Pe','Pf','Pg','Pj','Pk','Pc']],
}
fo=[]
for fn,seqs in FLOWS.items():
    for s in seqs: assert sorted(s)==[0,0,1,1,2,2,3,3]
    P=len(seqs)
    fo.append(f"/-- The type sequences of flow {fn}: " + ", ".join("".join(TN[x] for x in s) for s in seqs) + ". -/")
    fo.append(f"def seq{fn} : Fin {P} → Fin 8 → Fin 4 :=\n  ![" + ",\n    ".join("![" + ", ".join(map(str,s)) + "]" for s in seqs) + "]")
    fo.append(f"/-- Prefix counts of flow {fn}. -/")
    fo.append(f"def tab{fn} : Fin {P} → Fin 9 → Fin 4 → ℕ :=\n  ![" + ",\n    ".join("![" + ", ".join("![" + ", ".join(map(str,st)) + "]" for st in states(s)) + "]" for s in seqs) + "]")
open("gen_flows.lean","w").write("\n\n".join(fo)+"\n")
print("ok")
