# generate Lean tables of prefix counts for the two primal laws
L0 = ["AaaABb", "AaBabA", "aAbBAa", "aBAbaA", "BbaAAa", "bAAaaB"]
L1 = ["AabAaB", "aAaABb", "aAaAbB", "BaAaAb", "BbaAaA", "bAaBAa", "bBAaaA"]
def seq(st): return [ "AaBb".index(c) for c in st]
def counts(s,k): return [sum(1 for j in range(k) if s[j]==t) for t in range(4)]
def kap(s,k):
    v=counts(s,k); return abs(v[0]-v[1])
for nm,L in [("0",L0),("1",L1)]:
    S=[seq(x) for x in L]
    print(f"def s{nm} : Fin {len(S)} → Fin 6 → Fin 4 :=")
    print("  ![" + ",\n    ".join("![" + ", ".join(map(str,s)) + "]" for s in S) + "]")
    print(f"def T{nm} : Fin {len(S)} → Fin 7 → Fin 4 → ℕ :=")
    rows=[]
    for s in S:
        rows.append("![" + ", ".join("![" + ", ".join(map(str,counts(s,k))) + "]" for k in range(7)) + "]")
    print("  ![" + ",\n    ".join(rows) + "]")
    print(f"def kap{nm} : Fin {len(S)} → Fin 7 → ℝ :=")
    print("  ![" + ",\n    ".join("![" + ", ".join(str(kap(s,k)) for k in range(7)) + "]" for s in S) + "]")
