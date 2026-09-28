from fractions import Fraction as Fr
from red import solve

def line_at(r, eta):
    val, mu, y, supp = solve(r, eta)
    # slope: -(1/3)*(sum |band duals|)
    S = sum(abs(q) for q in y) / 3
    return (val + eta * S, S), val, mu, y

def pieces(r, lo=Fr(0), hi=Fr(3)):
    La, va, mua, ya = line_at(r, lo)
    Lb, vb, mub, yb = line_at(r, hi)
    out = {}
    def rec(a, La, b, Lb):
        if La == Lb:
            return
        # intersection: Phi_a - e S_a = Phi_b - e S_b
        if La[1] == Lb[1]:
            raise Exception("parallel")
        e = (La[0] - Lb[0]) / (La[1] - Lb[1])
        Le, ve, mue, ye = line_at(r, e)
        if ve == La[0] - e * La[1]:
            out[e] = (La, Lb)
            return
        rec(a, La, e, Le)
        rec(e, Le, b, Lb)
    rec(lo, La, hi, Lb)
    return La, sorted(out.items())

if __name__ == "__main__":
    import sys
    rs = [Fr(3, 2), Fr(2)] + [Fr(2) + Fr(j, 40) for j in range(1, 40)] + [Fr(3), Fr(7, 2)]
    for r in rs:
        L0, bps = pieces(r)
        desc = [f"eta={str(e)}({float(e):.4f})" for e, _ in bps]
        lines = [L0] + [lb for _, (la, lb) in bps]
        print(f"r={r} ({float(r):.3f}) bps: {desc}")
        print("     lines (Phi, S):", [(str(p), str(s)) for p, s in lines])
