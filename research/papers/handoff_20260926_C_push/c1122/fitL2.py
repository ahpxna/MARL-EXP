from fractions import Fraction as Fr
from red import solve
from pieces import pieces
for j in range(0, 11):
    r = Fr(7, 3) + (Fr(13, 5) - Fr(7, 3)) * Fr(j, 10)
    rho = r - 1
    L0, bps = pieces(r)
    # the piece before the free threshold
    lines = [L0] + [lb for _, (la, lb) in bps]
    etas = [e for e, _ in bps]
    # L2' is lines[-2]
    Phi, S = lines[-2]
    e = (etas[-2] + etas[-1]) / 2
    val, mu, y, supp = solve(r, e)
    Tf = 2 * rho * (2 - rho) / (8 - 3 * rho)
    ef = 4 * (5 - 3 * rho) / (8 - 3 * rho)
    print(f"r={r} rho={rho} Phi={Phi} S={S} mu={[str(x) for x in mu]} y={[str(x) for x in y]} Tf_ok={lines[-1][0]==Tf} ef_ok={etas[-1]==ef} eta1={etas[-2]}")
    print("   supp:", [(str(p), s) for p, s, k in supp])
