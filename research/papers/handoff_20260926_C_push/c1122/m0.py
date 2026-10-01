from fractions import Fraction as Fr
from red import solve
for r in [Fr(2), Fr(41, 20), Fr(21, 10), Fr(11, 5), Fr(23, 10), Fr(12, 5), Fr(49, 20), Fr(5, 2)]:
    val, mu, y, supp = solve(r, Fr(0))
    print(r, val, [(str(p), s, tuple(str(q) for q in k[0]), str(k[1]), str(k[2])) for p, s, k in supp])
