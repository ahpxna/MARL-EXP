import sys
from plp import *
for r in [1.5, 2.2, 2.4, 2.5, 2.55, 2.8, 3.5]:
    for eta in [0.0, 0.1, 0.3, 0.5, 0.8, 1.2]:
        T, p, mu, lu, ll = solve(r, eta)
        sup = [(round(p[j], 5), ''.join('AaBb'[t] for t in seqs[j])) for j in range(180) if p[j] > 1e-9]
        print(f"r={r} eta={eta} T={T:.6f} mu={np.round(mu,5)}")
        print("   l(up-lo)=", np.round(lu - ll, 5).tolist())
        print("   supp=", sup)
