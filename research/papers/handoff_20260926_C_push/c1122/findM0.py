from fractions import Fraction as Fr
from feat import features, seqs
from xlp import simplex
import sys
# joint feasibility at rho=1 and rho=3/2 with same weights, eta = 0, T = (3-rho)/3 ; M cost regime
def uvec(j, r):
    f = features(j, 'M')
    return [x[0] * r + x[1] for x in f[:3]], f[3], f[4]
# restrict to one representative per (M-feature-class as linear forms)
cl = {}
for j in range(180):
    f = features(j, 'M')
    cl.setdefault(f, j)
J = list(cl.values())
N = len(J)
A, b = [], []
for r in (Fr(2), Fr(5, 2)):
    T = (3 - (r - 1)) / 3
    for k in range(3):
        A.append([uvec(j, r)[0][k] for j in J]); b.append(T)
Aeq = [[uvec(j, 2)[1] for j in J], [uvec(j, 2)[2] for j in J], [1] * N]
beq = [Fr(1, 3), Fr(2, 3), 1]
res = simplex([0] * N, A, b, Aeq, beq)
print(res is not None)
if res:
    val, x, y = res
    for i in range(N):
        if x[i]:
            print(x[i], ''.join('AaBb'[t] for t in seqs[J[i]]), features(J[i], 'M'))
