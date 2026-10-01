from fractions import Fraction as Fr
from full import *
def rhos(lo, hi, N=12):
    return [lo + (hi - lo) * Fr(j, N) for j in range(N + 1)]
ok = True
def claim(c, msg):
    global ok
    if not c:
        ok = False; print("FAIL", msg)
# ---- primal flows
P = {}
P['L0'] = lambda rho: symmix([(Fr(2, 3), 'AbaBBb'), (Fr(1, 3), 'BaBbAb')])
P['H0'] = lambda rho: symmix([(Fr(2, 3), 'AaBbBb'), (Fr(1, 4), 'BBaAbb'), (Fr(1, 12), 'BbAaBb')])
P['M1f'] = lambda rho: symmix([((2 - rho) / 2, 'BaBbAb'), (rho / 2, 'AaBbBb')])
P['M23f'] = lambda rho: symmix([((8 - 5 * rho) / (8 - 3 * rho), 'BaBbAb'), ((6 * rho - 8) / (8 - 3 * rho), 'BaAbBb'), (4 * (2 - rho) / (8 - 3 * rho), 'AaBbBb')])
P['M4f'] = lambda rho: symmix([(1 - Fr(8, 5) / rho, 'BbAaBb'), (Fr(4, 5) / rho, 'BaAbBb'), (Fr(4, 5) / rho, 'AaBbBb')])
P['Hf'] = lambda rho: symmix([(Fr(1, 5), 'BbAaBb'), (Fr(2, 5), 'BaAbBb'), (Fr(2, 5), 'AaBbBb')])
tests = [('L0', Fr(1, 100), Fr(1), lambda rho: 2 * rho / 3, lambda rho: 0),
         ('H0', Fr(3, 2), Fr(5), lambda rho: rho / 3, lambda rho: 0),
         ('M1f', Fr(1, 100), Fr(1), lambda rho: rho / 2, lambda rho: 1),  # L free uses theta=1/2 though
         ('M1f', Fr(1), Fr(4, 3), lambda rho: rho * (2 - rho) / 2, lambda rho: 1),
         ('M23f', Fr(4, 3), Fr(8, 5), lambda rho: 2 * rho * (2 - rho) / (8 - 3 * rho), lambda rho: 4 * (5 - 3 * rho) / (8 - 3 * rho)),
         ('M4f', Fr(8, 5), Fr(2), lambda rho: Fr(2, 5), lambda rho: 1 - Fr(6, 5) / rho),
         ('Hf', Fr(2), Fr(5), lambda rho: rho / 5, lambda rho: Fr(2, 5))]
for name, lo, hi, Tf, ef in tests:
    for rho in rhos(lo, hi):
        mix = P[name](rho) if not (name == 'M1f' and hi == 1) else symmix([(Fr(1, 2), 'BaBbAb'), (Fr(1, 2), 'AaBbBb')])
        dev, costs = check_mix(rho + 1, mix)
        claim(max(costs) == Tf(rho), f"{name} rho={rho} costs={costs} T={Tf(rho)}")
        claim(dev <= ef(rho), f"{name} rho={rho} dev={dev} ef={ef(rho)}")
print("primal flows checked", ok)
# ---- dual certificates (reduced mu, lam1, lam2)
D = {}
D['A'] = (lambda rho: ((0, Fr(1, 2), Fr(1, 2)), 0, rho / 2))
D['band'] = (lambda rho: ((1, 0, 0), -rho, 0))
D['Lf'] = (lambda rho: ((0, Fr(1, 2), Fr(1, 2)), 0, 0))
D['M1f'] = (lambda rho: ((0, (2 - rho) / 2, rho / 2), 0, 0))
D['M23f'] = (lambda rho: ((2 * (2 - rho) / (8 - 3 * rho), 2 * (2 - rho) / (8 - 3 * rho), rho / (8 - 3 * rho)), 0, 0))
D['M4Hf'] = (lambda rho: ((Fr(2, 5), Fr(2, 5), Fr(1, 5)), 0, 0))
dtests = [('A', Fr(1, 100), Fr(1), lambda rho: 2 * rho / 3, lambda rho: rho / 6),
          ('A', Fr(1), Fr(3, 2), lambda rho: (3 - rho) / 3, lambda rho: rho / 6),
          ('band', Fr(1, 100), Fr(5), lambda rho: rho / 3, lambda rho: rho / 3),
          ('Lf', Fr(1, 100), Fr(1), lambda rho: rho / 2, lambda rho: 0),
          ('M1f', Fr(1), Fr(4, 3), lambda rho: rho * (2 - rho) / 2, lambda rho: 0),
          ('M23f', Fr(4, 3), Fr(8, 5), lambda rho: 2 * rho * (2 - rho) / (8 - 3 * rho), lambda rho: 0),
          ('M4Hf', Fr(8, 5), Fr(2), lambda rho: Fr(2, 5), lambda rho: 0),
          ('M4Hf', Fr(2), Fr(5), lambda rho: rho / 5, lambda rho: 0)]
for name, lo, hi, Phi, Sl in dtests:
    for rho in rhos(lo, hi):
        mu, l1, l2 = D[name](rho)
        val, pen, psi = lb(rho + 1, mu, l1, l2)
        claim(val == Phi(rho), f"dual {name} rho={rho} val={val} want {Phi(rho)}")
        claim(pen == Sl(rho), f"dual {name} rho={rho} pen={pen} want {Sl(rho)}")
print("duals checked", ok)
def PM0(rho):
    x = (rho - 1) / (3 * (2 - rho))
    return symmix([(x, 'AbaBBb'), (x, 'BaAbBb'), (Fr(2, 3) - x, 'AaBbBb'), (Fr(1, 3) - x, 'BBaAbb')])
for rho in rhos(Fr(1), Fr(3, 2)):
    dev, costs = check_mix(rho + 1, PM0(rho))
    claim(dev == 0 and max(costs) == (3 - rho) / 3, f"PM0 {rho} {dev} {costs}")
print("PM0 checked", ok)
