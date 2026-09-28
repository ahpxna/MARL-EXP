#!/usr/bin/env python3
"""Exact (Fraction) verification of the (2,2,1,1) certificates.
Types: 0=+a, 1=-a, 2=+b, 3=-b; multiset counts (2,2,1,1); m = 6; D = 4a+2b; c = (a-b)/D.
Claim: V(eta) = c * max((2-eta)/3, 2/5).
"""
import itertools
from fractions import Fraction as Fr

N = (2, 2, 1, 1)
W = lambda a, b: (a, -a, b, -b)
SEQS = sorted(set(itertools.permutations([0, 0, 1, 1, 2, 3])))
ok = True


def check(name, cond):
    global ok
    print(("OK   " if cond else "FAIL ") + name)
    ok = ok and cond


def counts(s, k):
    return tuple(sum(1 for j in range(k) if s[j] == t) for t in range(4))


def baseline(a, b, k):
    return min(abs(sum(w * u for w, u in zip(W(a, b), u)))
               for u in itertools.product(*[range(n + 1) for n in N]) if sum(u) == k)


def raw_cost(a, b, s, k):
    v = counts(s, k)
    return abs(sum(w * x for w, x in zip(W(a, b), v))) - baseline(a, b, k)


# test points: rays and several interior ratios (costs are piecewise linear; sign pattern
# is fixed on a > b > 0, so linear identities on the open cone follow from the rays + interior)
PTS = [(Fr(1), Fr(0)), (Fr(1), Fr(1)), (Fr(3, 2), Fr(1)), (Fr(2), Fr(1)), (Fr(7), Fr(3)),
       (Fr(101), Fr(100)), (Fr(1000), Fr(1))]
INTERIOR = PTS[2:]

# 1. baselines
for a, b in INTERIOR:
    check(f"baselines (b,0,b,0,b) at a/b={a/b}",
          [baseline(a, b, k) for k in range(1, 6)] == [b, 0, b, 0, b])

# 2. cost lower bound kappa: raw_cost >= |x0-x1|(a-b) on every box state, every k
states = list(itertools.product(*[range(n + 1) for n in N]))
good = True
for a, b in INTERIOR:
    bk = [baseline(a, b, k) for k in range(7)]
    for v in states:
        k = sum(v)
        if not 1 <= k <= 5:
            continue
        cst = abs(sum(w * x for w, x in zip(W(a, b), v))) - bk[k]
        if cst < abs(v[0] - v[1]) * (a - b):
            good = False
check("cost >= |x0-x1|(a-b) on box states, k=1..5", good)

# 3. dual (band): budget-1 cost = (a-b)*[first is an a-item]; P(b first) <= 2(1+eta)/6
good = all(raw_cost(a, b, s, 1) == ((a - b) if s[0] in (0, 1) else 0) for a, b in INTERIOR for s in SEQS)
check("budget-1 cost is (a-b) iff an a-item is first", good)

# 4. dual (free): every order has r1+..+r5 >= 2(a-b)
good = all(sum(raw_cost(a, b, s, k) for k in range(1, 6)) >= 2 * (a - b) for a, b in INTERIOR for s in SEQS)
check("every order has r1+...+r5 >= 2(a-b) (all 180 type sequences)", good)
# the per-order case proof used: (i) a-item first -> r1 = a-b; (ii) a-item last -> r5 = a-b;
# (iii) b-item first & a-item second -> r2 >= a-b; (iv) a-item 5th & b-item last -> r4 >= a-b;
# (v) both b-items in the last two / first two -> r3 = a-b.
def case_ok(s, a, b):
    r = [None] + [raw_cost(a, b, s, k) for k in range(1, 6)]
    A = lambda t: t in (0, 1)
    if A(s[0]) and A(s[5]):
        return r[1] == a - b and r[5] == a - b
    if not A(s[0]) and not A(s[5]):
        return r[2] >= a - b and r[4] >= a - b
    if A(s[0]) and not A(s[5]):
        if A(s[4]):
            return r[1] == a - b and r[4] >= a - b
        return r[1] == a - b and r[3] == a - b
    if A(s[1]):
        return r[5] == a - b and r[2] >= a - b
    return r[5] == a - b and r[3] == a - b
check("the per-order case split holds on every order",
      all(case_ok(s, a, b) for a, b in INTERIOR for s in SEQS))

# 5. primal laws
def parse(st):
    return tuple("AaBb".index(ch) for ch in st)

L0 = [(parse(x), Fr(1, 6)) for x in ["AaaABb", "AaBabA", "aAbBAa", "aBAbaA", "BbaAAa", "bAAaaB"]]
L1 = [(parse("AabAaB"), Fr(1, 5)), (parse("aAaABb"), Fr(1, 10)), (parse("aAaAbB"), Fr(1, 10)),
      (parse("BaAaAb"), Fr(1, 5)), (parse("BbaAaA"), Fr(1, 10)), (parse("bAaBAa"), Fr(1, 5)),
      (parse("bBAaaA"), Fr(1, 10))]


def dev(L):
    d = Fr(0)
    for k in range(7):
        for t in range(4):
            mean = sum(w * counts(s, k)[t] for s, w in L) / N[t]
            d = max(d, 6 * abs(mean - Fr(k, 6)))
    return d


for nm, L, bound, eta in [("L0", L0, Fr(2, 3), Fr(0)), ("L1", L1, Fr(2, 5), Fr(4, 5))]:
    check(f"{nm}: weights nonneg, sum 1", all(w >= 0 for _, w in L) and sum(w for _, w in L) == 1)
    check(f"{nm}: every sequence has multiplicities (2,2,1,1)", all(counts(s, 6) == N for s, _ in L))
    check(f"{nm}: deviation {dev(L)} <= {eta}", dev(L) <= eta)
    for a, b in PTS[:2] + INTERIOR:
        costs = [sum(w * raw_cost(a, b, s, k) for s, w in L) for k in range(1, 6)]
        if b < a and b > 0:
            check(f"{nm}: costs at a/b={a/b} are {[c/(a-b) for c in costs]}*(a-b) <= {bound}(a-b)",
                  all(c <= bound * (a - b) for c in costs))

# 6. the claimed frontier numerically consistent: primal at eta in [0,4/5] via mixture
for eta in [Fr(0), Fr(1, 5), Fr(1, 2), Fr(4, 5)]:
    t = eta * Fr(5, 4)
    L = [(s, (1 - t) * w) for s, w in L0] + [(s, t * w) for s, w in L1]
    a, b = Fr(2), Fr(1)
    costs = [sum(w * raw_cost(a, b, s, k) for s, w in L) for k in range(1, 6)]
    check(f"mixture at eta={eta}: dev {dev(L)} <= eta, max cost/(a-b) = {max(costs)/(a-b)} = (2-eta)/3",
          dev(L) <= eta and max(costs) / (a - b) == (2 - eta) / 3)

print("ALL OK" if ok else "SOME CHECK FAILED")
