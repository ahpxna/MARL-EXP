"""Exact finite checks for the proposed shared-packet MARL game.

Not a learned policy, traffic experiment, general proof, or novelty certificate.
Two decision agents share the same packet observations and deterministic decoder;
team success is their common output equalling X. Each query trial is resampled.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import json

EDGES = ((1, 2), (1, 3), (2, 3))
ITEMS = (0, 1, 2, 3)
SETS = [s for k in (0, 1, 2) for s in combinations(ITEMS, k)]
CHECKS = 0


def check(ok):
    global CHECKS
    assert ok
    CHECKS += 1


def bweight(bit, p):
    return p if bit else 1 - p


def values(a, h, bad):
    out = {s: F(0) for s in SETS}
    # Exact observation/target joint laws also verify no hidden singleton signal.
    joint = {s: {} for s in SETS}
    mass = F(0)
    for X, E, E0, U12, U13, U23, V in product((0, 1), repeat=7):
        prob = F(1, 32) * bweight(E, F(1, 2)-h) * bweight(E0, F(1, 2)-a)
        mass += prob
        pads = dict(zip(EDGES, (U12, U13, U23)))
        payload = {0: {'copy': X ^ E0}, 1: {}, 2: {}, 3: {}}
        for edge, pad in pads.items():
            i, j = edge
            z = V if edge == bad else X ^ E
            payload[i][edge] = pad
            payload[j][edge] = pad ^ z
        for S in SETS:
            obs = tuple(tuple(payload[i].values()) for i in S)
            joint[S][(obs, X)] = joint[S].get((obs, X), F(0)) + prob
            if 0 in S:
                action = payload[0]['copy']
            elif len(S) == 2:
                edge = tuple(S)
                action = payload[S[0]][edge] ^ payload[S[1]][edge]
            else:
                action = 0
            out[S] += prob * (action == X)
    check(mass == 1)
    for S in SETS:
        expected = F(1, 2) + (a if 0 in S else h if len(S)==2 and S!=bad else 0)
        check(out[S] == expected)
        if 0 not in S and (len(S) <= 1 or S == bad):
            for obs, X in joint[S]:
                check(joint[S].get((obs, 0), F(0)) == joint[S].get((obs, 1), F(0)))
        if a > 0:
            # For the positive-a instances only: Bayes decoder agrees in value.
            observations = {obs for obs, _ in joint[S]}
            bayes = sum(max(joint[S].get((obs, 0), F(0)), joint[S].get((obs, 1), F(0)))
                        for obs in observations)
            check(bayes == out[S])
    return out


def geometry(a, h, bad, f):
    best = {k: max(f[s] for s in SETS if len(s)==k) for k in (1, 2)}
    def regrets(p):
        return [best[k] - f[tuple(sorted(p[:k]))] for k in (1, 2)]
    all_regrets = [regrets(p) for p in permutations(ITEMS)]
    det = min(max(r) for r in all_regrets)
    target = a*(h-a)/h
    check(det == min(a, h-a))
    # Exact dual lower certificate for every ranking.
    for r1, r2 in all_regrets:
        check((h-a)/h*r1 + a/h*r2 >= target)
    good = next(e for e in EDGES if e != bad)
    p0 = ITEMS
    p1 = good + tuple(x for x in ITEMS if x not in good)
    r0, r1 = regrets(p0), regrets(p1)
    mix = [a/h*r0[k] + (1-a/h)*r1[k] for k in range(2)]
    check(mix == [target, target])
    # Fixed rank, world-informed oracle repair, one replacement, both budgets.
    for k in (1, 2):
        prefix = set(ITEMS[:k])
        reach = [s for s in SETS if len(s)==k and len(prefix-set(s)) <= 1]
        check(max(f[s] for s in reach) == best[k])
    return {'a':str(a),'h':str(h),'bad':bad,'values':{str(s):str(v) for s,v in f.items()},
            'det_price':str(det),'random_price':str(target),'oracle_R1_price':'0'}


def main():
    rows=[]
    for a, h in ((F(1,8),F(1,4)), (F(1,10),F(3,10)), (F(1,16),F(3,16))):
        tables={bad:values(a,h,bad) for bad in EDGES}
        for s in SETS:
            if len(s)<=1:
                check(len({f[s] for f in tables.values()})==1)
        for bad,f in tables.items():
            rows.append(geometry(a,h,bad,f))
    # A negative-a alternative is evaluated by the SAME fixed decoder.
    for bad in EDGES:
        f=values(F(-1,8),F(1,4),bad)
        check(f[(0,)] < f[(1,)])
    out=Path(__file__).with_name('exact_check.json')
    if out.exists():
        raise FileExistsError('Refusing to overwrite existing evidence: '+str(out))
    result={'evidence_class':'EXACT FINITE CHECK OF A PROPOSED GAME; NOT LEAN OR TRAFFIC',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'checks':CHECKS,'instances':rows,
            'not_established':['all real parameters','noisy stopping/sample-complexity theorem',
                               'publication novelty','learned MARL performance']}
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks':CHECKS,'instances':len(rows),'artifact':str(out)},indent=2))

if __name__=='__main__':
    main()
