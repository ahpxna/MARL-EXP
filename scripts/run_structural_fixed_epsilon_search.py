"""Exact menu size on a subset lattice, with bounded random instance search.

No permutation enumeration and no floating point optimizer. A state retains the
inclusion-maximal sets of budgets covered by paths ending at that subset. This
is lossless: every continuation is shared by paths with the same endpoint.
Random search is NOT a universal bound or evidence that an unseen witness is
impossible. Every reported menu size is exact for the specified finite instance.
"""
from __future__ import annotations
import argparse, hashlib, json, random
from fractions import Fraction
from pathlib import Path


def maximal(masks):
    answer = []
    for a in sorted(set(masks), key=int.bit_count, reverse=True):
        if not any(a | b == b for b in answer):
            answer.append(a)
    return tuple(answer)


def solve(points, epsilon):
    m = len(points[0]); size = 1 << m
    assert all(len(p) == m for p in points)
    scale = sum(max(p[j] for p in points)-min(p[j] for p in points) for j in range(m))
    assert scale > 0
    sums = [[0]*size for _ in points]
    costs = [0]*size
    opt = [10**30]*(m+1)
    for s in range(size):
        if s:
            bit = s & -s; j = bit.bit_length()-1; prev = s ^ bit
            for row, p in zip(sums, points): row[s] = row[prev]+p[j]
        remaining = [sum(p)-row[s] for row,p in zip(sums,points)]
        costs[s] = max(remaining)-min(remaining)
        k = s.bit_count(); opt[k] = min(opt[k],costs[s])
    good = [(costs[s]-opt[s.bit_count()])*epsilon.denominator <= epsilon.numerator*scale for s in range(size)]
    paths = [()]*size; paths[0] = (1,)
    for s in range(1,size):
        bitmask = (1 << s.bit_count()) if good[s] else 0
        candidates = []; bits = s
        while bits:
            bit = bits & -bits; bits ^= bit
            candidates.extend(a | bitmask for a in paths[s ^ bit])
        paths[s] = maximal(candidates)
    full = (1 << (m+1))-1
    covers = paths[-1]
    level = {0: ()}
    while full not in level:
        nxt = {}
        for a, chosen in level.items():
            for b in covers:
                nxt.setdefault(a | b, chosen+(b,))
        keep = maximal(nxt)
        level = {a:nxt[a] for a in keep}
    chosen = level[full]
    rankings = []
    for target in chosen:
        s = size-1; reverse = []
        while s:
            if good[s]: target &= ~(1 << s.bit_count())
            for j in range(m):
                if s & (1 << j):
                    prev = s ^ (1 << j)
                    if any(target | a == a for a in paths[prev]):
                        reverse.append(j); s = prev; break
            else: raise AssertionError('Missing path witness')
        rankings.append(reverse[::-1])
    verified = 0
    for ranking in rankings:
        s = 0
        for k in range(m+1):
            if k: s |= 1 << ranking[k-1]
            if good[s]: verified |= 1 << k
    assert verified == full
    return dict(points=points,epsilon=str(epsilon),minimum_rankings=len(chosen),
                total_component_span=scale,normalization='selectedRadius / (sum component spans / 2)',
                optimum_span_by_budget=opt,witness_rankings=rankings,
                maximal_budget_masks=list(covers),subsets_evaluated=size,
                maximum_antichain=max(map(len,paths)))


def main():
    p=argparse.ArgumentParser();p.add_argument('--samples',type=int,default=30)
    p.add_argument('--seed',type=int,default=91021);p.add_argument('--out',required=True)
    args=p.parse_args();rng=random.Random(args.seed);records=[];counts={}
    old=[-32,7,29,-7,-8,-13,18]
    for eps in [Fraction(0),Fraction(1,114),Fraction(1,57),Fraction(7,57)]:
        result=solve([[0]*7,old],eps);records.append(dict(family='known_chi5_validation',**result))
    assert [r['minimum_rankings'] for r in records] == [5,3,2,1]
    for m in [8,10,12]:
        for family in ['scalar','multi_support']:
            for sample in range(args.samples):
                points=[[0]*m]+[[rng.randint(-40,40) for _ in range(m)] for _ in range(1 if family=='scalar' else 4)]
                for eps in [Fraction(1,20),Fraction(1,10),Fraction(1,5)]:
                    r=solve(points,eps);key=f'{family}:m={m}:eps={eps}'
                    counts.setdefault(key,{})
                    k=r['minimum_rankings'];counts[key][k]=counts[key].get(k,0)+1
                    if sample == 0 or k>=3:
                        records.append(dict(family=family,sample=sample,**r))
            print(json.dumps(dict(family=family,m=m,completed_samples=args.samples)),flush=True)
    out=Path(args.out);out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(dict(evidence_class='EXACT_FINITE_INSTANCE_VALUES_RANDOM_SEARCH',
      universal_bound_proved=False,seed=args.seed,samples_per_family_width=args.samples,
      script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),counts=counts,records=records),indent=2)+'\n')
    print(json.dumps(counts,sort_keys=True),flush=True)
if __name__=='__main__':main()
