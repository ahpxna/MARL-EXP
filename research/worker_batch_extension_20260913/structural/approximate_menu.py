"""Rational budget-bucket menu with a user-supplied approximate anchor oracle.

Contract: sorted c_i >= osc(f_i)/2, B=sum(c)>0, 0<=eta<eps, and
oracle(a, eta*B) returns a set S of size a with radius(S)<=OPT_a+eta*B.
The algorithm validates dimensions and arithmetic, but the oracle's accuracy
must be independently certified. Oracle calls are made once per nonempty bucket.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable,Iterable,Sequence

@dataclass(frozen=True)
class Menu:
    rankings: tuple[tuple[int,...],...]
    anchor_budgets: tuple[int,...]
    budget_ranking: tuple[int,...]
    potential: tuple[Fraction,...]
    normalizer: Fraction
    tolerance: Fraction
    oracle_slack: Fraction
    call_bound: int

    @property
    def oracle_calls(self)->int:return len(self.anchor_budgets)

def build_menu(c:Sequence[Fraction],eps:Fraction,eta:Fraction,
               oracle:Callable[[int,Fraction],Iterable[int]])->Menu:
    c=tuple(Fraction(x) for x in c);eps=Fraction(eps);eta=Fraction(eta)
    if not 0<=eta<eps:raise ValueError('Require 0 <= eta < eps')
    if any(x<0 for x in c) or list(c)!=sorted(c):raise ValueError('Radii must be nonnegative and sorted')
    B=sum(c,Fraction(0));m=len(c)
    if B<=0:raise ValueError('Positive normalizer required')
    width=(eps-eta)*B;potential=[Fraction(0)];buckets={}
    for k in range(m):potential.append(potential[-1]+c[k]+c[m-1-k])
    for k,p in enumerate(potential):buckets.setdefault(p//width,[]).append(k)
    rankings=[];calls=[];budget_ranking=[-1]*(m+1)
    for budgets in buckets.values():
        a=budgets[0];raw=tuple(oracle(a,eta*B))
        if any(type(i) is not int or not 0<=i<m for i in raw) or len(set(raw))!=a or len(raw)!=a:
            raise ValueError('Oracle must return exactly a distinct valid coordinates')
        S=set(raw);ranking=tuple(sorted(S)+[i for i in range(m) if i not in S])
        for k in budgets:budget_ranking[k]=len(rankings)
        rankings.append(ranking);calls.append(a)
    return Menu(tuple(rankings),tuple(calls),tuple(budget_ranking),tuple(potential),B,eps*B,eta*B,
                int(Fraction(2)/(eps-eta))+1)
