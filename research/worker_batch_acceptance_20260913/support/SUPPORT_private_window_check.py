#!/usr/bin/env python3
"""Exact finite checks of corrected private-window claim; not a general proof."""
from itertools import combinations
from pathlib import Path
import json,hashlib

def windows(m,L):return [frozenset((x+i)%m for i in range(L)) for x in range(m)]
def private_flags(family):
 return [bool(I-set().union(*(J for k,J in enumerate(family) if k!=i))) for i,I in enumerate(family)]
def bound(s,L):return (s//2)*(L+1)+(s%2)*L
old=[set(range(3)),set(range(2,5)),set(range(1,4))]
negative={'m':13,'L':3,'s':3,'windows':[sorted(x) for x in old],'private':private_flags(old),'union':len(set.union(*old)),'claimed':bound(3,3)}
assert sum(negative['private'])==2 and negative['union']<negative['claimed']
rows=[]
for m in range(3,15):
 for L in range(1,min(m,6)):
  for s in range(1,5):
   if m<s*L+1:continue
   best=m+1;witness=None;checked=0
   for f in combinations(windows(m,L),s):
    if not all(private_flags(f)):continue
    checked+=1;n=len(set().union(*f))
    assert n>=bound(s,L),(m,L,s,f,n)
    if n<best:best=n;witness=[sorted(I) for I in f]
   rows.append({'m':m,'L':L,'s':s,'families_checked':checked,'minimum_union':best,'lower':bound(s,L),'attaining_windows':witness,'equality':best==bound(s,L)})
p=Path(__file__)
out={'scope':'Exact enumeration; verifies these finite parameter cells only. Does not prove query-depth upper H or general all-private theorem.','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'refuted_s_minus_one_claim':negative,'all_private_checks':rows,'families_checked':sum(x['families_checked'] for x in rows),'all_cells_attain_bound':all(x['equality'] for x in rows)}
p.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'counterexample':negative,'parameter_cells':len(rows),'families_checked':out['families_checked'],'all_cells_attain_bound':out['all_cells_attain_bound']},indent=2))
