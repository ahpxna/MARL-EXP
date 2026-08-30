"""Small finite search for rankability/co-extremizability counterexamples."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, itertools, json
from pathlib import Path
import numpy as np

from research_chains.finite_world import FiniteResponseWorld
from research_chains.structural import analyze_world
from research_chains.support import SupportModel
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='chain_structural_rankability_search_v2'


def run(mode='quick',seed=0,max_worlds=3000):
    rng=np.random.default_rng(seed); m=3; full=list(itertools.product((0,1),repeat=m)); slopes=(-2.0,-1.0,1.0,2.0)
    records=[]; counts={}
    if mode=='exhaustive3':
        supports=[tuple(a for bit,a in enumerate(full) if mask&(1<<bit)) for mask in range(1,1<<len(full))]
        slope_rows=list(itertools.product(slopes,repeat=m))
        iterator=((omega,s) for omega in supports for s in slope_rows)
    else:
        def gen():
            for _ in range(int(max_worlds)):
                omega=tuple(a for a in full if rng.random()<rng.uniform(0.2,0.9))
                if not omega: omega=(full[int(rng.integers(len(full)))],)
                s=tuple(float(rng.choice(slopes)) for _ in range(m)); yield omega,s
        iterator=gen()
    processed=0
    for omega,s in iterator:
        # Need both binary actions represented on each coordinate for nontrivial span.
        if any(len({a[j] for a in omega})<2 for j in range(m)): continue
        primitives=tuple(np.asarray([0.0,s[j]]) for j in range(m)); world=FiniteResponseWorld(SupportModel((2,)*m,omega,key='search'),primitives)
        result=analyze_world(world); key=tuple(result[k] for k in ('globally_coextremizable','all_subsets_modular','scalar_prefix_order_exists','topc_exact_all_budgets'))
        counts[str(key)]=counts.get(str(key),0)+1
        if len(records)<100 and (result['scalar_prefix_order_exists'] != result['globally_coextremizable'] or result['all_subsets_modular'] != result['globally_coextremizable']):
            records.append({'omega':[list(a) for a in omega],'slopes':list(s),**result})
        processed+=1
        if mode!='exhaustive3' and processed>=int(max_worlds): break
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'mode':mode,'processed_worlds':processed,'pattern_counts':counts,'interesting_examples':records}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--mode',choices=['quick','exhaustive3'],default='quick'); p.add_argument('--seed',type=int,default=0); p.add_argument('--max-worlds',type=int,default=3000); p.add_argument('--out',default='research/new_chains_v2/structural/summary.json'); a=p.parse_args(argv)
    payload=run(a.mode,a.seed,a.max_worlds); atomic_json(Path(a.out),payload); print(json.dumps({'protocol_version':payload['protocol_version'],'mode':payload['mode'],'processed_worlds':payload['processed_worlds'],'patterns':payload['pattern_counts'],'interesting_examples':len(payload['interesting_examples'])},indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
