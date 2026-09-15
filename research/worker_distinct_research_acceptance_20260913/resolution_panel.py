"""N5 finite-panel resolution curves in native reward-count units.
Grid is fixed independently of targets. No world IDs or catalog keys in responses.
All collected units, including constant targets, are retained.
"""
from pathlib import Path
from fractions import Fraction as F
import importlib.util,json,hashlib,itertools,collections
ETA=list(map(F,['0','1/100','1/20','1/10','1/4','49/100','1/2','51/100','3/4','1','3/2','2']))
EPS=list(map(F,['0','1/10','1/4','1/2','3/5','1']))
repo=Path('/Users/phanan/cig-amf-main');helper=Path(__file__).parent/'inputs/QUERY_restricted_decoder_exact.py'
panel=Path(__file__).parent/'inputs/QUERY_natural_panel_v2.json'
spec=importlib.util.spec_from_file_location('panel_helper',helper);lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)
payload=json.loads(panel.read_text());units=lib.build_units(payload)

def run(features,target):
    groups=collections.defaultdict(list)
    for i,u in enumerate(units):groups[tuple(x for f in features for x in u[f])].append(i)
    points=list(groups);extremes=[]
    for v in points:
        inds=groups[v];lo=min(inds,key=lambda i:units[i][target]);hi=max(inds,key=lambda i:units[i][target])
        extremes.append((lo,hi))
    pairs=[]
    for a,p in enumerate(points):
        for b in range(a,len(points)):
            distance=max(abs(x-y) for x,y in zip(p,points[b]))
            inds=extremes[a]+extremes[b]
            lo=min(inds,key=lambda i:units[i][target]);hi=max(inds,key=lambda i:units[i][target])
            diameter=units[hi][target]-units[lo][target]
            # Same-group diameters also matter for distinct pairs of groups.
            pairs.append((F(distance),diameter,lo,hi,a,b))
    curve=[]
    for eta in ETA:
        chosen=max((p for p in pairs if p[0]<=2*eta),key=lambda p:p[1]);floor=chosen[1]/2
        # Certificates at noiseless-center observations only, NOT uniform over disturbances.
        radii=[]
        for a,point in enumerate(points):
            candidates=[i for b,other in enumerate(points) if max(abs(x-y) for x,y in zip(point,other))<=eta for i in extremes[b]]
            rad=(max(units[i][target] for i in candidates)-min(units[i][target] for i in candidates))/2
            radii.extend([rad]*len(groups[point]))
        assert len(radii)==len(units)
        curve.append({'eta':str(eta),'minimax_error':str(floor),'worst_unit_indices':list(chosen[2:4]),
            'noiseless_center_certificate_counts':{str(e):sum(v<=e for v in radii) for e in EPS}})
    critical=[]
    for eps in EPS:
        bad=[p for p in pairs if p[1]>2*eps]
        if bad:
            p=min(bad,key=lambda p:p[0]);critical.append({'epsilon':str(eps),'critical_eta':str(p[0]/2),
              'equality_fails':True,'witness_unit_indices':list(p[2:4])})
        else:critical.append({'epsilon':str(eps),'critical_eta':None,'meaning':'target tolerance needs no representation'})
    assert all(F(a['minimax_error'])<=F(b['minimax_error']) for a,b in zip(curve,curve[1:]))
    return {'features':features,'target':target,'dimensions':len(points[0]),'unique_vectors':len(points),
      'coordinate_units':'native reward counts; eta applies after feature computation','curve':curve,'critical_resolution':critical}

out={'population_units':len(units),'constant_horizon6_profiles':sum(len(set(u['RT']))==1 for u in units),
     'panel_sha256':hashlib.sha256(panel.read_bytes()).hexdigest(),'helper_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),
     'grid_policy':'fixed rational eta grid in reward units, declared before reading outcomes',
     'scope':'exact finite panel; no continuous-world or measured-noise generalization',
     'center_certificate_scope':'Counts at y=R(theta), not a probability or worst-case over all errors',
     'results':[run(f,t) for f in [('R1',),('R1','R2'),('c1',),('c1','c2')] for t in ['ateT','shapT']]}
assert len(units)==1600
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out['results']:print(r['features'],r['target'],r['unique_vectors'],[(v['eta'],v['minimax_error']) for v in r['curve']],flush=True)
