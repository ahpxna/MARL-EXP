"""Read-only audit of saved evidence. No Lean compilation, sampling, LP/QP or experiment run.
Only new files in this audit directory are written. Independent Fraction KKT reconstruction,
CP recalculation, arithmetic summaries and byte-level gate/provenance checks.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import json, hashlib, statistics, datetime
from scipy.stats import beta
ROOT=Path(__file__).resolve().parents[2]
D=ROOT/'research/unified_20260919'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def get(n): return json.loads((D/n).read_text())
out={'snapshot':datetime.datetime.now().astimezone().isoformat(),'no_experiments_or_compilation':True}
# Independent certificate verification: use saved multipliers, never call proposer/solver.
a=get('paperA_frozen_proxy_exact.json'); total=0; famrows=[]
for fam in ['family1','family2']:
 for row in a[fam]:
  M=F(row['M']); theta=list(map(F,['0','1','1/2','0','3/4','1/2'] if fam=='family1' else ['0','1','3/4','0','1/2','1/4']))
  var=[F(1)]*6;var[5 if fam=='family1' else 1]=M
  certs=row['region_certificates']; assert {tuple(c['region']) for c in certs}==set(product(range(3),repeat=4)) and len(certs)==81
  vals=[]
  for c in certs:
   imax,imin,jmax,jmin=c['region']; rows=[]
   for side,hi,lo in [(0,imax,imin),(3,jmax,jmin)]:
    for i in range(3):
     if i!=hi:
      r=[F(0)]*6;r[side+i]+=1;r[side+hi]-=1;rows.append(r)
    for i in range(3):
     if i!=lo:
      r=[F(0)]*6;r[side+lo]+=1;r[side+i]-=1;rows.append(r)
   r=[F(0)]*6;r[imax]+=1;r[imin]-=1;r[3+jmax]-=1;r[3+jmin]+=1;rows.append(r)
   S=c['active'];mu=list(map(F,c['mu']));assert len(S)==len(mu) and len(S)==len(set(S)) and all(x>=0 for x in mu)
   x=[theta[i]-var[i]*sum(rows[k][i]*v for k,v in zip(S,mu)) for i in range(6)]
   slack=[sum(ri*xi for ri,xi in zip(r,x)) for r in rows]
   assert all(v<=0 for v in slack) and all(slack[k]*v==0 for k,v in zip(S,mu))
   assert all((x[i]-theta[i])/var[i]+sum(rows[k][i]*v for k,v in zip(S,mu))==0 for i in range(6))
   value=sum((xi-ti)**2/(2*vi) for xi,ti,vi in zip(x,theta,var)); assert value==F(c['value']);vals.append(value);total+=1
   if c['region']==row['argmin_region']: assert x==list(map(F,row['argmin_x']))
  jf=F(1,128) if fam=='family1' else 1/(8*(M+3));assert jf==F(row['J_frozen'])
  assert min(vals)==F(row['J_full']) and min(vals)/jf==F(row['ratio'])
  famrows.append({'family':fam,'M':int(M),'J_full':str(min(vals)),'J_frozen':str(jf),'ratio':str(min(vals)/jf)})
out['A_exact_KKT']={'regions_verified':total,'all_checks_passed':True,'cases':famrows}
# Current full and smoke gates, compare actual bytes rather than mtimes.
gates={}
for name in ['full7_20260925','smokeR2_20260925','smokeSHARP1_20260925']:
 p=ROOT/'work/gate_runs'/name; files=list(p.glob('*.lean')); changed=[]
 for f in files:
  src=ROOT/'work/p13_conjectures'/f.name
  if not src.exists() or sha(src)!=sha(f): changed.append(f.name)
 summary=p/'report/SUMMARY.txt'
 gates[name]={'snapshot_modules':len(files),'source_drift':changed,'summary':summary.read_text() if summary.exists() else None,
              'roots':(p/'report/ROOTS.list').read_text().splitlines()}
out['gates']=gates
paperfiles=list((ROOT/'work/p13_conjectures').glob('LeanPaper*.lean'))
covered=set()
for name,g in gates.items():
 if g['summary'] and 'PASS' in g['summary'] and not g['source_drift']:
  covered|={p.name for p in (ROOT/'work/gate_runs'/name).glob('*.lean')}
out['paper_modules']={'total':len(paperfiles),'covered_by_completed_matching_gates':sum(p.name in covered for p in paperfiles),'not_covered':[p.name for p in paperfiles if p.name not in covered]}
# SHA provenance of a selected set of headline data/figures.
pro=[]
for name,producer in [('paperA_frozen_proxy_exact.json','EXP_paperA_frozen_proxy_exact.py'),('paperA7_panel.json','EXP_paperA7_panel.py'),('paperA_deployable_paired.json','EXP_paperA_deployable_paired.py'),('paperB_decoder_leanfallback.json','EXP_paperB_decoder_leanfallback.py'),('paperC_formula_check.json','EXP_paperC_formula_check.py'),('paperC_perturbation.json','EXP_paperC_perturbation.py')]:
 d=get(name);pro.append({'artifact':name,'artifact_sha256':sha(D/name),'producer':producer,'stored_source_sha256':d.get('source_sha256'),'current_source_sha256':sha(ROOT/'scripts'/producer),'match':d.get('source_sha256')==sha(ROOT/'scripts'/producer)})
out['provenance']=pro
# 7200-run paired panel: restricted mean and accounting; don't drop censored runs.
a=get('paperA_deployable_paired.json');rr=[]
for r in a['rows']:
 taus=[x['tau'] for x in r['runs']];assert len(taus)==a['config']['n_runs']
 assert len({tuple(x['seed']) for x in r['runs']})==len(taus)
 assert all(abs(sum(x['counts'])-x['tau'])<1e-8 for x in r['runs'])
 assert sum(x['censored'] for x in r['runs'])==r['censored']
 assert sum(not x['censored'] and x['answer']!=r['correct_answer'] for x in r['runs'])==r['stopped_wrong']
 assert abs(statistics.mean(taus)-r['restricted_mean_tau'])<1e-8
 assert r['stopped']+r['censored']==len(taus) and all(0<t<=a['config']['budget'] for t in taus)
 rr.append({k:v for k,v in r.items() if k in ['r','M','swapped','rule','restricted_mean_tau','stopped','stopped_wrong','censored']})
out['A_paired']={'rows':rr,'total':sum(r['stopped']+r['censored'] for r in a['rows']),'censored':sum(r['censored'] for r in a['rows']),'stopped_wrong':sum(r['stopped_wrong'] for r in a['rows']),'rules_module_hash_match':a['rules_module_sha256']==sha(ROOT/'scripts/EXP_paperA_deployable.py')}
# Actual A7 code panel; count-check real observations and saved stopping margins.
a=get('paperA7_panel.json');rr=[];n=0;wrong=0;cens=0;sel=defaultdict(int)
for c in a['cells']:
 for arm,v in c['arms'].items():
  runs=v['runs'];ts=[]
  for r in runs:
   n+=1;ts.append(r['tau']);assert abs(sum(r['counts'])-r['tau'])<1e-7
   cens+=bool(r['censored']); wrong+=(not r['censored'] and r['answer']!=c['truth'])
   if not r['censored']:
    cert=r['stop_certificate'];assert cert['statistic']>cert['threshold'];assert abs(cert['margin']-(cert['statistic']-cert['threshold']))<1e-9
   for s in r.get('selection_trace',[]):sel[str((c['name'],s['selected'],s['kept']))]+=1
  rr.append({'world':c['name'],'arm':arm,'n':len(runs),'restricted_mean_tau':statistics.mean(ts),'censored':sum(bool(r['censored']) for r in runs)})
out['A7']={'rows':rr,'total':n,'wrong':wrong,'censored':cens,'selection_counts':dict(sel),'learner_hash_match':a['learner_source_sha256']==sha(ROOT/'scripts/EXP_paperA7_learner.py')}
# Formal decoder counts, BOTH CP tails, all worlds per budget; no sampling.
b=get('paperB_decoder_leanfallback.json');rows=b['results'];tail=.05/(2*len(rows));pan=defaultdict(lambda:defaultdict(dict));worst=0
for r in rows:
 k,n=r['bad'],r['reps'];lo=0. if k==0 else float(beta.ppf(tail,k,n-k+1));hi=1. if k==n else float(beta.isf(tail,k+1,n-k))
 worst=max(worst,abs(lo-r['err_lower_fw']),abs(hi-r['err_upper_fw']))
 assert worst<1e-10
 key=(r['m'],r['h'],r['decoder']);N=r['N_per_query'];w=r['world'];assert w not in pan[key][N];pan[key][N][w]=(lo,hi,r['total_budget'])
br=[]
for key,ns in sorted(pan.items()):
 m,h,dec=key;assert all(set(v)==set(range(1,m+1)) for v in ns.values())
 bounds={N:(max(x[0] for x in v.values()),max(x[1] for x in v.values())) for N,v in ns.items()}
 cert=next((N for N in sorted(ns) if bounds[N][1]<=b['delta_target']),None);pref=[]
 for N in sorted(ns):
  if bounds[N][0]>b['delta_target']:pref.append(N)
  else:break
 stored=next(c for c in b['certified']+b['censored'] if (c['m'],c['h'],c['decoder'])==key)
 assert (cert,pref)==(stored['certified_N'],stored['failed_prefix'])
 br.append({'m':m,'h':h,'decoder':dec,'certified_N':cert,'total_upper':None if cert is None else cert*(1 if dec=='safe' else m-1),'failed_prefix':pref})
out['B_formal_decoder']={'intervals':len(rows),'max_CP_difference':worst,'certified':sum(x['certified_N'] is not None for x in br),'no_certificate':sum(x['certified_N'] is None for x in br),'panels':br}
# Arithmetic vs saved LP results, not solving the LP again.
c=get('paperC_formula_check.json');wa=wp=0.
for row in c['rows']:
 m=row['m'];e=F(str(row['eta']));vf=F(2,(m+4)*(m-1));v=max(vf,4*(1-e)/(m*(m+4))) if m%2==0 else max((m+3-(m+1)*e)/(m*(m+4)),vf+max(F(0),1-e)/(m*(m+4)))
 post=F(2,m+4) if m%2==0 else (2+F(2,m)*max(F(0),1-e))/(m+4)
 assert abs(float(v)-row['formula_exante'])<1e-14 and abs(float(post)-row['formula_expost'])<1e-14
 wa=max(wa,abs(float(v)-row['lp_exante']));wp=max(wp,abs(float(post)-row['lp_expost']))
out['C_formula']={'rows':len(c['rows']),'sizes':c['ms'],'max_exante_difference':wa,'max_expost_difference':wp}
c=get('paperC_perturbation.json');prs=c['rows']+c['per_item_rows'];ratios=[]
for r in prs:
 E=3*r['l1']/min(r['D0'],r['D1']);drift=abs(r.get('V_recomputed',r.get('V_movingD'))-r['V0']);assert drift<=E+1e-8
 ratios.append(drift/E if E else 0)
out['C_perturbation']={'rows':len(prs),'violations_of_3_l1_over_min_D':0,'max_bound_fraction':max(ratios),'solver_not_reverified':True}
# Recovered original identity (content, not filenames).
rec=ROOT/'legacy/overwrite_incident_20260922/recovered_originals_20260923'
out['legacy']={'CFamily_exact_original':sha(rec/'LeanPaperCFamilyV1.original.lean')==sha(ROOT/'work/p13_conjectures/LeanPaperCFamilyV1.lean'),'BSafeOrder_original_has_no_distinctness_in_Together':'∀ θ ∈ H, ∀ lam ∈ H, s < sep θ lam' in (rec/'LeanPaperBSafeOrderV1.original.lean').read_text()}
target=Path(__file__).with_name('SAVED_EVIDENCE_VERIFICATION.json');target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k in ['snapshot','paper_modules','C_formula','C_perturbation','legacy']},indent=2))
print('KKT',total,'A paired',out['A_paired']['total'],'B CP',len(rows),'written',target)
