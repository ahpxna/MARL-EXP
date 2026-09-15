from pathlib import Path
import os,subprocess,hashlib,json,time,re
R=Path(__file__).resolve().parent;S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures');B=R/'build';D=R/'dependencies';L=R/'dependency_logs';D.mkdir(exist_ok=True);L.mkdir(exist_ok=True)
order=json.loads((R/'dependency_order.json').read_text());order=[n for n in order if not (B/(n+'.lean')).exists()]
previous=Path('/Users/phanan/cig-amf-main/research/d05_d06_worker_acceptance_20260912');old={x['module']:x for x in json.loads((previous/'manifest.json').read_text())['modules']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(D)]+[str(p/'.lake/build/lib/lean') for p in sorted((S/'.lake/packages').iterdir()) if p.is_dir()]);records=[]
for idx,n in enumerate(order):
 source=S/(n+'.lean');snapshot=D/source.name;snapshot.write_bytes(source.read_bytes());before=sha(snapshot);start=time.time()
 print(f'[{idx+1}/{len(order)}] {n}',flush=True)
 if n in old and old[n]['accepted'] and old[n]['source_sha256']==before and sha(previous/'build'/(n+'.olean'))==old[n]['olean_sha256']:
  (D/(n+'.olean')).write_bytes((previous/'build'/(n+'.olean')).read_bytes());(L/(n+'.log')).write_bytes((previous/'logs'/(n+'.log')).read_bytes());rc=0;mode='reused hash-verified prior source rebuild';aud=old[n]['axiom_audit']
 else:
  cmd=['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','-o',n+'.olean',n+'.lean']
  with (L/(n+'.log')).open('w') as out:rc=subprocess.run(cmd,cwd=D,env=env,stdout=out,stderr=subprocess.STDOUT).returncode
  log=(L/(n+'.log')).read_text();aud={name:[a.strip() for a in aa.split(',') if a.strip()] for name,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)};mode='fresh isolated rebuild'
 bad={name:aa for name,aa in aud.items() if set(aa)-{'propext','Classical.choice','Quot.sound'}}
 rec={'module':n,'mode':mode,'lean_exit':rc,'source_sha256':before,'source_unchanged':before==sha(source),'olean_sha256':sha(D/(n+'.olean')) if rc==0 else None,'log_sha256':sha(L/(n+'.log')),'axiom_audit':aud,'nonstandard_axioms':bad,'wall_seconds':round(time.time()-start,2),'accepted':rc==0 and not bad and before==sha(source)}
 records.append(rec);(L/(n+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');(R/'dependency_manifest.json').write_text(json.dumps({'complete':len(records)==len(order),'source_root':str(S),'isolated_build':str(D),'modules':records},indent=2)+'\n')
 print('EXIT',rc,mode,'seconds',rec['wall_seconds'],flush=True)
 if not rec['accepted']:print((L/(n+'.log')).read_text());raise SystemExit(1)
print('DEPENDENCY_SOURCE_CLOSURE_VERIFIED',flush=True)
