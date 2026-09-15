from pathlib import Path
import os,subprocess,hashlib,json,time,re,sys
R=Path(__file__).resolve().parent;S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures');D=R/'dependencies';L=R/'dependency_logs'
manifest=json.loads((R/'dependency_manifest.json').read_text());known={x['module'] for x in manifest['modules']};order=[]
def visit(n):
 if n in known or n in order:return
 src=S/(n+'.lean')
 if not src.exists():return
 for dep in re.findall(r'^import\s+[«]?([^»\s]+)',src.read_text(),re.M):visit(dep)
 order.append(n)
for n in sys.argv[1:]:visit(n)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(D)]+[str(p/'.lake/build/lib/lean') for p in sorted((S/'.lake/packages').iterdir()) if p.is_dir()])
for n in order:
 src=S/(n+'.lean');(D/src.name).write_bytes(src.read_bytes());before=sha(src);start=time.time();print('REBUILD',n,flush=True)
 with (L/(n+'.log')).open('w') as f:rc=subprocess.run(['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','-o',n+'.olean',n+'.lean'],cwd=D,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 log=(L/(n+'.log')).read_text();aud={a:[z.strip() for z in b.split(',') if z.strip()] for a,b in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)};bad={a:b for a,b in aud.items() if set(b)-{'propext','Classical.choice','Quot.sound'}}
 rec={'module':n,'mode':'fresh isolated rebuild','lean_exit':rc,'source_sha256':before,'source_unchanged':sha(src)==before,'olean_sha256':sha(D/(n+'.olean')) if rc==0 else None,'log_sha256':sha(L/(n+'.log')),'axiom_audit':aud,'nonstandard_axioms':bad,'wall_seconds':round(time.time()-start,2),'accepted':rc==0 and not bad and sha(src)==before}
 (L/(n+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
 if not rec['accepted']:print(log);raise SystemExit(1)
 manifest['modules'].append(rec);(R/'dependency_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print('ACCEPTED',n,flush=True)
