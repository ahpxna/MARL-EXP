from pathlib import Path
import os,sys,subprocess,hashlib,json,time,re
R=Path(__file__).resolve().parent; B=R/'build';S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures');L=R/'logs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(B),str(R/'dependencies')]+[str(p/'.lake/build/lib/lean') for p in sorted((S/'.lake/packages').iterdir()) if p.is_dir()])
def dependencies(name):
 found={}
 def visit(n):
  for d in (B,R/'dependencies'):
   src=d/(n+'.lean')
   if src.exists():
    for dep in re.findall(r'^import\s+[«]?([^»\s]+)',src.read_text(),re.M):
     if dep in found:continue
     locations=[B,R/'dependencies']+[p/'.lake/build/lib/lean' for p in sorted((S/'.lake/packages').iterdir()) if p.is_dir()]
     obj=next((p/(dep.replace('.','/')+'.olean') for p in locations if (p/(dep.replace('.','/')+'.olean')).exists()),None)
     if obj is None:raise RuntimeError('Missing dependency '+dep)
     found[dep]={'olean_path':str(obj),'olean_sha256':sha(obj)}
     for local in (B,R/'dependencies'):
      ds=local/(dep+'.lean')
      if ds.exists():found[dep]['source_sha256']=sha(ds);visit(dep);break
    return
 visit(name)
 return dict(sorted(found.items()))
for n in sys.argv[1:]:
 n=n.removesuffix('.lean');s=B/(n+'.lean');before=sha(s);inputs=dependencies(n);start=time.time();cmd=['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','-o',n+'.olean',n+'.lean']
 with (L/(n+'.log')).open('w') as out:p=subprocess.run(cmd,cwd=B,env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(L/(n+'.log')).read_text();aud={name:[a.strip() for a in aa.split(',') if a.strip()] for name,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)};bad={n:a for n,a in aud.items() if set(a)-{'propext','Classical.choice','Quot.sound'}}
 rec={'module':n,'dependencies':inputs,'dependencies_unchanged':inputs==dependencies(n),'source_sha256':before,'source_unchanged':before==sha(s),'lean_exit':p.returncode,'olean_sha256':sha(B/(n+'.olean')) if p.returncode==0 else None,'log_sha256':sha(L/(n+'.log')),'axiom_audit':aud,'nonstandard_axioms':bad,'wall_seconds':round(time.time()-start,2),'accepted':p.returncode==0 and not bad and before==sha(s) and inputs==dependencies(n)}
 (L/(n+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(log);print(n,'EXIT',p.returncode,'ACCEPTED',rec['accepted'],flush=True)
 if not rec['accepted']:sys.exit(1)
