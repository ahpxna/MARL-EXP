from pathlib import Path
import subprocess,os,hashlib,json,re,time,sys
R=Path(__file__).resolve().parent;S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(R)]+[str(p/'.lake/build/lib/lean') for p in sorted((S/'.lake/packages').iterdir()) if p.is_dir()])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n in sys.argv[1:]:
 p=R/(n+'.lean');before=sha(p);start=time.time()
 with (R/(n+'.log')).open('w') as out:rc=subprocess.run(['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','-o',n+'.olean',n+'.lean'],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT).returncode
 log=(R/(n+'.log')).read_text();aud={a:[z.strip() for z in b.split(',') if z.strip()] for a,b in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)}
 ok=rc==0 and before==sha(p) and bool(aud) and all(not set(a)-{'propext','Classical.choice','Quot.sound'} for a in aud.values())
 d={'module':n,'accepted':ok,'lean_exit':rc,'source_sha256':before,'olean_sha256':sha(R/(n+'.olean')) if rc==0 else None,'log_sha256':sha(R/(n+'.log')),'axiom_audit':aud,'seconds':time.time()-start}
 (R/(n+'.receipt.json')).write_text(json.dumps(d,indent=2)+'\n');print(log);print(n,'ACCEPTED',ok,flush=True)
 if not ok:sys.exit(1)
