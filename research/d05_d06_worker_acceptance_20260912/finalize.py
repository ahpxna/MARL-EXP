from pathlib import Path
import hashlib,json,os,re,subprocess,time
R=Path(__file__).resolve().parent; B=R/'build'; L=R/'logs'
S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
N='LeanD6ReferencePhysicalCertificateV1'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'manifest.json').read_text())
assert m['complete'] and all(x['accepted'] for x in m['modules'])
env=dict(os.environ); env['LEAN_PATH']=':'.join([str(B)]+[str(p/'.lake/build/lib/lean') for p in sorted((S/'.lake/packages').iterdir()) if p.is_dir()])
source=B/(N+'.lean'); before=sha(source); cmd=['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','-o',N+'.olean',N+'.lean']; start=time.time()
with (L/(N+'.log')).open('w') as out: p=subprocess.run(cmd,cwd=B,env=env,stdout=out,stderr=subprocess.STDOUT)
log=(L/(N+'.log')).read_text(); audits={n:[a.strip() for a in aa.split(',') if a.strip()] for n,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)}
bad={n:a for n,a in audits.items() if set(a)-{'propext','Classical.choice','Quot.sound'}}
rec={'module':N,'command':cmd,'lean_exit':p.returncode,'wall_seconds':round(time.time()-start,2),'source_sha256':before,'source_unchanged':before==sha(source),'olean_sha256':sha(B/(N+'.olean')) if p.returncode==0 else None,'log_sha256':sha(L/(N+'.log')),'axiom_audit':audits,'nonstandard_axioms':bad,'dependencies':{n:{'source_sha256':sha(B/(n+'.lean')),'olean_sha256':sha(B/(n+'.olean'))} for n in ['LeanD6ReferenceCertifiedPhaseValueV1','LeanD6ReferencePhaseWitnessV1','LeanD6ReferenceCenteredGeometryV1']},'accepted':p.returncode==0 and not bad and len(audits)==8 and before==sha(source)}
(L/(N+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
m['modules']=[x for x in m['modules'] if x['module']!=N]+[rec]
m['complete']=all(x['accepted'] for x in m['modules'])
m['original_sources_unchanged_at_final_check']=all(sha(S/(x['module']+'.lean'))==x['source_sha256'] for x in m['modules'] if x['module']!=N)
m['toolchain_record_sha256']=sha(R/'toolchain.json')
(R/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print(log); print('FINAL_EXIT',p.returncode,'ACCEPTED',rec['accepted'],flush=True)
raise SystemExit(0 if rec['accepted'] else 1)
