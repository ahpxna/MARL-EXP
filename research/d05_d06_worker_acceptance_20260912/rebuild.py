from pathlib import Path
import hashlib,json,os,re,subprocess,time
ROOT=Path(__file__).resolve().parent
SRC=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
BUILD=ROOT/'build'; BUILD.mkdir(exist_ok=True)
LOG=ROOT/'logs'; LOG.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
seen=set(); order=[]; deps={}
def visit(n):
 if n in seen: return
 seen.add(n); f=SRC/(n+'.lean'); ds=[]
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    d=d.strip('«»')
    if (SRC/(d+'.lean')).exists(): ds.append(d); visit(d)
 deps[n]=ds; order.append(n)
for n in ['LeanD6ReferenceCertifiedPhaseValueV1','LeanD6ReferencePhaseWitnessV1']: visit(n)
for n in order: (BUILD/(n+'.lean')).write_bytes((SRC/(n+'.lean')).read_bytes())
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:
 (BUILD/n).write_bytes((SRC/n).read_bytes())
if not (BUILD/'.lake').exists(): (BUILD/'.lake').symlink_to(SRC/'.lake',target_is_directory=True)
env=dict(os.environ); env['LEAN_PATH']=':'.join([str(BUILD)]+[str(p/'.lake/build/lib/lean') for p in sorted((SRC/'.lake/packages').iterdir()) if p.is_dir()])
records=[]
for i,n in enumerate(order):
 f=BUILD/(n+'.lean'); start=time.time(); before=sha(f)
 cmd=['/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean','-o',n+'.olean',n+'.lean']
 print(f'[{i+1}/{len(order)}] {n}',flush=True)
 with (LOG/(n+'.log')).open('w') as out: proc=subprocess.run(cmd,cwd=BUILD,env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(LOG/(n+'.log')).read_text()
 audits={name:[a.strip() for a in axioms.split(',') if a.strip()] for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)}
 bad={n:a for n,a in audits.items() if set(a)-{'propext','Classical.choice','Quot.sound'}}
 record={'module':n,'command':cmd,'lean_exit':proc.returncode,'wall_seconds':round(time.time()-start,2),'source_sha256':before,'source_unchanged':before==sha(f),'original_source_unchanged':before==sha(SRC/f.name),'olean_sha256':sha(BUILD/(n+'.olean')) if proc.returncode==0 else None,'log_sha256':sha(LOG/(n+'.log')),'axiom_audit':audits,'nonstandard_axioms':bad,'dependencies':{d:{'source_sha256':sha(BUILD/(d+'.lean')),'olean_sha256':sha(BUILD/(d+'.olean'))} for d in deps[n]},'accepted':proc.returncode==0 and not bad and before==sha(f)}
 records.append(record); (ROOT/'manifest.json').write_text(json.dumps({'source_root':str(SRC),'build_root':str(BUILD),'modules':records,'complete':len(records)==len(order)},indent=2)+'\n')
 (LOG/(n+'.receipt.json')).write_text(json.dumps(record,indent=2)+'\n')
 print(f'EXIT={proc.returncode} seconds={record["wall_seconds"]} audited={len(audits)}',flush=True)
 if not record['accepted']: print(log,flush=True); raise SystemExit(1)
print('ALL_LOCAL_DEPENDENCIES_REBUILT',flush=True)
