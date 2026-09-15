#!/usr/bin/env python3
"""Detached parallel compile; records actual Lean exits and SHA-bound axiom receipts."""
import concurrent.futures,datetime,hashlib,json,os,pathlib,re,shutil,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[1]
WORK=ROOT/'work/p13_conjectures'
OUT=ROOT/'research/master_query_compile_20260914'
MODULES={'LeanMasterAnchorThresholdV1':12,'LeanQueryAffinityTestingV1':9}
STANDARD={'propext','Classical.choice','Quot.sound'}
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def build(name,expected):
 source=WORK/(name+'.lean'); log=WORK/(name+'.compile.log'); olean=WORK/(name+'.olean')
 before=sha(source); start=time.monotonic(); env=os.environ.copy()
 env['LEAN_PATH']=str(WORK)+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
 lake=shutil.which('lake') or str(pathlib.Path.home()/'.elan/bin/lake')
 with log.open('w') as f:
  job=subprocess.Popen([lake,'env','lean','-o',olean.name,source.name],cwd=WORK,env=env,stdout=f,stderr=subprocess.STDOUT)
  write(OUT/(name+'.running.json'),{'pid':job.pid,'module':name,'started_utc':now(),'source_sha256':before})
  code=job.wait()
 text=log.read_text(); after=sha(source)
 audits={n:[a.strip() for a in aa.split(',') if a.strip()] for n,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)}
 bad={n:a for n,a in audits.items() if not set(a)<=STANDARD}
 errors=len(re.findall(r'\berror:',text));fresh=olean.exists() and olean.stat().st_mtime>=source.stat().st_mtime
 record={'module':name,'finished_utc':now(),'lean_exit':code,'wall_seconds':round(time.monotonic()-start,2),
  'source_sha256_before':before,'source_sha256_after':after,'source_unchanged':before==after,
  'olean_newer_than_source':fresh,'errors':errors,'audited_names':len(audits),'expected_audits':expected,
  'axiom_audit':audits,'nonstandard_axioms':bad,'log':str(log),
  'accepted':code==0 and not errors and not bad and len(audits)==expected and before==after and fresh}
 write(WORK/(name+'.compile.receipt.json'),record)
 return record
OUT.mkdir(parents=True,exist_ok=True)
write(OUT/'status.json',{'state':'RUNNING','pid':os.getpid(),'started_utc':now(),'modules':list(MODULES)})
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 futures=[pool.submit(build,n,k) for n,k in MODULES.items()]
 results=[]
 for future in futures:
  try:results.append(future.result())
  except Exception as e:results.append({'accepted':False,'exception':repr(e)})
write(OUT/'status.json',{'state':'FINISHED','finished_utc':now(),'accepted':all(x['accepted'] for x in results),'results':results})
