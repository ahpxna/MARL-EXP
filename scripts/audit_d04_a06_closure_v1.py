#!/usr/bin/env python3
"""Audit the D04/A06 deliverable, not the entire repository or paper closure."""
from pathlib import Path
import argparse,datetime,hashlib,json,re
MODULES={
 'LeanD6ReferenceCenteredCompensatedV1':14,
 'LeanD6ReferenceCenteredGeometryV1':5,
 'LeanD6ReferenceRetainedOscillationV1':34,
 'LeanD6ReferenceMinimumBranchesV1':7,
 'LeanD6ReferenceMaximumBranchesV1':5,
 'LeanD6ReferenceFullCountLossV1':8,
 'LeanD6ReferenceLegalCountMinimumV1':3,
 'LeanD6CyclicConfidenceSequenceV1':10,
}
ALLOWED={'propext','Classical.choice','Quot.sound'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 root=a.root.resolve();work=root/'work/p13_conjectures'; rows=[]
 for name,expected in MODULES.items():
  row={'module':name,'expected_audits':expected,'failures':[]};rows.append(row);fail=row['failures']
  paths={ext:work/(name+ext) for ext in ['.lean','.olean','.compile.log','.compile.receipt.json']}
  for ext,p in paths.items():
   if not p.is_file():fail.append('MISSING:'+ext)
  if fail:continue
  src=paths['.lean'].read_text();log=paths['.compile.log'].read_text();receipt=json.loads(paths['.compile.receipt.json'].read_text());sha=hashlib.sha256(paths['.lean'].read_bytes()).hexdigest()
  row.update(source_sha256=sha,receipt=receipt)
  if receipt.get('lean_exit')!=0:fail.append('LEAN_EXIT')
  if receipt.get('source_unchanged') is not True:fail.append('SOURCE_CHANGED_DURING_COMPILE')
  if receipt.get('source_sha256_at_launch')!=sha:fail.append('RECEIPT_SOURCE_MISMATCH')
  if re.search(r':\d+:\d+: error',log):fail.append('ERROR_IN_LOG')
  if re.search(r'\bsorryAx\b',log):fail.append('SORRY_AXIOM')
  if paths['.olean'].stat().st_mtime_ns<paths['.lean'].stat().st_mtime_ns:fail.append('STALE_OLEAN')
  prints=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
  row['audit_theorems']=[{'name':n,'axioms':[s.strip() for s in ax.split(',') if s.strip()]} for n,ax in prints]
  if len(prints)!=expected or len(re.findall(r'^#print axioms ',src,re.M))!=expected:fail.append('AUDIT_COUNT')
  if len({n for n,_ in prints})!=expected:fail.append('DUPLICATE_AUDIT')
  for n,ax in prints:
   if not {s.strip() for s in ax.split(',') if s.strip()}<=ALLOWED:fail.append('NONSTANDARD_AXIOMS:'+n)
  for line in src.splitlines():
   if not line.startswith('import '):continue
   for imp in re.findall(r'«([^»]+)»|([A-Za-z_][A-Za-z0-9_]*)',line[7:]):
    dep=imp[0] or imp[1];ds=work/(dep+'.lean');do=work/(dep+'.olean')
    if ds.is_file():
     if not do.is_file():fail.append('MISSING_DEPENDENCY:'+dep)
     elif do.stat().st_mtime_ns<ds.stat().st_mtime_ns:fail.append('STALE_DEPENDENCY:'+dep)
     elif paths['.olean'].stat().st_mtime_ns<do.stat().st_mtime_ns:fail.append('DEPENDENCY_REBUILT_AFTER_MODULE:'+dep)
 result={'generated_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root':str(root),'scope':'Eight named D04/A06 modules; not whole-corpus or full-paper closure.','all_passed':all(not r['failures'] for r in rows),'audit_prints':sum(len(r.get('audit_theorems',[])) for r in rows),'modules':rows,'remaining':['D05 finite-group averaging and actual hidden-world minimax primal/dual bridge','A07-A10 full adaptive tracking, stopping-time/termination and expected Gamma rate']}
 a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'all_passed':result['all_passed'],'modules':len(rows),'audit_prints':result['audit_prints'],'failures':{r['module']:r['failures'] for r in rows if r['failures']},'out':str(a.out)},indent=2))
 raise SystemExit(0 if result['all_passed'] else 1)
if __name__=='__main__':main()
