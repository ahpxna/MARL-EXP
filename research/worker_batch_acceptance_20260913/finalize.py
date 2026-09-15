from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parent
REPO=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
GROUPS={
 'functional':['LeanFunctionalExtremaSeparationV1','LeanFunctionalIntervalOracleV1','LeanFunctionalFullOracleV1'],
 'static':['LeanD6ScaledReferenceCoefficientsV1','LeanD6ScaledReferencePhaseV1','LeanD6ScaledReferenceErrorV1','LeanD6ScaledPhysicalLimitV1','LeanD6ScaledValueErrorV1'],
 'support':['LeanSupportPrivateWindowV1','LeanSupportLineUnionV1','LeanSupportKernelGeometryV1'],
 'query':['LeanQueryFiberRepairV1','LeanQueryScalarMinimaxV1']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_record(d,p):
 assert d['accepted'] and d['lean_exit']==0,(p,d)
 for ext,key in [('lean','source_sha256'),('olean','olean_sha256'),('log','log_sha256')]:assert sha(p.with_suffix('.'+ext))==d[key],(p,key)
 assert all(not set(a)-{'propext','Classical.choice','Quot.sound'} for a in d['axiom_audit'].values())
 return d
modules=[];dependencies={};checked={}
for group,names in GROUPS.items():
 folder=R/group;up={}
 if (folder/'upstream_manifest.json').exists():
  u=json.loads((folder/'upstream_manifest.json').read_text());receipt=Path(u['source_receipt'])
  assert sha(receipt/'manifest.json')==u['manifest_sha256']
  up={v['module']:v for v in u['modules']}
 def visit(n):
  key=group+'/'+n
  if key in checked:return checked[key]
  p=folder/n
  if p.with_suffix('.receipt.json').exists():
   d=check_record(json.loads(p.with_suffix('.receipt.json').read_text()),p)
   origin='compiled in this staging directory'
  else:
   d=up[n];assert d['accepted'] and not d.get('nonstandard_axioms')
   for ext,k in [('lean','source_sha256'),('olean','olean_sha256')]:assert sha(p.with_suffix('.'+ext))==d[k]
   assert sha(REPO/(n+'.lean'))==d['source_sha256']
   origin=u['source_receipt']
  record={'module':n,'group':group,'source_sha256':d['source_sha256'],'olean_sha256':d['olean_sha256'],'origin':origin,'imports':[]}
  checked[key]=record
  for imp in re.findall(r'^import\s+[«"]?([^»"\s]+)',p.with_suffix('.lean').read_text(),re.M):
   if imp=='Mathlib' or imp.startswith('Mathlib.'):continue
   assert (folder/(imp+'.lean')).exists(),(n,imp)
   visit(imp);record['imports'].append(group+'/'+imp)
  if n not in names:
   original=REPO/(n+'.lean');local=p.with_suffix('.lean')
   if sha(original)!=sha(local):
    original_text=original.read_text();local_text=local.read_text()
    assert group=='query' and local_text.startswith(original_text),(key,'unexpected dependency edit')
    tail=local_text[len(original_text):]
    assert all(not line.strip() or re.fullmatch(r'#print axioms [A-Za-z0-9_.]+',line.strip()) for line in tail.splitlines())
    record['original_source_sha256']=sha(original);record['difference']='appended audit commands only'
   dependencies[key]=record
  return record
 for n in names:
  record=visit(n);d=json.loads((folder/(n+'.receipt.json')).read_text());assert d['axiom_audit']
  modules.append({**record,'log_sha256':d['log_sha256'],'receipt_sha256':sha(folder/(n+'.receipt.json')),'axiom_audit':d['axiom_audit']})
ver=json.loads((R/'functional/exact_oracle_verification.json').read_text());assert ver['accepted']
assert sha(R/'functional/exact_oracle_certificates.json')==ver['certificate_sha256']
lean=Path('/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean')
toolchain={'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'lean_binary_sha256':sha(lean),'lean_toolchain':(REPO/'lean-toolchain').read_text().strip(),'lake_manifest_sha256':sha(REPO/'lake-manifest.json')}
(R/'toolchain.json').write_text(json.dumps(toolchain,indent=2)+'\n')
artifacts={}
for group in GROUPS:
 for p in sorted((R/group).glob('*')):
  if p.is_file() and p.suffix in ('.lean','.olean','.log','.json','.py'):artifacts[str(p.relative_to(R))]=sha(p)
for n in ['REPORT.md','toolchain.json','finalize.py','install.py']:artifacts[n]=sha(R/n)
manifest={'complete':True,'scope':'13-module incremental checkpoint, not completion of all eight packages','new_module_count':len(modules),'new_axiom_audit_count':sum(len(m['axiom_audit']) for m in modules),'modules':modules,'local_dependencies':dependencies,'artifacts':artifacts,'toolchain':toolchain,'exact_oracle_verification':ver}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
receipt=f'''# Acceptance receipt\n\nNew modules: {len(modules)}. New theorem axiom audits: {manifest['new_axiom_audit_count']}.\n\nAll selected modules exited zero; source, olean, log, receipt and local dependency hashes match. Printed dependencies contain only propext, Classical.choice and Quot.sound.\n\nManifest SHA-256: `{sha(R/'manifest.json')}`.\n\nThe rational oracle verifier accepted {ver['regions_verified']} regions across {ver['instances']} instances and rejected {ver['negative_controls_rejected']} corruptions. See REPORT.md for assumptions and uncompleted obligations. Rebuilt dependencies are excluded from new-module and new-audit counts.\n'''
(R/'RECEIPT.md').write_text(receipt)
print(json.dumps({'accepted':True,'modules':len(modules),'audits':manifest['new_axiom_audit_count'],'dependency_snapshots':len(dependencies),'manifest_sha256':sha(R/'manifest.json')}))
