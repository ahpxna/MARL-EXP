"""Finalize only the six new extension modules and their checked closure."""
from pathlib import Path
import json,hashlib,re,subprocess,shutil
R=Path(__file__).resolve().parent;REPO=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
GROUPS={'structural':['LeanPrefixBudgetMetricCoverSlackV1','LeanStructuralApproximateAnchorV1','LeanStructuralApproximateMenuV1'],
        'static':['LeanD6UniformScaledBoundsV1'],'master':['LeanMasterFixedWorldResponseV1'],
        'functional':['LeanFunctionalWeightCertificatesV1']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
artifacts={};checked={};modules=[];deps={}
def record_file(p):artifacts[str(p.relative_to(R))]=sha(p)
for group,names in GROUPS.items():
 folder=R/group;up={}
 if (folder/'upstream_manifest.json').exists():
  u=json.loads((folder/'upstream_manifest.json').read_text());assert sha(Path(u['source_receipt'])/'manifest.json')==u['manifest_sha256'];up={v['module']:v for v in u['modules']};record_file(folder/'upstream_manifest.json')
 def visit(n):
  key=group+'/'+n
  if key in checked:return checked[key]
  p=folder/n;receipt=p.with_suffix('.receipt.json')
  if receipt.exists():
   d=json.loads(receipt.read_text());assert d['accepted'] and d['lean_exit']==0,key
   for ext,k in [('lean','source_sha256'),('olean','olean_sha256'),('log','log_sha256')]:
    f=p.with_suffix('.'+ext);assert sha(f)==d[k],(key,k);record_file(f)
   assert all(not set(a)-{'propext','Classical.choice','Quot.sound'} for a in d['axiom_audit'].values()),key
   record_file(receipt);origin='compiled in this staging directory'
  else:
   d=up[n];assert d['accepted'] and not d.get('nonstandard_axioms'),key
   for ext,k in [('lean','source_sha256'),('olean','olean_sha256')]:
    f=p.with_suffix('.'+ext);assert sha(f)==d[k],(key,k);record_file(f)
   origin=u['source_receipt']
  rec={'module':n,'group':group,'source_sha256':d['source_sha256'],'olean_sha256':d['olean_sha256'],'origin':origin,'axiom_audit':d['axiom_audit'],'imports':[]}
  checked[key]=rec
  for imp in re.findall(r'^import\s+[«"]?([^»"\s]+)',p.with_suffix('.lean').read_text(),re.M):
   if imp=='Mathlib' or imp.startswith('Mathlib.'):continue
   assert (folder/(imp+'.lean')).exists(),(key,imp)
   visit(imp);rec['imports'].append(group+'/'+imp)
  if n not in names:
   assert sha(REPO/(n+'.lean'))==d['source_sha256'],('dependency source changed',key)
   deps[key]=rec
  return rec
 for n in names:
  rec=visit(n);assert rec['axiom_audit'],n;modules.append(rec)
 record_file(folder/'compile.py')
# Exact finite experiments; preserve their source and data.
for group,files in {'structural':['approximate_menu.py','check_approximate_menu.py','check_approximate_menu.json','dependency_sources.json','dependency_order.json','build_dependencies.py'],
                    'master':['check_fixed_world.py','check_fixed_world.json'],
                    'query':['check_physical_horizon_repair.py','check_physical_horizon_repair.json']}.items():
 for name in files:record_file(R/group/name)
 for name in files:
  if name.startswith('check_') and name.endswith('.json'):
   d=json.loads((R/group/name).read_text());assert d['source_sha256']==sha((R/group/name).with_suffix('.py'))
query=json.loads((R/'query/check_physical_horizon_repair.json').read_text())
external={'query_panel':{'path':query['panel_path'],'sha256':query['panel_sha256']},'query_helper':{'path':str(REPO.parent.parent/'scripts/QUERY_restricted_decoder_exact.py'),'sha256':query['helper_source_sha256']}}
for item in external.values():assert sha(Path(item['path']))==item['sha256']
for name in ['EXTENSION_REPORT.md','toolchain.json','finalize_extension.py','install_extension.py']:record_file(R/name)
manifest={'complete':True,'scope':'Six-module extension; remaining programme obligations are in EXTENSION_REPORT.md','new_module_count':len(modules),'new_axiom_audit_count':sum(len(m['axiom_audit']) for m in modules),'modules':modules,'dependencies':deps,'artifacts':artifacts,'external_inputs':external,'toolchain':json.loads((R/'toolchain.json').read_text())}
(R/'extension_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(R/'EXTENSION_RECEIPT.md').write_text(f"# Extension acceptance receipt\n\nNew modules: {len(modules)}. New theorem audits: {manifest['new_axiom_audit_count']}. All exit zero, with source/olean/log hashes and transitive local source snapshots verified. All printed axioms are from propext, Classical.choice, Quot.sound.\n\nManifest SHA-256: `{sha(R/'extension_manifest.json')}`.\n\nThis is an incremental checkpoint, not completion of all eight packages. Read EXTENSION_REPORT.md for exact scopes and negative results.\n")
print(json.dumps(dict(accepted=True,modules=len(modules),audits=manifest['new_axiom_audit_count'],dependency_snapshots=len(deps),manifest_sha256=sha(R/'extension_manifest.json'))))
