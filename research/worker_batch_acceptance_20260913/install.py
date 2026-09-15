"""Install only this accepted incremental checkpoint; reject source collisions."""
from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent
repo=Path('/Users/phanan/cig-amf-main');dest=repo/'research/worker_batch_acceptance_20260913'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'manifest.json').read_text());assert m['complete']
for rel,h in m['artifacts'].items():assert sha(R/rel)==h,rel
new=[]
for rec in m['modules']:
 for ext,key in [('lean','source_sha256'),('olean','olean_sha256')]:
  src=R/rec['group']/(rec['module']+'.'+ext);target=repo/'work/p13_conjectures'/src.name
  assert sha(src)==rec[key]
  if target.exists():assert sha(target)==sha(src),f'Existing different file: {target}'
  else:new.append((src,target))
archive=[]
for rel in list(m['artifacts'])+['manifest.json','RECEIPT.md']:
 src=R/rel;target=dest/rel
 if target.exists():assert sha(target)==sha(src),f'Existing different archive: {target}'
 else:archive.append((src,target))
for src,target in new+archive:
 target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,target)
 assert sha(src)==sha(target)
result={'installed':True,'new_module_count':m['new_module_count'],'audit_count':m['new_axiom_audit_count'],'new_repo_files':len(new),'new_archive_files':len(archive),'archive':str(dest),'manifest_sha256':sha(R/'manifest.json')}
(dest/'installation.json').write_text(json.dumps(result,indent=2)+'\n')
(R/'installation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
