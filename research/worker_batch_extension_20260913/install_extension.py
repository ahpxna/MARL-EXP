from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent;repo=Path('/Users/phanan/cig-amf-main');dest=repo/'research/worker_batch_extension_20260913'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'extension_manifest.json').read_text());assert m['complete'];copies=[]
for rel,h in m['artifacts'].items():assert sha(R/rel)==h,rel
for rec in m['modules']:
 for ext,k in [('lean','source_sha256'),('olean','olean_sha256')]:
  src=R/rec['group']/(rec['module']+'.'+ext);target=repo/'work/p13_conjectures'/src.name
  assert sha(src)==rec[k]
  if target.exists():assert sha(target)==sha(src),str(target)
  else:copies.append((src,target))
for rel in list(m['artifacts'])+['extension_manifest.json','EXTENSION_RECEIPT.md']:
 src=R/rel;target=dest/rel
 if target.exists():assert sha(target)==sha(src),str(target)
 else:copies.append((src,target))
for name,item in m['external_inputs'].items():
 src=Path(item['path']);assert sha(src)==item['sha256'];target=dest/'inputs'/src.name
 if target.exists():assert sha(target)==sha(src),str(target)
 else:copies.append((src,target))
for src,target in copies:
 target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,target);assert sha(src)==sha(target)
r=dict(installed=True,modules=m['new_module_count'],audits=m['new_axiom_audit_count'],copied_files=len(copies),archive=str(dest),manifest_sha256=sha(R/'extension_manifest.json'))
(dest/'installation.json').write_text(json.dumps(r,indent=2)+'\n');(R/'extension_installation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
