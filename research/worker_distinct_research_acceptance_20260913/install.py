from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent
REPO=Path('/Users/phanan/cig-amf-main')
DEST=REPO/'research/worker_distinct_research_acceptance_20260913'
SRC=REPO/'work/p13_conjectures'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'MANIFEST.json').read_text());pending=[]
for rel,rec in m['files'].items():
    p=R/rel;assert sha(p)==rec['sha256'],rel;pending.append((p,DEST/rel))
pending.append((R/'MANIFEST.json',DEST/'MANIFEST.json'))
for n in m['new_modules']:
    for ext in ['.lean','.olean']:pending.append((R/'build'/(n+ext),SRC/(n+ext)))
# Preflight everything before any write; never silently overwrite divergent work.
for p,d in pending:
    if d.exists() and sha(p)!=sha(d):raise RuntimeError('Conflicting existing artifact: '+str(d))
for p,d in pending:
    d.parent.mkdir(parents=True,exist_ok=True)
    if not d.exists():shutil.copy2(p,d)
for p,d in pending:assert sha(p)==sha(d),str(d)
receipt={'installed_root':str(DEST),'manifest_sha256':sha(R/'MANIFEST.json'),
         'new_modules':len(m['new_modules']),'new_axiom_audits':m['new_axiom_audits'],
         'verified_files':len(pending),'all_hashes_match':True}
(R/'INSTALL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
(DEST/'INSTALL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
