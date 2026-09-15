from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent;S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures');DEST=S.parents[1]/'research/adaptive_worker_acceptance_20260912'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'manifest.json').read_text());assert m['accepted'];changes=[]
# Validate every original dependency and all staged artifacts before writes.
for x in m['local_dependencies']:
 assert sha(S/(x['module']+'.lean'))==x['source_sha256']
 assert sha(R/'dependencies'/(x['module']+'.olean'))==x['olean_sha256']
for x in m['modules']:
 for suffix,key in [('.lean','source_sha256'),('.olean','olean_sha256')]:
  src=R/'build'/(x['module']+suffix);assert sha(src)==x[key]
  dst=S/src.name
  if suffix=='.lean' and dst.exists():assert sha(dst)==x[key],f'Unexpected existing source {dst}'
if DEST.exists():
 assert (DEST/'manifest.json').exists() and sha(DEST/'manifest.json')==sha(R/'manifest.json'),'Receipt destination collision'
else:shutil.copytree(R,DEST)
backup=DEST/'previous_oleans';backup.mkdir(exist_ok=True)
for x in m['local_dependencies']:
 dst=S/(x['module']+'.olean');src=R/'dependencies'/dst.name
 if not dst.exists() or sha(dst)!=x['olean_sha256']:
  old=sha(dst) if dst.exists() else None
  if dst.exists():shutil.copy2(dst,backup/dst.name)
  shutil.copy2(src,dst);changes.append({'path':str(dst),'kind':'dependency_binary','previous_sha256':old,'sha256':sha(dst)})
for x in m['modules']:
 for suffix,key in [('.lean','source_sha256'),('.olean','olean_sha256')]:
  src=R/'build'/(x['module']+suffix);dst=S/src.name
  if not dst.exists() or sha(dst)!=x[key]:
   old=sha(dst) if dst.exists() else None
   if dst.exists():shutil.copy2(dst,backup/dst.name)
   shutil.copy2(src,dst);changes.append({'path':str(dst),'kind':'new_module','previous_sha256':old,'sha256':sha(dst)})
  assert sha(dst)==x[key]
for x in m['local_dependencies']:assert sha(S/(x['module']+'.olean'))==x['olean_sha256']
record={'accepted':True,'receipt':str(DEST),'manifest_sha256':sha(R/'manifest.json'),'changes':changes,'all_installed_source_and_binary_hashes_match':True}
(DEST/'installation.json').write_text(json.dumps(record,indent=2)+'\n');(R/'installation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'receipt':str(DEST),'changes':len(changes),'verified':True},indent=2))
