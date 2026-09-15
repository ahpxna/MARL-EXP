from pathlib import Path
import hashlib,json,shutil
R=Path(__file__).resolve().parent
S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures')
D=Path('/Users/phanan/cig-amf-main/research/d05_d06_worker_acceptance_20260912')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'manifest.json').read_text())
assert m['complete'] and m['original_sources_unchanged_at_final_check']
assert all(x['accepted'] for x in m['modules'])
assert not D.exists(), 'Receipt destination already exists; refusing overwrite'
for x in m['modules']:
 n=x['module']; assert sha(S/(n+'.lean'))==x['source_sha256'],f'Source changed: {n}'
 assert sha(R/'build'/(n+'.olean'))==x['olean_sha256'],f'Build artifact changed: {n}'
shutil.copytree(R,D,symlinks=True,ignore=shutil.ignore_patterns('*.draft*.log'))
updated=[]
for x in m['modules']:
 n=x['module']; dest=S/(n+'.olean')
 if not dest.exists() or sha(dest)!=x['olean_sha256']:
  if dest.exists():
   backup=D/'previous_oleans';backup.mkdir(exist_ok=True);shutil.copy2(dest,backup/dest.name)
  shutil.copy2(R/'build'/dest.name,dest);updated.append(n)
 assert sha(dest)==x['olean_sha256']
for x in m['modules']:
 n=x['module']
 if n in ['LeanD6ReferenceMatchingMinimaxV1','LeanD6ReferenceCertifiedPhaseValueV1','LeanD6ReferencePhysicalBoundsV1','LeanD6ReferencePhaseThresholdV1','LeanD6ReferencePhaseWitnessV1','LeanD6ReferencePhysicalCertificateV1']:
  shutil.copy2(R/'logs'/(n+'.log'), S/(n+'.compile.log'))
  receipt=dict(x,build_root=str(R/'build'),log=n+'.compile.log',installed_olean_path=str(S/(n+'.olean')))
  (S/(n+'.compile.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
installation={'accepted':True,'artifact_bundle':str(D),'compiled_at':str(R/'build'),'repo_work':str(S),'module_count':len(m['modules']),'source_unchanged':all(sha(S/(x['module']+'.lean'))==x['source_sha256'] for x in m['modules']),'all_repo_oleans_match_rebuilt_hashes':all(sha(S/(x['module']+'.olean'))==x['olean_sha256'] for x in m['modules']),'refreshed_oleans':updated,'manifest_sha256':sha(R/'manifest.json')}
assert installation['source_unchanged'] and installation['all_repo_oleans_match_rebuilt_hashes']
(D/'installation.json').write_text(json.dumps(installation,indent=2)+'\n')
(R/'installation.json').write_text(json.dumps(installation,indent=2)+'\n')
print(json.dumps(installation,indent=2))
