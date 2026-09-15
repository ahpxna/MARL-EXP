from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
modules=[];audits=0
for src in sorted((R/'build').glob('*.lean')):
    rec=R/'logs'/(src.stem+'.receipt.json');d=json.loads(rec.read_text())
    assert d['accepted'] and d['lean_exit']==0,src.name
    assert not re.search(r'\b(sorry|admit|axiom)\b',src.read_text()),src.name
    assert sha(src)==d['source_sha256'] and sha(src.with_suffix('.olean'))==d['olean_sha256']
    assert sha(rec.with_suffix('').with_suffix('.log'))==d['log_sha256']
    assert d['source_unchanged'] and d['dependencies_unchanged']
    for dep,record in d['dependencies'].items():
        p=Path(record['olean_path']);assert sha(p)==record['olean_sha256'],dep
        if 'source_sha256' in record:assert sha(p.with_suffix('.lean'))==record['source_sha256'],dep
    assert d['axiom_audit'] and all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in d['axiom_audit'].values())
    audits+=len(d['axiom_audit']);modules.append(src.stem)
assert json.loads((R/'verify_games.json').read_text())['passed']
assert json.loads((R/'check_boundary_cases.json').read_text())['passed']
for n in ['approximate_game','calibration_game','nonadaptive_windows']:
    assert json.loads((R/(n+'.json')).read_text())['status']=='complete'
files=[]
for folder in ['build','logs','dependencies','inputs']:
    files.extend(p for p in (R/folder).rglob('*') if p.is_file())
files.extend(p for p in R.iterdir() if p.is_file() and p.suffix in {'.py','.json','.md','.txt'}
             and p.name not in {'MANIFEST.json','INSTALL_RECEIPT.json'})
manifest={'scope':'New distinct research checkpoint N1-N6; partial batch with explicit remaining work',
          'new_module_count':len(modules),'new_axiom_audits':audits,'new_modules':modules,
          'dependency_module_count':len(list((R/'dependencies').glob('*.lean'))),
          'files':{str(p.relative_to(R)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(set(files))}}
(R/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(modules),'modules',audits,'audits',len(files),'files; manifest',sha(R/'MANIFEST.json'))
