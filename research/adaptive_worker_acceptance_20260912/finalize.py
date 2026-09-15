from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parent;S=Path('/Users/phanan/cig-amf-main/work/p13_conjectures');B=R/'build'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
deps=json.loads((R/'dependency_manifest.json').read_text())['modules'];records=[]
for s in sorted(B.glob('*.lean')):
 rec=json.loads((R/'logs'/(s.stem+'.receipt.json')).read_text())
 assert rec['accepted'] and rec['dependencies_unchanged'] and rec['source_sha256']==sha(s),s
 assert rec['olean_sha256']==sha(s.with_suffix('.olean')) and rec['log_sha256']==sha(R/'logs'/(s.stem+'.log')),s
 assert rec['axiom_audit'] and not rec['nonstandard_axioms'],s
 for n,d in rec['dependencies'].items():
  assert sha(Path(d['olean_path']))==d['olean_sha256'],(s,n)
  if 'source_sha256' in d:
   p=next(p for p in [B/(n+'.lean'),R/'dependencies'/(n+'.lean')] if p.exists())
   assert sha(p)==d['source_sha256'],(s,n)
 records.append(rec)
for rec in deps:
 assert rec['accepted'] and rec['source_sha256']==sha(S/(rec['module']+'.lean'))
 assert rec['source_sha256']==sha(R/'dependencies'/(rec['module']+'.lean'))
 assert rec['olean_sha256']==sha(R/'dependencies'/(rec['module']+'.olean'))
 assert rec['log_sha256']==sha(R/'dependency_logs'/(rec['module']+'.log'))
 assert not rec['nonstandard_axioms']
# Complete recursive local graph including new modules, in topological order.
order=[]
def visit(n):
 if n in order:return
 p=next((p for p in [B/(n+'.lean'),R/'dependencies'/(n+'.lean')] if p.exists()),None)
 if p is None:return
 for d in re.findall(r'^import\s+[«]?([^»\s]+)',p.read_text(),re.M):visit(d)
 order.append(n)
for rec in records:visit(rec['module'])
assert set(order)=={x['module'] for x in records+deps}
(R/'dependency_order.json').write_text(json.dumps(order,indent=2)+'\n')
tool=Path('/Users/phanan/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean')
provenance={'lean_version':subprocess.check_output([str(tool),'--version'],text=True).strip(),'lean_binary':str(tool),'lean_binary_sha256':sha(tool),'lean_toolchain':(S/'lean-toolchain').read_text().strip(),'lake_manifest_sha256':sha(S/'lake-manifest.json'),'external_packages':json.loads((S/'lake-manifest.json').read_text())['packages']}
(R/'toolchain.json').write_text(json.dumps(provenance,indent=2)+'\n')
manifest={'accepted':True,'scope':'finite adaptive solver, causal tracking, label loss, and discovery stopping; no full Gamma stopping theorem','source_root':str(S),'modules':records,'local_dependencies':deps,'dependency_order_sha256':sha(R/'dependency_order.json'),'toolchain_sha256':sha(R/'toolchain.json'),'report_sha256':sha(R/'REPORT.md'),'new_theorem_audit_count':sum(len(x['axiom_audit']) for x in records),'dependency_audit_count':sum(len(x['axiom_audit']) for x in deps)}
(R/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(R/'RECEIPT.md').write_text(f'''# Adaptive worker acceptance receipt\n\nAccepted {len(records)} new Lean modules and {len(deps)} source-verified local dependencies.\n\n- Every accepted compile exits 0.\n- New final/theorem audits: {manifest['new_theorem_audit_count']}; dependency audits: {manifest['dependency_audit_count']}.\n- Only propext, Classical.choice, and Quot.sound occur in these audits.\n- No sorryAx or additional axioms accepted.\n- Per-module source, compiled output, log, and recursive local dependency hashes are in manifest.json and logs/*.receipt.json.\n- Source originals remain unchanged; new files are additive.\n- Full theorem assumptions, scope, and outstanding mathematical work are in REPORT.md.\n- Full adaptive likelihood stopping and expected Gamma rate remain unproved.\n\nManifest SHA-256: `{sha(R/'manifest.json')}`\n''')
print(json.dumps({'new_modules':len(records),'dependencies':len(deps),'new_audits':manifest['new_theorem_audit_count'],'dependency_audits':manifest['dependency_audit_count'],'manifest_sha256':sha(R/'manifest.json')},indent=2))
