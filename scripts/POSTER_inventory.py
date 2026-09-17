#!/usr/bin/env python3
"""Build a per-section inventory: for each theorem the poster names, find its module and
count what that module actually contains.  Nothing here is estimated -- the declaration
names come from the Lean sources and the audited counts from the compile receipts."""
import json, re, glob
from pathlib import Path
W = Path('work/p13_conjectures')

def module_of(name):
    for f in glob.glob(str(W / '*.lean')):
        if re.search(rf'^(theorem|lemma|def|noncomputable def)\s+{re.escape(name)}\b',
                     Path(f).read_text(), re.M):
            return Path(f).stem
    return None

def module_stats(mod):
    src = (W / f'{mod}.lean')
    if not src.exists():
        return None
    t = src.read_text()
    thms = re.findall(r'^(?:theorem|lemma)\s+([A-Za-z_0-9\']+)', t, re.M)
    defs = re.findall(r'^(?:noncomputable def|def)\s+([A-Za-z_0-9\']+)', t, re.M)
    r = W / f'{mod}.compile.receipt.json'
    aud, acc = 0, False
    if r.exists():
        d = json.loads(r.read_text())
        aud, acc = d.get('audited_names', 0), bool(d.get('accepted'))
    return {'module': mod, 'theorems': len(thms), 'defs': len(defs),
            'audited': aud, 'accepted': acc, 'names': thms}

SECTIONS = json.loads(Path('research/papers/_figures/sections.json').read_text())

out = {}
for paper, steps in SECTIONS.items():
    rows = []
    for step, names in steps:
        mods, thms, defs, aud = set(), 0, 0, 0
        supporting = []
        for n in names:
            m = module_of(n)
            if m and m not in mods:
                mods.add(m)
                st = module_stats(m)
                if st:
                    thms += st['theorems']; defs += st['defs']; aud += st['audited']
                    supporting += [x for x in st['names'] if x not in names]
        rows.append({'step': step, 'cited': names, 'modules': sorted(mods),
                     'theorems': thms, 'defs': defs, 'audited': aud,
                     'supporting': supporting})
    out[paper] = rows
    print(f'--- {paper}')
    for r in rows:
        print(f"  {r['step'][:44]:46} cited {len(r['cited'])}  modules {len(r['modules'])}  "
              f"thms {r['theorems']:3d}  defs {r['defs']:2d}  audited {r['audited']:3d}")
Path('research/papers/_figures/inventory.json').write_text(json.dumps(out, indent=1))
print('\nartifact: research/papers/_figures/inventory.json')
