from pathlib import Path
from collections import Counter
import re,json,hashlib
R=Path('/Users/phanan/cig-amf-main'); T=R/'research/papers/_tex'
def uncomment(s):
    return '\n'.join(re.split(r'(?<!\\)%',line,maxsplit=1)[0] for line in s.splitlines())
def escaped(s,i):
    k=i-1
    while k>=0 and s[k]=='\\':k-=1
    return (i-k-1)%2==1
out={}; bad=0
for p in [T/f'paper_{x}{y}.tex' for x in 'abc' for y in ('','_supplement')]:
    raw=p.read_text();s=uncomment(raw);errors=[];level=0
    for i,c in enumerate(s):
        if c in '{}' and not escaped(s,i):
            level+=1 if c=='{' else -1
            if level<0:errors.append('premature close brace');break
    if level:errors.append('brace balance '+str(level))
    stack=[]
    for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',s):
        cmd,env=m.groups()
        if cmd=='begin':stack.append(env)
        elif not stack or stack.pop()!=env:errors.append('environment mismatch '+env)
    if stack:errors.append('open environments '+str(stack))
    labels=Counter(re.findall(r'\\label\{([^}]+)\}',s))
    dup=[x for x,v in labels.items() if v>1]
    if dup:errors.append('duplicate labels '+str(dup))
    refs=set(re.findall(r'\\(?:eqref|ref|pageref|autoref)\{([^}]+)\}',s))
    miss=sorted(refs-set(labels))
    if miss:errors.append('missing refs '+str(miss))
    bib=set(re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}',s))
    cites=set(x.strip() for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',s) for x in group.split(','))
    if cites-bib:errors.append('missing cites '+str(sorted(cites-bib)))
    figures=re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}',s)
    for f in figures:
        if not any((base/f).exists() for base in (T.parent/'_figures',T/'figures',T)):
            errors.append('missing figure '+f)
    controls=[hex(ord(c)) for c in raw if ord(c)<32 and c not in '\n\t\r']
    if controls:errors.append('control characters '+str(controls))
    dollars=sum(c=='$' and not escaped(s,i) for i,c in enumerate(s))
    if dollars%2:errors.append('odd dollar count')
    if len(re.findall(r'(?<!\\)\\\[',s))!=len(re.findall(r'(?<!\\)\\\]',s)):errors.append('display delimiter mismatch')
    modules=sorted(set(re.findall(r'Lean(?:Paper|Unified)[A-Za-z0-9]+V\d+',s)))
    missingmod=[x for x in modules if not (R/'work/p13_conjectures'/f'{x}.lean').exists()]
    if missingmod:errors.append('missing modules '+str(missingmod))
    out[p.name]={'errors':errors,'labels':len(labels),'references':len(refs),'bibliography':len(bib),'figures':len(figures),'lean_modules':len(modules),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    bad+=len(errors)
(R/'research/audit_current_20260925/TEX_STATIC_CHECK.json').write_text(json.dumps({'not_a_latex_compile':True,'files':out},indent=2)+'\n')
for k,v in out.items():print(k,json.dumps(v))
raise SystemExit(bool(bad))
