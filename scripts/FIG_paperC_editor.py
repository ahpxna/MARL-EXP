#!/usr/bin/env python3
"""Embed Paper C vector figures from theorem formulas and existing JSON only.

No solver, simulation, fit, or sampling is run. Markers are existing LP outputs;
lines are closed forms. Re-run with --write to refresh the marked inline block.
The saved manifest records every input hash and all numerical consistency checks.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, json, math, re, argparse

ROOT = Path('/Users/phanan/cig-amf-main')
DATA = ROOT / 'research/unified_20260919'
TEX = ROOT / 'research/papers/_tex/paper_c.tex'
NAMES = ['formula_check', 'typed_frontier', 'typed_transition', 'budget_recourse', 'perturbation', 'robustness']
DATASETS = {n: json.loads((DATA / f'paperC_{n}.json').read_text()) for n in NAMES}
CHECKS = []

def check(name, value, tolerance):
    CHECKS.append(dict(name=name, observed=value, tolerance=tolerance, passed=value <= tolerance))
    if value > tolerance:
        raise ValueError(f'{name}: {value} > {tolerance}')

def free(m): return 2 / ((m+4)*(m-1))
def front(m,e):
    if m % 2 == 0: return max(free(m),4*(1-e)/(m*(m+4)))
    return max((m+3-(m+1)*e)/(m*(m+4)),free(m)+max(1-e,0)/(m*(m+4)))
def aware(m,e):
    return (4*max(1-e,0) if m%2==0 else max(m+3-(m+1)*e,m+1-(m-1)*e,0))/(m*(m+4))
def post(m,e): return (2+(2*max(1-e,0)/m if m%2 else 0))/(m+4)
def free8(a):
    if a<=2: return 2*(a-1)/3
    if a<=5-2*math.sqrt(2): return 2*(3-a)/(5-a)
    if a<=17/7: return 2*a*(3-a)/(17-5*a)
    if a<=3: return 4/7
    return 2*(a-1)/7
def f8(a,e):
    l1=(a-1)*(1-e)/2
    l2=(5-a)/4-e*(a-1)/8
    if a<=2: return max(3*(a-1)/4-e*(a-1)/8,free8(a))/(4*(a+1))
    if a<=17/7:
        l3=(3-a)*(2*(a*a-2*a+3)-e*(a-1)*(3-a))/(2*(a-1)*(10-3*a))
        vals=[l2,l3,free8(a)]+([l1] if a>=7/3 else [])
    elif a<=53/21: vals=[l1,l2,free8(a)]
    else: vals=[l1,free8(a)]
    return max(vals)/(4*(a+1))
def f6(a,e):
    if a<=2: return max((a-1)*(2/3-e/6),(a-1)/2)/(2*a+4)
    A=(4-a)/3-e*(a-1)/6; B=(a-1)*(1-e)/3
    if a<=7/3:
        F=(a-1)*(3-a)/2
        vals=[A,F+(1-e)*(3-a)**2/6,F]
    elif a<13/5:
        F=2*(a-1)*(3-a)/(11-3*a)
        L=(a-1)*(3-a)*(2*a-e*(3-a))/(3*(15*a-3*a*a-16))
        vals=[A,L,F]+([B] if a>2.5 else [])
    elif a<=3: vals=[B,2/5]
    else: vals=[B,(a-1)/5]
    return max(vals)/(2*a+4)

def validate():
    rows=DATASETS['formula_check']['rows']
    check('stored parity ex-ante and ex-post vs theorem',max(max(abs(r['lp_exante']-front(r['m'],r['eta'])),abs(r['lp_expost']-post(r['m'],r['eta']))) for r in rows),1e-7)
    for name in ['typed_frontier','typed_transition']:
        obj=DATASETS[name]
        for counts,formula in [([1,1,2,2],f6),([2,2,2,2],f8)]:
            selected=[r for r in obj['rows'] if r['counts_+a_-a_+b_-b']==counts]
            errs=[abs(v-formula(float(Fraction(r['a_over_b'])),e)) for r in selected for e,v in zip(obj['eta_grid'],r['values'])]
            check(f'{name}: full frontier {counts}, {len(errs)} saved values',max(errs),1e-7)
    for ms,group in DATASETS['budget_recourse']['g_m'].items():
        m=int(ms)
        check(f'budget-aware m={m}: U and B vs theorem',max(max(abs(r['U']-front(m,r['eta'])),abs(r['B']-aware(m,r['eta']))) for r in group['rows']),1e-7)
        if m%2==0:
            check(f'even one-exchange m={m} vs theorem',max(abs(r['V']['1']-aware(m,r['eta'])) for r in group['rows']),1e-7)
    pert=DATASETS['perturbation']
    check('group perturbation count',abs(len(pert['rows'])-160),0)
    check('per-item perturbation count',abs(len(pert['per_item_rows'])-60),0)
    check('physical stability: all stored rows',max(r['drift_movingD']-3*r['l1']/min(r['D0'],r['D1']) for r in pert['rows']+pert['per_item_rows']),1e-7)

def grid(lo,hi,n=100): return [lo+(hi-lo)*i/n for i in range(n+1)]
def plot(points,style='',legend=None):
    c=' '.join(f'({x:.9g},{y:.9g})' for x,y in points)
    s='\\addplot+['+style+'] coordinates {'+c+'};\n'
    if legend is not None: s+='\\addlegendentry{'+legend+'}\n'
    return s
def axis(options): return '\\nextgroupplot['+options+']\n'
def figure(n,content,caption,label):
    w={2:'0.44',3:'0.285'}[n]
    return ('\\begin{figure*}[t]\n\\centering\n\\begin{tikzpicture}\n'
      '\\begin{groupplot}[group style={group size='+str(n)+' by 1,horizontal sep=1.35cm},'
      'width='+w+'\\textwidth,height=4.65cm,scale only axis=false,'
      'tick label style={font=\\scriptsize},label style={font=\\small},'
      'title style={font=\\small},legend style={font=\\scriptsize,draw=none,fill=white},'
      'grid=major,grid style={black!10},/tikz/mark size=1.5pt,unbounded coords=jump]\n'
      +content+'\\end{groupplot}\n\\end{tikzpicture}\n\\caption{'+caption+'}\n'
      '\\label{'+label+'}\n\\end{figure*}\n')

COLORS=['cblue','corange','cgreen','cpurple','cred','cteal']
def figures():
    validate()
    fs=[]
    # (1) Parity and timing, same observation-free mathematical objective.
    c=axis(r'title={(a) One order, every budget},xlabel={band $\eta$},ylabel={$V_m/V_m^{\rm free}$},xmin=0,xmax=1.2,ymin=0.9,legend columns=2,legend pos=north east')
    for color,m in zip(COLORS,[5,7,9,4,6,8]):
        x=sorted(set(grid(0,1.2,90)+([1-2/(m*(m-1)),1] if m%2 else [(m-2)/(2*(m-1))])))
        c+=plot([(e,front(m,e)/free(m)) for e in x],f'{color},no marks,thick'+(',dashed' if m%2==0 else ''),f'$m={m}$')
        c+=plot([(r['eta'],r['lp_exante']/free(m)) for r in DATASETS['formula_check']['rows'] if r['m']==m and r['eta']<=1.2],f'{color},only marks,mark=o,forget plot')
    c+=axis(r'title={(b) Budget chosen after the draw},xlabel={band $\eta$},ylabel={$V_m^{\rm post}/[2/(m+4)]$},xmin=0,xmax=1.2,ymin=0.98,ymax=1.36,legend columns=2,legend pos=north east')
    for color,m in zip(COLORS,[3,5,7,9,4]):
        c+=plot([(e,post(m,e)/(2/(m+4))) for e in [0,1,1.2]],f'{color},no marks,thick'+(',dashed' if m%2==0 else ''),f'$m={m}$')
        c+=plot([(r['eta'],r['lp_expost']/(2/(m+4))) for r in DATASETS['formula_check']['rows'] if r['m']==m and r['eta']<=1.2],f'{color},only marks,mark=o,forget plot')
    fs.append(figure(2,c,r'The cost of the marginal constraint depends on when the budget is chosen. Lines are Theorems~\ref{thm:even}, \ref{thm:odd} and~\ref{thm:expostband}; circles are stored floating-point LP values (\NUM). In (a), even sizes are dashed and odd sizes solid. Each panel uses its own unconstrained value as denominator: the ex-post denominator is $m-1$ times the ex-ante one. The small band price in (b) therefore does not mean a small absolute loss.','fig:ctheorems'))
    # (2) Heterogeneity, new exact 2222 frontier.
    c=axis(r'title={(a) Multiplicity changes the price},xlabel={magnitude ratio $a/b$},ylabel={$V_g(0)/V_g^{\rm free}$},xmin=1.4,xmax=3.2,ymin=1.05,ymax=1.85,legend pos=north west')
    x=sorted(set(grid(1.4,3.2,200)+[2,5-2*math.sqrt(2),7/3,2.5,13/5,17/7,3]))
    for form,counts,color in [(f6,[1,1,2,2],'cblue'),(f8,[2,2,2,2],'corange')]:
        c+=plot([(a,form(a,0)/form(a,8)) for a in x],f'{color},no marks,thick',str(tuple(counts)))
        c+=plot([(float(Fraction(r['a_over_b'])),r['price_V0_over_free']) for r in DATASETS['typed_transition']['rows'] if r['counts_+a_-a_+b_-b']==counts],f'{color},only marks,mark=o,forget plot')
    c+=axis(r'title={(b) Eight items: full band frontier},xlabel={band $\eta$},ylabel={$V_g(\eta)/V_g^{\rm free}$},xmin=0,xmax=1.2,ymin=0.98,ymax=1.8,legend columns=2,legend pos=north east')
    for color,a in zip(COLORS,[2,2.2,2.35,2.5,3]):
        # Include every pairwise line crossing in the plotted coordinates, preserving kinks.
        l1=((a-1)/2,-(a-1)/2);l2=((5-a)/4,-(a-1)/8)
        lines=[l1,l2,(free8(a),0)]
        if a<=2:lines=[(3*(a-1)/4,-(a-1)/8),(free8(a),0)]
        elif a<=17/7:lines.append(((3-a)*(a*a-2*a+3)/((a-1)*(10-3*a)),-(3-a)**2/(2*(10-3*a))))
        crossings=[(v[0]-u[0])/(u[1]-v[1]) for u in lines for v in lines if u[1]!=v[1]]
        x=sorted(set(grid(0,1.2,100)+[e for e in crossings if 0<=e<=1.2]))
        c+=plot([(e,f8(a,e)/(free8(a)/(4*(a+1)))) for e in x],f'{color},no marks,thick',f'$a/b={a:g}$')
        rs=[r for r in DATASETS['typed_transition']['rows'] if r['counts_+a_-a_+b_-b']==[2,2,2,2] and abs(float(Fraction(r['a_over_b']))-a)<1e-8]
        if rs:
            r=rs[0]
            c+=plot([(e,v/r['Vfree']) for j,(e,v) in enumerate(zip(DATASETS['typed_transition']['eta_grid'],r['values'])) if j%4==0],f'{color},only marks,mark=o,forget plot')
    fs.append(figure(2,c,r'Beyond the parity family. Exact curves from Theorems~\ref{thm:twomagprice}, \ref{thm:twomag1122} and~\ref{thm:twomag2222}; circles are the pre-existing ratio-refinement LP results. Both count patterns have even size, yet their prices are nonmonotone in $a/b$ and their active constraints change. In (b), all curves are proved for every band; sampled markers only check the transcription of the formulas.','fig:chetero'))
    # (3) Knowing vs editing. Odd R=1 remains numerical, stated explicitly.
    c=''
    for m in [8,7]:
        c+=axis('title={'+('(a) Even size: one exchange is proved' if m%2==0 else '(b) Odd size: one exchange is numerical')+r'},xlabel={band $\eta$},ylabel={value$/V_m^{\rm free}$},xmin=0,xmax=1.2,ymin=-0.08,legend pos=north east')
        x=sorted(set(grid(0,1.2,110)+[1,(m-2)/(2*(m-1)) if m%2==0 else 1-2/(m*(m-1)),(m+1)/(m-1)]))
        x=[e for e in x if e<=1.2]
        c+=plot([(e,front(m,e)/free(m)) for e in x],'cblue,no marks,thick',r'commit: $V_m$')
        c+=plot([(e,aware(m,e)/free(m)) for e in x],'corange,no marks,thick,dashed',r'know $k$: $B_m$')
        rs=DATASETS['budget_recourse']['g_m'][str(m)]['rows']
        c+=plot([(r['eta'],r['V']['1']/free(m)) for i,r in enumerate(rs) if i%6==0],'cgreen,only marks,mark=triangle',r'one edit: LP $V^{(1)}_m$')
        eta=(m-2)/(2*(m-1)) if m%2==0 else 1-2/(m*(m-1))
        c+=plot([(eta,0),(eta,front(m,eta)/free(m))],'black!55,no marks,densely dotted,forget plot')
    fs.append(figure(2,c,r'When commitment costs something, and what one edit recovers. Here $m=8$ (left) and $m=7$ (right). Solid and dashed curves are the proved universal and budget-aware values; the dotted vertical line is the exact onset of a positive gap. Triangles are saved one-exchange LP values. Their equality to $B_m$ is proved for every even size and band; for odd size past $\eta_t$ it is an observation on the sampled grid, not a theorem. Both the initial and edited laws obey the marginal band.','fig:crecourse'))
    # (4) Stability: all physical rows, attained search, theorem ball bounds.
    c=axis(r'title={(a) All saved perturbations},xlabel={envelope $3\Vert g-g\prime\Vert_1/d$},ylabel={observed value drift},xmin=0,ymin=0,legend pos=north west')
    pp=DATASETS['perturbation']; mx=max(3*r['l1']/min(r['D0'],r['D1']) for r in pp['rows']+pp['per_item_rows'])*1.03
    c+=plot([(0,0),(mx,mx)],'black!55,no marks,dashed',r'theorem envelope')
    for key,col,lab in [('rows','cblue','160 group'),('per_item_rows','corange','60 per-item')]:
        c+=plot([(3*r['l1']/min(r['D0'],r['D1']),r['drift_movingD']) for r in pp[key]],col+',only marks,mark=o',lab)
    c+=axis(r'title={(b) Search gives attained examples},xlabel={radius $\varepsilon$},ylabel={price ratio},xmode=log,xmin=0.018,xmax=1.8,ymin=0,legend pos=north east')
    for color,m in zip(COLORS,[5,6,7]):
        rs=[r for r in DATASETS['robustness']['rows'] if r['m']==m]
        c+=plot([(r['eps'],r['worst_ratio']) for r in rs],f'{color},only marks,mark=o',f'attained, $m={m}$')
        if m%2:
            c+=plot([(e,1/(4*e+4/(m-1))) for e in grid(.02,.25,25)],f'{color},no marks,dashed,forget plot')
    c+=axis(r'title={(c) Guarantee over a ball, $m=101$},xlabel={radius $\varepsilon$},ylabel={$\mathcal R_{101}(\varepsilon)$},xmode=log,ymode=log,xmin=0.0001,xmax=0.167,ymin=0.25,ymax=100,legend pos=south west')
    x=[10**(-4+(math.log10(1/6)+4)*i/160) for i in range(161)]
    c+=plot([(e,min(100,1/e)/16) for e in x],'cblue,no marks,thick','uniform lower bound')
    c+=plot([(e,min(104*100/(2*101),10/e)) for e in x],'corange,no marks,thick,dashed','constructive upper bound')
    c+=plot([(1/101,.25),(1/101,100)],'black!55,no marks,densely dotted,forget plot')
    fs.append(figure(3,c,r'Robustness with the quantifiers kept explicit. (a) All 220 saved perturbations, with recomputed baselines and moving normalisation, lie under the envelope; $d=\min(\Vert g\Vert_1,\Vert g\prime\Vert_1)$ and the largest drift/envelope ratio is 0.322. The producer could skip failures; the full prescribed row counts were checked, with none missing. (b) Search returns attained ratios, hence upper bounds on the infimum over the searched ball, not global minimisers. Dashed floors for odd sizes are shown only in their domain $\varepsilon\le1/4$. (c) The two bounds in Corollary~\ref{cor:robustball}, drawn only on $0<\varepsilon\le1/6$; these are theorem bounds, not measured worst-case optima. The vertical line marks $1/m$.','fig:cstab'))
    return '\n'.join(fs)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');ap.add_argument('--out',type=Path);args=ap.parse_args()
    out=figures()
    manifest={'generator':'scripts/FIG_paperC_editor.py','generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'computed_new_LP_or_samples':False,'inputs':{str(DATA/f'paperC_{n}.json'):hashlib.sha256((DATA/f'paperC_{n}.json').read_bytes()).hexdigest() for n in NAMES},
              'checks':CHECKS,'all_passed':True,'selection':'All 220 stability rows; selected m/ratios labelled in each panel; theorem curves and stored numerical markers distinct.'}
    if args.out:
        args.out.write_text(out)
        args.out.with_suffix('.json').write_text(json.dumps(manifest,indent=2)+'\n')
    if args.write:
        t=TEX.read_text();start='% BEGIN PAPER C INLINE FIGURES';end='% END PAPER C INLINE FIGURES'
        assert start in t and end in t
        t=t.split(start)[0]+start+'\n'+out+'\n'+end+t.split(end,1)[1]
        TEX.write_text(t)
        (ROOT/'research/papers/_figures/paperC_editor_figures_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'figures':4,'checks':len(CHECKS),'max_saved_frontier_error':max(c['observed'] for c in CHECKS if 'full frontier' in c['name']),'all_passed':True}))

if __name__=='__main__': main()
