#!/usr/bin/env python3
"""Read-only source/results audit. Writes only its explicitly named JSON output.
No Lean compilation, LP optimization, or new learner simulation is performed.
"""
import argparse, hashlib, importlib.util, itertools, json, math, re, sys
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    sys.modules[name] = m
    spec.loader.exec_module(m)
    return m

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path('/Users/phanan/cig-amf-main'))
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args(); root=a.root.resolve()
    if a.out.exists(): raise SystemExit('Refusing to overwrite '+str(a.out))
    source_files={}
    def read(rel):
        p=root/rel; source_files[rel]=sha(p)
        return json.loads(p.read_text())
    out={'scope':'G02 headline modules; P12/P13/P16 exact replay; counterexamples and construction checks; existing Functional panel reanalysis. Not a whole-repository proof audit.',
         'new_simulations':False,'lean_compilation':False}

    table=read('research/worker_G02_table_20260915/G02_claim_theorem_table.json')
    lean=[]
    for name in sorted({n for row in table['rows'] for n in row['modules']}):
        p=root/'work/p13_conjectures'/name
        src=p.with_suffix('.lean'); ol=p.with_suffix('.olean'); log=p.with_suffix('.compile.log')
        rc=p.with_suffix('.compile.receipt.json')
        rr=json.loads(rc.read_text()) if rc.exists() else {}
        txt=log.read_text() if log.exists() else ''
        ax=re.findall(r'depends on axioms:\s*\[([^]]*)\]',txt)
        bad=[s for s in ax if set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',s))-{'propext','Classical.choice','Quot.sound'}]
        sh=sha(src); source_files[str(src.relative_to(root))]=sh
        lean.append({'module':name,'source_sha256':sh,'source_hash_in_receipt':sh in json.dumps(rr),
                     'olean_fresh':ol.exists() and ol.stat().st_mtime>=src.stat().st_mtime,
                     'nonempty_axiom_prints':len(ax),'nonstandard_axioms':bad,
                     'log_errors':len(re.findall(r'\berror:',txt)),'sorryAx_in_log':'sorryAx' in txt,
                     'receipt_exit_code':rr.get('lean_exit',rr.get('exit_code',rr.get('lean_exit_code')))})
    out['headline_compile_inventory']=lean

    j=read('research/worker_P12_master_20260915/P12_master_anchor_required.json')
    ds=[[F(x) for x in row] for row in j['alternatives']]
    up=j['upper']; low=j['lower']; lam=list(map(F,up['lambda'])); cuts=[(u,F(t)) for u,t in up['cuts']]
    assert len(lam)==len(cuts) and min(lam)>=0 and sum(lam)==1
    hs=[sum(lam[i]*(ds[u][e]-t)**2/2 for i,(u,t) in enumerate(cuts)) for e in range(4)]
    assert hs==list(map(F,up['H_over_kappa'])) and max(hs)==F(up['U0'])
    x=list(map(F,low['x'])); x0=F(low['x0']); K=sum(x)+x0
    assert min(x)>=0 and x0>0 and sum(x)+F(j['c0'])*x0==1 and K==F(low['K'])
    vals=[sum(xe*de*de/2 for xe,de in zip(x,d))-sum(xe*de for xe,de in zip(x,d))**2/(2*K) for d in ds]
    assert vals==list(map(F,low['I'])) and min(vals)==F(low['L1'])
    gap=min(vals)-max(hs); assert gap>0 and gap==F(j['conclusion']['L1_minus_U0'])
    out['P12']={'replay':'PASS','U0':float(max(hs)),'L1':float(min(vals)),'gap':float(gap),
                'scope':'finite three-alternative game; no assertion U0 equals anchor-free optimum; not a price threshold'}

    # P6 unrestricted threshold-class counterexample, using the stated additive-offset law.
    theta=list(map(F,[1,0,0,1])); group=[0,0,1,1]
    witnesses=[]
    for missing in [0,1]:
        delta=F(3,4)
        alt=[v-delta if group[i]==missing else v for i,v in enumerate(theta)]
        offset=[delta if g==missing else F(0) for g in range(2)]
        means=[alt[i]+offset[group[i]] for i in range(4)]
        old=[i for i,v in enumerate(theta) if v>F(1,2)]
        new=[i for i,v in enumerate(alt) if v>F(1,2)]
        assert means==theta and old!=new
        witnesses.append({'missing_control':missing,'theta':list(map(str,theta)),
                          'alternative':list(map(str,alt)),'alternative_offsets':list(map(str,offset)),
                          'ordinary_means_identical':True,'other_control_mean_identical':offset[1-missing]==0,
                          'truth_answer':old,'alternative_answer':new})
    out['P6_unrestricted_counterexamples']=witnesses
    # Cancelling M is feasible but need not maximize single-alternative information.
    anchor_free=F(9,8) # max variance of {-1,2}, divided by two
    x1=F(9,10); z=F(10); price=F(1,100)
    info=2*x1-(2*x1)**2/(2*(x1+z))
    assert x1+price*z==1 and info>anchor_free
    out['cancellation_is_not_optimality']={'d':['2','-1'],'cancelling_weights':['1/3','2/3'],
        'anchor_free_optimum':str(anchor_free),'price':str(price),'allocation_positive_query':str(x1),
        'anchor_exposure':str(z),'anchored_value':str(info)}

    # B-scalar's exchange term stays positive at x=0.
    out['D6_B_scalar_at_zero']={'q':3,'mu':'1/4','d':1,'x':'0','information':str(F(1,3)*F(1,4)**2/2)}
    out['functional_critical_gap']=[{'n':n,'c':'1','g_over_d':'1/2',
        'sandwich_ratio':str(F(16+4*n,16+n))} for n in [64,256,1024,4096]]

    checked=0
    for m in range(5,151):
        p=(m-1)//2; q=m-2-p; target=Counter([-3]+[-1]*p+[1]*q+[3])
        for j in range(1,m):
            if j%2:
                t=(j-1)//2; z=[-1,1]*t+[-3,3]; neg=p-t; pos=q-t
                z += [-1,1]*pos+[-1]*(neg-pos)
            else:
                t=j//2; z=[-1,1]*(t-1)+[-1,3,-3]; neg=p-t; pos=q-t+1
                z += [1,-1]*neg+[1]*(pos-neg)
            assert Counter(z)==target
            total=0; defects=[]
            for ell,value in enumerate(z,1):
                total+=value; excess=abs(total)-(ell%2)
                if excess: defects.append((ell,excess))
            assert defects==[(j,2)],(m,j,defects)
            checked+=1
    out['structural_explicit_ordering_check']={'m_range':[5,150],'rankings_checked':checked,
        'result':'PASS','scope':'finite test of an explicit proposed construction, not the all-m Lean theorem'}

    # Independent occupancy Markov recurrence, not the producer's inclusion-exclusion code.
    j=read('research/worker_P13_support_20260915/P13_support_decide_exponent.json')
    checks=0
    for cfg in j['configs']:
        aa=cfg['a']; bb=cfg['b']; pp=list(map(F,cfg['p'])); law={tuple(bb):F(1)}
        assert sum(b*p for b,p in zip(bb,pp))<=1
        saved={r['N']:r for r in cfg['N']}
        for n in range(max(saved)+1):
            if n in saved:
                rd=sum(pr*min(F(l,a+l) for a,l in zip(aa,ls)) for ls,pr in law.items())
                rr=sum(pr*(1-F(1,math.prod(math.comb(a+l,l) for a,l in zip(aa,ls)))) for ls,pr in law.items())
                ep=sum(pr*math.prod(ls) for ls,pr in law.items())
                s=sum(pp); bprod=math.prod(bb); k0=min(F(1,a+1) for a in aa)
                assert ep==bprod*(1-s)**n and k0*(1-s)**n<=rd<=ep
                assert abs(float(rd)-saved[n]['R_decide'])<1e-14
                assert abs(float(rr)-saved[n]['R_recover'])<1e-14
                checks+=1
            nxt={}
            for ls,pr in law.items():
                stay=1-sum(l*p for l,p in zip(ls,pp))
                nxt[ls]=nxt.get(ls,F(0))+pr*stay
                for i,l in enumerate(ls):
                    if l:
                        dest=list(ls);dest[i]-=1;dest=tuple(dest)
                        nxt[dest]=nxt.get(dest,F(0))+pr*l*pp[i]
            law=nxt;assert sum(law.values())==1 and min(law.values())>=0
    out['P13_independent_occupancy_replay']={'cells':checks,'result':'PASS',
        'scope':'validates occupancy law and numerical expectations, not the K-class minimax theorem'}

    # P16 restricted decisions are loss-equivalent to exact-size full-ground decisions.
    gp=root/'scripts/G4_fixed_world_observation_classes.py';source_files[str(gp.relative_to(root))]=sha(gp)
    g4=module(gp,'alignment_g4');cfg=g4.make_cfg(3,F(1,8),F(1))
    worlds=[frozenset([0,1,3]),frozenset([0,2,3])];tabs=[]
    for w in worlds:
        fw=g4.world_fn(cfg,w);qw={i:g4.response_levels(cfg,fw,i) for i in range(cfg['m'])}
        assert all(qw[i][u]==0 for i in range(cfg['m']) if i not in cfg['T'] for u in [0,1])
        tabs.append((fw,qw))
    j=read('research/worker_P16_query_20260915/P16_query_regret_chain.json');rows=[]
    for b in j['budgets']:
        budget=b['budget'];red=g4.decisions(cfg,budget);full=g4.decisions(cfg,budget,full_ground=True)
        lr=[[g4.compression_loss(cfg,fw,qw,s) for s in red] for fw,qw in tabs]
        lf=[[g4.compression_loss(cfg,fw,qw,s) for s in full] for fw,qw in tabs]
        for wi in range(2):
            for si,s in enumerate(full): assert lf[wi][si]==lr[wi][red.index(s&cfg['T'])]
        regs=[[v-min(row) for v in row] for row in lf]
        gamma=min(max(regs[0][i],regs[1][i]) for i in range(len(full)))
        assert gamma==F(b['gamma'])
        rows.append({'budget':budget,'reduced_decisions':len(red),'full_decisions':len(full),'gamma':str(gamma)})
    out['P16_full_decision_replay']={'result':'PASS','rows':rows,
        'scope':'geometry and reduction are valid; expected-regret and Taylor bounds still need proof'}

    p7=read('research/worker_P7_d6_fulldesign_20260914/P7_d6_full_design.json')
    masses=[sum(F(w) for lab,w in row['support']) for row in p7['cells']]
    out['P7_saved_certificate_surface']={'cells':len(masses),'all_saved_support_mass_one':all(v==1 for v in masses),
        'all_reported_lower_le_upper':all(F(r['Gamma_full_lower'])<=F(r['dual_upper']) for r in p7['cells']),
        'restricted_upper_saved':any('two_class_upper' in r for r in p7['cells']),
        'warning':'full_lower/two_class_value compares two lower bounds; not a strict-separation certificate'}
    out['P11_schedule_counterexample']={'counts_before':[50,1],'target':100,'new_weights':['1/10','9/10'],
        'requested_additions':[0,89],'actual_total_after':140,
        'meaning':'componentwise deficits can exceed the stated cumulative target; compare budgets under one explicit convention'}

    # Existing panel only; bootstrap does not generate new worlds or new learner outcomes.
    fp='research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json'
    if (root/fp).exists():
        import numpy as np
        j=read(fp);H=j['max_n'];runs=j['runs_by_variant']; summary={}
        for v,rr in runs.items():
            summary[v]={'n':len(rr),'certified':sum(r['certificate_emitted'] for r in rr),
                'false_safe':sum(r['false_safe'] is True for r in rr),
                'median_reported':j['by_variant'][v]['median_N_certificate']}
        x={(r['seed'],r['instance_id']):r for r in runs['C_lucb']}
        y={(r['seed'],r['instance_id']):r for r in runs['C_anytime']}
        assert x.keys()==y.keys(); keys=sorted(x)
        assert all(x[k].get('world_sha256') is not None and x[k]['world_sha256']==y[k]['world_sha256'] for k in keys)
        dt=np.array([(x[k]['N_certificate'] if x[k]['N_certificate'] is not None else H)-
                     (y[k]['N_certificate'] if y[k]['N_certificate'] is not None else H) for k in keys],float)
        dc=np.array([int(x[k]['certificate_emitted'])-int(y[k]['certificate_emitted']) for k in keys],float)
        rng=np.random.default_rng(20260915);bts=[];bcs=[]
        for _ in range(4000):
            ix=rng.integers(len(keys),size=len(keys));bts.append(float(dt[ix].mean()));bcs.append(float(dc[ix].mean()))
        paired={'comparison':'C_lucb minus C_anytime','restricted_time_horizon':H,'n':len(keys),
            'mean_restricted_time_difference':float(dt.mean()),'bootstrap_95':np.quantile(bts,[.025,.975]).tolist(),
            'certificate_fraction_difference':float(dc.mean()),'certificate_bootstrap_95':np.quantile(bcs,[.025,.975]).tolist(),
            'assumption':'paired iid generated instances; PRNG treated as sampling; conditional generator inference only',
            'bootstrap_replicates':4000,'bootstrap_seed':20260915}
        out['functional_panel_reanalysis']={'variants':summary,'paired':paired,'new_experiment':False,
            'warning':'does not retroactively make the run preregistered or establish superiority outside this generator'}

    out['source_sha256']=source_files
    out['audit_script_sha256']=sha(Path(__file__))
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'output':str(a.out),'headline_modules':len(lean),'nonempty_axiom_prints':sum(r['nonempty_axiom_prints'] for r in lean),
       'compile_inventory_pass':all(r['source_hash_in_receipt'] and r['olean_fresh'] and r['receipt_exit_code']==0 and not r['log_errors'] and not r['sorryAx_in_log'] and not r['nonstandard_axioms'] for r in lean),
       'P12':out['P12'],'P13':out['P13_independent_occupancy_replay'],'P16':out['P16_full_decision_replay'],
       'functional_paired':out.get('functional_panel_reanalysis',{}).get('paired')},indent=2))

if __name__=='__main__': main()
