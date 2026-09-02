"""One-command launcher for the post-P13 novelty-critical development labs.

This is orchestration only.  Each child runner keeps its own protocol version,
scientific scope, and provenance sidecar.  Historical result trees are never
modified unless the caller explicitly chooses that tree as --repo-root.
"""
from __future__ import annotations
import argparse,json,subprocess,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

PROFILES={
    'quick':{
        'tcc':50,'functional':60,'support':20,'structural':80,'d6':60,'query':100,
    },
    'screening':{
        'tcc':1000,'functional':2000,'support':500,'structural':2000,'d6':2000,'query':5000,
    },
}


def _cmd(module,args,out):
    return [sys.executable,'-m',module,*map(str,args),'--out',str(out)]


def main(argv=None):
    p=argparse.ArgumentParser()
    p.add_argument('--profile',choices=sorted(PROFILES),default='quick')
    p.add_argument('--repo-root',default=str(ROOT))
    p.add_argument('--out-dir',default='research/novelty_critical')
    p.add_argument('--continue-on-error',action='store_true')
    a=p.parse_args(argv)
    root=Path(a.repo_root).resolve(); outdir=Path(a.out_dir)
    if not outdir.is_absolute(): outdir=root/outdir
    outdir.mkdir(parents=True,exist_ok=True)
    n=PROFILES[a.profile]
    jobs=[
      ('MASTER','scripts.run_typed_certificate_completion_lab',['--instances',n['tcc'],'--seed',6101],outdir/'tcc.json'),
      ('FUNCTIONAL','scripts.run_functional_selective_maintenance_lab',['--instances',n['functional'],'--seed',6201],outdir/'functional_selective_maintenance.json'),
      ('SUPPORT','scripts.run_support_critical_identification_lab',['--instances',n['support'],'--seed',6301,'--m',4,'--k',2,'--epsilon',.05],outdir/'support_critical_identification.json'),
      ('STRUCTURAL','scripts.run_structural_prefix_cover_lab',['--instances',n['structural'],'--seed',6401,'--m-values',3,4,5,6],outdir/'structural_prefix_cover.json'),
      ('D6','scripts.run_d6_cost_aware_paec_lab',['--instances',n['d6'],'--seed',6501],outdir/'d6_cost_aware_paec.json'),
      ('QUERY','scripts.run_query_identifiability_lab',['--instances',n['query'],'--seed',6601],outdir/'query_identifiability.json'),
    ]
    rows=[]; t0=time.time()
    for chain,module,args,out in jobs:
        cmd=_cmd(module,args,out); t=time.time()
        cp=subprocess.run(cmd,cwd=root,text=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
        row={'chain':chain,'module':module,'output':str(out.relative_to(root) if out.is_relative_to(root) else out),'returncode':cp.returncode,'seconds':time.time()-t}
        if cp.returncode: row['stderr_tail']=cp.stderr[-4000:]
        rows.append(row)
        if cp.returncode and not a.continue_on_error: break
    summary={'schema':'novelty_critical_suite_v1','profile':a.profile,'repo_root':str(root),'all_passed':len(rows)==len(jobs) and all(r['returncode']==0 for r in rows),'total_seconds':time.time()-t0,'jobs':rows}
    (outdir/'SUITE_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    return 0 if summary['all_passed'] else 1

if __name__=='__main__': raise SystemExit(main())
