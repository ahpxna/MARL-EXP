"""Exact computation of chi for the source-audited staircase family."""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))

from research_chains.provenance import write_artifact_with_provenance
from research_chains.structural_staircase import staircase_exact_prefix_dimension

PROTOCOL_VERSION="structural_staircase_exact_v1"


def run(r_values=(1,2,3,4,5,6), verify_milp=True):
    rows=[]
    for r in map(int,r_values):
        t0=time.perf_counter()
        row=staircase_exact_prefix_dimension(r, verify_milp=bool(verify_milp))
        row["solve_seconds"]=float(time.perf_counter()-t0)
        rows.append(row)
    return {
        "protocol_version":PROTOCOL_VERSION,
        "development_only":True,
        "evidence_class":"EXACT_FINITE_THEOREM_DISCOVERY",
        "r_values":list(map(int,r_values)),
        "rows":rows,
        "observed_sequence":[int(x["dimension"]) for x in rows],
        "exact_chi_equals_r_on_tested_range":bool(all(x["equals_r"] for x in rows)),
        "all_dp_milp_agree":bool(all(x["dp_milp_agree"] for x in rows)),
        "all_designated_zero":bool(all(x["all_designated_zero"] for x in rows)),
        "all_designated_unique":bool(all(x["all_designated_unique"] for x in rows)),
        "all_designated_pairwise_incomparable":bool(all(x["designated_pairwise_incomparable"] for x in rows)),
        "scope":"finite exact computation; chi=r on tested r is discovery evidence, not a parametric proof",
        "next_formal_target":"construct r rankings for every r and prove PrefixCoverDimensionAtMost staircase 0 r",
    }


def main(argv=None):
    p=argparse.ArgumentParser()
    p.add_argument('--r-values',nargs='+',type=int,default=[1,2,3,4,5,6])
    p.add_argument('--no-milp',action='store_true')
    p.add_argument('--out',default='research/current_six_reports/structural/staircase_exact.json')
    a=p.parse_args(argv)
    payload=run(tuple(a.r_values),verify_milp=not a.no_milp)
    write_artifact_with_provenance(Path(a.out),payload,
        protocol={'protocol_version':PROTOCOL_VERSION,'r_values':a.r_values,'verify_milp':not a.no_milp},
        seed=None,evidence_class='EXACT_FINITE_THEOREM_DISCOVERY',chain='STRUCTURAL')
    print(json.dumps(payload,indent=2)); return 0

if __name__=='__main__': raise SystemExit(main())
