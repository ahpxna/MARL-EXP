"""Predetermined distance × horizon × continuation-policy signal test on RWARE.
Includes blocked/constant states. Positive-control fixtures, not natural traffic.
"""
import json,sys,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.run_query_signal_probe import delivery_opportunity,summarize
from scripts.run_external_query_transfer import _state_panel
from envs.external.runtime import maybe_reexec_in_external_runtime

def main():
    maybe_reexec_in_external_runtime(require_ready=True)
    from envs.external.registry import build_environment
    env=build_environment('rware',seed=91011,n_agents=5);banks={}
    out=ROOT/'research/high_risk_20260910/query_distance_horizon.json'
    for distance in [1,2,4]:
      for horizon in [1,distance,distance+1]:
       for policy in ['noop','forward']:
        key=f'd{distance}_h{horizon}_{policy}'
        if key in banks:continue
        rows=[]
        for s in range(6):
            env.reset(seed=91011+s)
            try:
                meta=delivery_opportunity(env,[1,2,3,4],91011+s,distance=distance)
                row=_state_panel(env,0,[1,2,3,4],2,information_budget=128,expected_candidates=4,
                    horizon=horizon,continuation_policy=policy)
                row['state_design']=meta
            except Exception as exc:
                row={'status':'BLOCKED','reason':f'{type(exc).__name__}: {exc}','matrix':{},'queries':{}}
            row['seed']=91011+s;rows.append(row)
        banks[key]=summarize(rows)
        payload=dict(evidence_class='DEVELOPMENT_PREDETERMINED_DISTANCE_POLICY_CONTROL',banks=banks,
            state_selection='No filtering by query outcomes; all six fixture attempts included in each cell',
            natural_trajectory_claim=False,forward_policy='frozen first non-idle action; not a learned delivery policy',
            script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(payload,indent=2)+'\n');tmp.replace(out)
        print(key,banks[key]['executable_states'],banks[key]['full_information_counts'],flush=True)
if __name__=='__main__':main()
