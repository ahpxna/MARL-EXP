"""Primitive-world semantic witnesses for query-sufficiency benchmarking."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, json, math
from pathlib import Path
import numpy as np
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='chain_e_primitive_semantic_lab_v2'


def mutual_information(joint):
    joint=np.asarray(joint,dtype=np.float64); joint=joint/joint.sum(); px=joint.sum(axis=1,keepdims=True); py=joint.sum(axis=0,keepdims=True)
    total=0.0
    for i in range(joint.shape[0]):
        for j in range(joint.shape[1]):
            p=joint[i,j]
            if p>0: total+=p*math.log(p/(px[i,0]*py[0,j]))
    return float(total)


def run():
    # Same response vector Q, different information structure generated from a primitive joint law.
    q=np.asarray([0.0,0.0])
    info_world_a=np.asarray([[0.5,0.0],[0.0,0.5]])  # perfect latent-observation dependence
    info_world_b=np.asarray([[0.25,0.25],[0.25,0.25]])  # independent
    ia,ib=mutual_information(info_world_a),mutual_information(info_world_b)
    # XOR joint response: every one-coordinate marginal under uniform complement is constant, joint varies.
    xor=np.asarray([[0.0,1.0],[1.0,0.0]])
    q0=xor.mean(axis=1); q1=xor.mean(axis=0)
    pairwise_zero=bool(np.allclose(q0,q0[0]) and np.allclose(q1,q1[0])); joint_nonconstant=bool(np.max(xor)>np.min(xor))
    gates={
        'same_Q_different_information': bool(np.allclose(q,q) and abs(ia-ib)>1e-12),
        'xor_pairwise_zero_joint_nonconstant': bool(pairwise_zero and joint_nonconstant),
    }
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'overall_status':'PASS' if all(gates.values()) else 'FAIL','gates':gates,'primitive_worlds':{'response_Q':q.tolist(),'information_world_a_joint':info_world_a.tolist(),'information_world_b_joint':info_world_b.tolist(),'information_values':[ia,ib],'xor_joint_response':xor.tolist(),'xor_pairwise_Q0':q0.tolist(),'xor_pairwise_Q1':q1.tolist()}}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--out',default='research/new_chains_v2/chain_e/summary.json'); a=p.parse_args(argv); payload=run(); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0 if payload['overall_status']=='PASS' else 2
if __name__=='__main__': raise SystemExit(main())
