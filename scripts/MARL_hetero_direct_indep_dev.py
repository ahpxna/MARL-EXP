#!/usr/bin/env python3
"""Independently tuned DIRECT budget-conditioned selector (critical path §4 step 3.4; B1 verdict §5).

The 'direct' policy of every earlier screen shared the critic whose epoch was selected for
repair_R1 (it only had its own tau).  Here the SAME trainer (MARL_hetero_mitigation_dev.run_job,
imported unchanged) selects the EPOCH with the DIRECT (unrestricted) operating-point metric at the
+84 total cap (bids charged), instead of the repair_R1 metric at +28.  Mechanism: during the epoch
loop, md.select_tau is wrapped so that the trainer's epoch-selection call (the only restrict=True
call made before the final load_state_dict) is answered with the direct metric; after training
(the first load_state_dict of the job) the wrapper is inert, so the reported repair_R1 / direct
tau selection and evaluation are exactly the original ones.
--learner mlp_top2_joint runs the stage-A pipeline of MARL_hetero_top2_joint_dev.py.
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import torch.nn as nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_mitigation_dev as md

OP_TOTAL = 84
_orig_select, _orig_run_job, _orig_load = md.select_tau, md.run_job, nn.Module.load_state_dict
_state = {'training': False, 'bid': 0}


def select_tau_wrapped(evs, anch, restrict, cap_extra):
    if _state['training'] and restrict:
        return _orig_select(evs, anch, False, OP_TOTAL - _state['bid'])
    return _orig_select(evs, anch, restrict, cap_extra)


def load_state_dict_wrapped(self, *a, **k):
    _state['training'] = False                      # epoch loop is over: evaluation is untouched
    return _orig_load(self, *a, **k)


def run_job_direct(G, learner, seed, out, epochs, threads):
    _state.update(training=True, bid=md.BID_BYTES.get(learner, 0))
    md.select_tau = select_tau_wrapped; nn.Module.load_state_dict = load_state_dict_wrapped
    try:
        return _orig_run_job(G, learner, seed, out, epochs, threads)
    finally:
        md.select_tau = _orig_select; nn.Module.load_state_dict = _orig_load; _state['training'] = False


def main(a):
    md.run_job = run_job_direct
    if a.learner == 'mlp_top2_joint':
        import scripts.MARL_hetero_top2_joint_dev as tj
        tj.main(argparse.Namespace(run=a.run, out=a.out, seeds=[0, 1, 2], epochs=40, epochs_a=4, threads=a.threads))
    else:
        md.main(argparse.Namespace(run=a.run, out=a.out, learners=[a.learner], seeds=[0, 1, 2], epochs=40, threads=a.threads))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--learner', required=True); ap.add_argument('--threads', type=int, default=3)
    main(ap.parse_args())
