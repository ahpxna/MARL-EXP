#!/usr/bin/env python3
"""Same-byte QUEUE bid data for existing E3 continuation labels (handoff F3; TRAIN/SELECT/DEV only, never test seeds).

The stored labels do not contain the receiver's fresh own queue.  For every (episode, t) of a label directory this
replays the deterministic base trajectory (committed cached-queue prefix + the SAME frozen actor, exactly as the label
producer) and records, before transmission, each receiver's own total waiting from its OWN view:
    qbid_i = min(255, round(sum of lane_waiting))            (1 byte per receiver, 9 B + 1 B header = 10 B charged)
Self-check (abort): at every stored t the replayed committed order and capacities equal the stored ones.
Output: <parent>/qbid_<label dir name>/{qbid.jsonl.gz, manifest.json}; the label directory itself is not modified.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy, step_with

SOURCES = ['scripts/MARL_e3_queue_side.py', 'scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_e3_actor_train.py',
           'models/marl_comm_actor.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']
TEST_SEEDS = set(range(1301, 1317))


def main(a):
    L = Path(a.labels); man = json.loads((L / 'manifest.json').read_text())
    if man.get('self_check') != 'PASS':
        raise SystemExit('labels are not self-check PASS')
    out = L.parent / f'qbid_{L.name}'; out.mkdir(parents=True, exist_ok=False)   # NOT '<labels>_qbid': that matched the labels_train_* globs
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(man['args']['ckpt'], weights_only=False)
    need = defaultdict(dict)
    for line in gzip.open(L / 'labels.jsonl.gz', 'rt'):
        st = json.loads(line)
        if st['traffic_seed'] in TEST_SEEDS:
            raise SystemExit('refusing: test seeds must never be labelled here')
        need[(st['traffic_seed'], st['headway'])][st['t']] = (st['order'], st['K'])
    sc = Scenarios(out); fh = gzip.open(out / 'qbid.jsonl.gz', 'wt'); n = 0; t0 = time.perf_counter()
    for (seed, load), ts in sorted(need.items()):
        env, topo, _, _ = sc.env(seed, load); pol = Policy(ck, topo, env.action_interval); m = env.n_agents
        for t in range(max(ts) + 1):
            with no_oracle_access(env):
                order, K = grant(env)
                if t in ts:
                    if list(order) != ts[t][0] or K != ts[t][1]:
                        raise AssertionError(f'SELF-CHECK FAIL: seed{seed} load{load} t{t}: replay differs from the stored label state')
                    q = [int(min(255, round(float(np.asarray(env._build_view(i).lane_waiting).sum())))) for i in range(m)]
                    fh.write(json.dumps(dict(episode_id=f'seed{seed}_load{load:g}', t=t, qbid=q)) + '\n'); n += 1
            step_with(env, pol, prefix_sets(order, K))
    fh.close()
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', labels=str(L), labels_ckpt=man['args']['ckpt'],
        states=n, source_hashes=h0, seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, n, 'states', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--labels', required=True); main(p.parse_args())
