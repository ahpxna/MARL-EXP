"""Latency-premise benchmark on the cheap-pilot networks (read-only; writes one JSON).

One deployment step = one context.  Work is split at the moment the grant k is revealed.
PRE-GRANT (k unknown):
  priority     : score net forward -> argsort (what the prepared-priority method needs)
  critic_table : critic forward over all 2^m masks -> per-k argmax table
  direct_table : direct budget net forward over all budgets -> per-k top-k table
POST-GRANT (k known):
  prefix              : cut the prepared ranking
  table_lookup        : read the precomputed per-k answer (critic_table or direct_table)
  repair_R1_indexed   : R=1 repair scored from a PRE-computed critic vector (enumerate + index)
  repair_R1_fresh     : R=1 repair with a fresh critic call on the candidates only
  repair_R2_fresh     : R=2 repair with a fresh critic call
  unrestricted_fresh  : critic call on all k-sets after the grant (no tabulation)
Median of repeated timings, torch single thread, CPU.  Timing excludes packet transmission.
"""
import json, sys, time, statistics
from pathlib import Path
import numpy as np
import torch
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
from scripts.MARL_cheap_pilot import SelectorNet, load_dataset
from models.marl_revision_selector import reachable_sets
from models.marl_screening import mask_of, layer_masks

def med_us(fn, reps):
    fn()
    ts = []
    for _ in range(reps):
        t = time.perf_counter_ns(); fn(); ts.append(time.perf_counter_ns() - t)
    return statistics.median(ts) / 1000.0

def main(run, out):
    torch.set_num_threads(1)
    run = Path(run); manifest, rows, splits = load_dataset(run / 'data')
    m = rows[0]['m']
    ck = sorted((run / 'models').glob('seed_*.pt'))[0]
    blob = torch.load(ck, weights_only=False)
    nets = {}
    for kind, sd in blob['networks'].items():
        net = SelectorNet(blob['input_dim'], m, kind, blob['hidden']); net.load_state_dict(sd); net.eval(); nets[kind] = net
    mean = np.asarray(blob['normalization']['mean']); std = np.asarray(blob['normalization']['std'])
    i0 = splits['test'][0]
    x = torch.as_tensor(((np.asarray(rows[i0]['features']) - mean) / std)[None, :], dtype=torch.float32)
    allmasks = torch.tensor([[(s >> i) & 1 for i in range(m)] for s in range(1 << m)], dtype=torch.float32)
    budgets = torch.arange(1, m, dtype=torch.float32)[:, None] / m
    layers = {k: layer_masks(m, k) for k in range(1, m)}
    state = {}

    def priority():
        with torch.no_grad():
            w = nets['score'](x)[0].numpy()
        state['rank'] = tuple(int(a) for a in np.argsort(-w, kind='stable'))

    def critic_table():
        with torch.no_grad():
            fh = nets['value'](x, allmasks)[0].numpy()
        state['fh'] = fh
        state['ctab'] = {k: max(layers[k], key=lambda s: fh[s]) for k in layers}

    def direct_table():
        with torch.no_grad():
            lg = nets['direct'](x, budgets)[0].numpy()
        state['dtab'] = {k: int(np.sum(1 << np.argsort(-lg[k - 1], kind='stable')[:k])) for k in layers}

    reps_slow, reps_fast = 300, 3000
    pre = dict(priority=med_us(priority, reps_slow), critic_table=med_us(critic_table, reps_slow),
               direct_table=med_us(direct_table, reps_slow))
    post = {}
    for k in range(1, m):
        rank, fh, ctab = state['rank'], state['fh'], state['ctab']
        c1 = [mask_of(s) for s in reachable_sets(rank, k, 1)]
        c2 = [mask_of(s) for s in reachable_sets(rank, k, 2)]
        t1 = allmasks[c1]; t2 = allmasks[c2]; tl = allmasks[layers[k]]

        def fresh(t):
            def go():
                with torch.no_grad():
                    v = nets['value'](x, t)[0].numpy()
                return int(np.argmax(v))
            return go
        post[k] = dict(
            n_candidates=dict(R1=len(c1), R2=len(c2), all=len(layers[k])),
            prefix=med_us(lambda: mask_of(rank[:k]), reps_fast),
            table_lookup=med_us(lambda: ctab[k], reps_fast),
            repair_R1_indexed=med_us(lambda: max((mask_of(s) for s in reachable_sets(rank, k, 1)), key=lambda s: fh[s]), reps_fast // 3),
            repair_R1_fresh=med_us(fresh(t1), reps_slow),
            repair_R2_fresh=med_us(fresh(t2), reps_slow),
            unrestricted_fresh=med_us(fresh(tl), reps_slow))
    res = dict(checkpoint=str(ck), m=m, microseconds_pre_grant=pre, microseconds_post_grant_by_k=post,
               torch_threads=torch.get_num_threads(), note='median of repeated calls; CPU; excludes transmission')
    Path(out).write_text(json.dumps(res, indent=1))
    print(json.dumps(res, indent=1))

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
