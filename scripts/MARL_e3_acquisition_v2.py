#!/usr/bin/env python3
"""Label-ACQUISITION ablation v2 (28/09, handoff F4): 'targeted' uses only the 2-bit gap BIN of the legal 1-byte bid
(thresholds = train-split quartiles, as the selector's bid encoding), not the full gap (v1 = privileged acquisition);
every run writes acq_manifest_<strategy>_s<seed>.json with the wrapper sha256, strategy, budget, subsample seed and
the per-state chosen candidate indices; a pool smaller than B is recorded (never silently).  Candidates are chosen
from permissible metadata (sets, bid) only; cont/joint labels are not read by the rule.

v1 description follows.
Label-ACQUISITION ablation on traffic (research/marl_budget/PROTOCOL_E3_DELAY_ACQ_20260928.md, part B).

The selector (MARL_e3_selector_train_v2.py, variant bid + response head, unchanged) is trained on TRAIN labels in
which every state keeps the prefix plus B candidates chosen by an acquisition strategy; the SELECT and DEV splits
keep every candidate, so tuning and evaluation are identical across strategies.  Same B for every strategy, so
the same number of labelled rollouts (simulator steps) per state.
  singleton  uniform among single-receiver one-swaps (importance-style acquisition)
  uniform    uniform among all candidates
  targeted   without replacement, probability proportional to sum over changed receivers of 1/(1 + bid gap)
             (legal bid information: decisions near a tie first)
  full       every candidate (reference; larger budget)
Subsampling rng = (init seed, state index): the same draw for every variant of one seed.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_selector_train_v2 as sv2

_orig_load = sv2.load
LOG = []
GAP_THR = None


def n_repl(c, P):
    return sum(len(set(s) - set(p)) for s, p in zip(c['sets'], P['sets']))


def subsample(st, strategy, B, rng):
    C = st['cands']; P = C[0]; idx = np.arange(1, len(C))
    if strategy == 'singleton':
        pool = np.array([k for k in idx if n_repl(C[k], P) == 1]); w = None
    elif strategy == 'uniform':
        pool = idx; w = None
    elif strategy == 'targeted':
        pool = idx
        gb = [int(np.searchsorted(GAP_THR, b['gap'])) for b in st['bid']]                 # the 2-bit bin actually transmitted
        w = np.array([sum(1.0 / (1.0 + gb[i]) for i, (s, p) in enumerate(zip(C[k]['sets'], P['sets'])) if set(s) != set(p))
                      for k in pool]) + 1e-9
        w = w / w.sum()
    else:
        raise ValueError(strategy)
    take = sorted(int(k) for k in rng.choice(pool, size=min(B, len(pool)), replace=False, p=w))
    LOG.append(dict(episode_id=st['episode_id'], t=st['t'], pool=int(len(pool)), chosen=take, short=bool(len(pool) < B)))
    return [P] + [C[k] for k in take]


def make_load(strategy, B, seed):
    def load(dirs):
        global GAP_THR
        S, ck = _orig_load(dirs)
        if dirs and all('labels_train' in str(d) for d in dirs):
            GAP_THR = np.quantile([b['gap'] for st in S for b in st['bid']], [0.25, 0.5, 0.75])   # same rule as the selector's bins
        if strategy != 'full' and dirs and all('labels_train' in str(d) for d in dirs):
            for k, st in enumerate(S):
                st['cands'] = subsample(st, strategy, B, np.random.default_rng([seed, k]))
        return S, ck
    return load


def main(a):
    sv2.load = make_load(a.strategy, a.budget, a.seed)
    sv2.main(argparse.Namespace(train=a.train, select=a.select, dev=a.dev, out=a.out, name=f'acq2_{a.strategy}', bid=True, resp=True,
                                seed=a.seed, epochs=a.epochs, lr=1e-3, hidden=128, threads=a.threads))
    man = dict(wrapper='scripts/MARL_e3_acquisition_v2.py', wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               trainer_sha256=hashlib.sha256((ROOT / 'scripts/MARL_e3_selector_train_v2.py').read_bytes()).hexdigest(),
               strategy=a.strategy, budget=a.budget, subsample_seed=[a.seed, 'state index'], gap_thresholds=None if GAP_THR is None else [float(x) for x in GAP_THR],
               states=len(LOG), states_short_of_budget=int(sum(x['short'] for x in LOG)),
               labelled_train_candidates=int(sum(len(x['chosen']) for x in LOG)) if LOG else None, per_state=LOG,
               note='select/dev keep full label tables (shared overhead, reported separately); offline replay of an acquisition rule')
    (Path(a.out) / f'acq_manifest_{a.strategy}_s{a.seed}.json').write_text(json.dumps(man))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--train', nargs='+', required=True); p.add_argument('--select', nargs='+', required=True); p.add_argument('--dev', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--strategy', choices=['singleton', 'uniform', 'targeted', 'full'], required=True)
    p.add_argument('--budget', type=int, default=24); p.add_argument('--seed', type=int, default=0); p.add_argument('--epochs', type=int, default=40)
    p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
