"""ADAPTIVE: check that the quota method holds the two properties it is claimed for.

The eight-rule sweep reports that Balinski and Young's quota method violates
neither the deficit bound nor the surplus bound on any target.  That is a
measurement, and on its own it invites the obvious objection: a rule can pass a
finite sweep by luck.

It does not pass by luck, and this separates the two reasons.  The rule is
house-monotone by construction, since samples are only ever added.  And it is
within quota in the apportionment sense,

    floor(t w_i) <= N_i(t) <= ceil(t w_i)   for every arm and every horizon,

which is STRICTLY STRONGER than the bound the paper is about: quota gives
|N_i(t) - t w_i| < 1, so the deficit bound and the surplus bound both follow.
The sweep therefore confirms a consequence rather than discovering a
coincidence, and a reader is entitled to see that stated separately from the
measurement.

Both properties are checked here directly on random targets, at every horizon
rather than at the end, so a violation anywhere in a trajectory is caught.
"""
import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P
import EXP_adaptive_rules as R

MASTER_SEED = 4423


def trajectory(rule, w, T, rng):
    K = len(w)
    N = [0] * K
    out = [list(N)]
    for t in range(T):
        N[R.pick(rule, w, N, t, rng)] += 1
        out.append(list(N))
    return out


def draw(rng, kmin, kmax, dmax):
    """A target, drawn skewed rather than uniform.

    A multinomial draw concentrates near the uniform target, and that is the
    easy regime: the failures this paper is about live on skewed targets, one
    arm carrying most of the weight and the rest at 1/d. Sampling the easy
    regime and reporting no violation would say nothing, which is what the
    self-check below exists to prevent.
    """
    K = int(rng.integers(kmin, kmax + 1))
    d = int(rng.integers(K, dmax + 1))
    while True:
        p = rng.dirichlet(np.full(K, 0.3))
        parts = np.maximum(1, np.floor(p * d).astype(int))
        short = d - int(parts.sum())
        if short >= 0:
            parts[int(np.argmax(parts))] += short
            return [F(int(x), d) for x in parts]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--targets', type=int, default=2000)
    ap.add_argument('--horizon', type=int, default=200)
    ap.add_argument('--kmax', type=int, default=12)
    ap.add_argument('--dmax', type=int, default=80)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    # ---------------- self-check: the properties must be falsifiable -----
    # the paper's own witness breaks the deficit bound at horizon eleven, so a
    # checker that reports no violation on it is not checking anything.
    chk = np.random.default_rng(MASTER_SEED + 1)
    witness = [F(17, 23), F(1, 23), F(1, 23), F(3, 23), F(1, 23)]
    saw_deficit_break = False
    for N in trajectory('largest_deficit', witness, 11, chk):
        t = sum(N)
        if any(t * witness[i] - N[i] > 1 for i in range(len(witness))):
            saw_deficit_break = True
            break
    print(f'self-check: the checker detects the known failure of '
          f'largest-deficit-first on its own witness -> {"PASS" if saw_deficit_break else "FAIL"}',
          flush=True)
    if not saw_deficit_break:
        raise SystemExit('checker never fires; results not reported')

    bad_mono = bad_quota = bad_deficit = bad_surplus = 0
    worst_dev = F(0)
    for n in range(a.targets):
        w = draw(rng, 3, a.kmax, a.dmax)
        tr = trajectory('quota_bny', w, a.horizon, rng)
        for prev, cur in zip(tr, tr[1:]):
            if any(y < x for x, y in zip(prev, cur)):
                bad_mono += 1
                break
        for t, N in enumerate(tr):
            for i in range(len(w)):
                q = t * w[i]
                if not (math.floor(q) <= N[i] <= math.ceil(q)):
                    bad_quota += 1
                    break
                dev = q - N[i]
                if dev > worst_dev:
                    worst_dev = dev
                if -dev > worst_dev:
                    worst_dev = -dev
                if dev > 1:
                    bad_deficit += 1
                if -dev > 1:
                    bad_surplus += 1
            else:
                continue
            break
        if (n + 1) % 500 == 0:
            print(f'  {n+1}/{a.targets}  {time.time()-t0:.0f}s', flush=True)

    ok = (bad_mono == 0 and bad_quota == 0 and bad_deficit == 0 and bad_surplus == 0)
    out = dict(provenance=_P.stamp(__file__), script='EXP_adaptive_quotacheck.py',
               design='house monotonicity and the apportionment quota property checked at '
                      'every horizon of every trajectory, for the Balinski-Young quota '
                      'method; quota implies the deficit and surplus bounds, so this says '
                      'the sweep confirms a consequence rather than a coincidence',
               master_seed=MASTER_SEED, targets=a.targets, horizon=a.horizon,
               kmax=a.kmax, dmax=a.dmax,
               self_check=dict(detects_known_failure=bool(saw_deficit_break)),
               house_monotonicity_violations=bad_mono,
               quota_violations=bad_quota,
               deficit_bound_violations=bad_deficit,
               surplus_bound_violations=bad_surplus,
               worst_absolute_deviation=str(worst_dev),
               worst_absolute_deviation_float=float(worst_dev),
               all_properties_held=bool(ok),
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(f'wrote {a.out}: monotonicity {bad_mono}, quota {bad_quota}, '
          f'deficit {bad_deficit}, surplus {bad_surplus} violations over '
          f'{a.targets} targets; worst |deviation| {worst_dev} '
          f'({float(worst_dev):.4f})')


if __name__ == '__main__':
    main()
