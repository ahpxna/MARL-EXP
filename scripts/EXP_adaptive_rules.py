"""ADAPTIVE: is the quota failure a property of the rule, or of integrality?

The paper refutes the per-horizon quota bound for largest-deficit-first, and then
asserts something broader in prose: that any rule serving whole samples and never
revoking them faces the same arithmetic, citing the apportionment impossibility.
That sentence has no experiment behind it. This supplies one.

Seven online rules are run on the same targets. Four are the classical
apportionment divisor methods, which is what makes the citation concrete rather
than decorative:

  largest_deficit   serve argmax_i (t w_i - N_i)          -- the paper's rule
  largest_relative  serve argmax_i (t w_i - N_i) / w_i    -- deficit per unit entitlement
  jefferson         serve argmax_i w_i / (N_i + 1)        -- D'Hondt
  webster           serve argmax_i w_i / (N_i + 1/2)      -- Sainte-Lague
  adams             serve argmax_i w_i / N_i              -- Adams (N_i = 0 first)
  smallest_share    serve argmin_i N_i / w_i              -- proportional fairness
  randomized        serve i with probability w_i          -- unbiased, seeded

Every rule is deterministic except the last, which is seeded and reported with
the seed. All arithmetic on deficits is exact rational; only the randomised rule
draws, and it draws from exact rational weights.

The quantity recorded per (target, rule) is the largest deficit reached over the
horizon and the first step at which it exceeds one. A rule that never exceeds one
on any target would be a counterexample to the prose claim and is what the
experiment is looking for.

Self-check: on the paper's own witness w = (17,1,1,3,1)/23 the largest-deficit
rule must exceed the bound first at t = 11, which is the published statement, and
the sweep is not reported unless it does.
"""
import json
import time
import argparse
import os
import sys
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 31337


def compositions(total, parts):
    """Every way of writing `total` as `parts` positive integers, up to order.

    Generated directly as non-decreasing tuples. The obvious implementation
    walks all C(total-1, parts-1) ordered compositions and keeps the sorted
    ones, which for this sweep means enumerating 442 million tuples to keep
    478 thousand -- a factor of 924 thrown away, and the reason the sweep used
    to take hours rather than minutes.
    """
    def gen(remaining, k, least):
        if k == 1:
            if remaining >= least:
                yield (remaining,)
            return
        top = remaining // k
        for first in range(least, top + 1):
            for rest in gen(remaining - first, k - 1, first):
                yield (first,) + rest
    return list(gen(total, parts, 1))


def _ceil(q):
    """Ceiling of an exact rational, without going through float."""
    return -((-q.numerator) // q.denominator)


def pick(rule, w, N, t, rng):
    K = len(w)
    if rule == 'largest_deficit':
        D = [t * w[i] - N[i] for i in range(K)]
        return D.index(max(D))
    if rule == 'largest_relative':
        D = [(t * w[i] - N[i]) / w[i] for i in range(K)]
        return D.index(max(D))
    if rule == 'jefferson':
        D = [w[i] / (N[i] + 1) for i in range(K)]
        return D.index(max(D))
    if rule == 'webster':
        D = [w[i] / (N[i] + F(1, 2)) for i in range(K)]
        return D.index(max(D))
    if rule == 'adams':
        zero = [i for i in range(K) if N[i] == 0]
        if zero:
            return max(zero, key=lambda i: w[i])
        D = [w[i] / N[i] for i in range(K)]
        return D.index(max(D))
    if rule == 'smallest_share':
        D = [N[i] / w[i] for i in range(K)]
        return D.index(min(D))
    if rule == 'quota_bny':
        # Balinski and Young's quota method (1975): Jefferson's rule restricted
        # to the arms that can take the next sample without passing their upper
        # quota at the new horizon. It is house-monotone by construction, since
        # samples are only ever added, and it stays within quota -- which is why
        # it belongs in this comparison. The apportionment literature settles
        # that those two properties are compatible, so the interesting question
        # is whether a rule holding both also holds the stronger per-arm bound.
        h = t + 1
        elig = [i for i in range(K) if N[i] + 1 <= _ceil(h * w[i])]
        # non-empty: sum_i ceil(h w_i) >= h = sum_i N_i + 1, so some arm has room
        return max((w[i] / (N[i] + 1), i) for i in elig)[1]
    if rule == 'randomized':
        u = F(int(rng.integers(0, 10 ** 9)), 10 ** 9)
        acc = F(0)
        for i in range(K):
            acc += w[i]
            if u < acc:
                return i
        return K - 1
    raise ValueError(rule)


def run(rule, w, T, rng=None):
    """Both quota directions over the horizon.

    The paper's bound is on the DEFICIT, t w_i - N_i: an arm served less than its
    entitlement. The opposite direction, N_i - t w_i, is the surplus. Apportionment
    theory separates them -- a divisor method can respect one and violate the
    other -- so measuring only the deficit cannot support a claim about every
    rule, and both are recorded here.
    """
    K = len(w)
    N = [0] * K
    worst_def = F(0); worst_sur = F(0)
    first_def = None; first_sur = None
    for t in range(T + 1):
        D = [t * w[i] - N[i] for i in range(K)]
        md = max(D); ms = max(-x for x in D)
        if md > worst_def:
            worst_def = md
        if ms > worst_sur:
            worst_sur = ms
        if md > 1 and first_def is None:
            first_def = t
        if ms > 1 and first_sur is None:
            first_sur = t
        if t < T:
            N[pick(rule, w, N, t, rng)] += 1
    return worst_def, first_def, worst_sur, first_sur


RULES = ('largest_deficit', 'largest_relative', 'jefferson', 'webster',
         'adams', 'smallest_share', 'randomized', 'quota_bny')


def main():
    import numpy as np
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--kmax', type=int, default=6)
    ap.add_argument('--dmax', type=int, default=40)
    ap.add_argument('--horizon', type=int, default=200)
    a = ap.parse_args()
    t0 = time.time()

    # ---------------- self-check against the published witness ----------
    w = [F(17, 23), F(1, 23), F(1, 23), F(3, 23), F(1, 23)]
    worst, first, _, _ = run('largest_deficit', w, 40)
    ok = (first == 11)
    print(f'self-check: published witness first exceeds the bound at t={first} '
          f'(worst {worst}) -> {"PASS" if ok else "FAIL"}', flush=True)
    if not ok:
        raise SystemExit('self-check failed; sweep not reported')

    rng = np.random.default_rng(MASTER_SEED)
    rows = []
    per_rule = {r: dict(checked=0, violating=0, worst=0.0, worst_at=None,
                        earliest=None, violating_surplus=0, worst_surplus=0.0,
                        earliest_surplus=None, violating_either=0)
                for r in RULES}
    for K in range(3, a.kmax + 1):
        for d in range(K, a.dmax + 1):
            for parts in compositions(d, K):
                w = [F(p, d) for p in parts]
                rec = dict(K=K, den=d, w=[str(x) for x in w])
                for rule in RULES:
                    wr, fv, ws, fs = run(rule, w, a.horizon, rng)
                    s = per_rule[rule]
                    s['checked'] += 1
                    rec[rule] = dict(worst=str(wr), worst_float=float(wr),
                                     first_violation=fv,
                                     worst_surplus=str(ws),
                                     worst_surplus_float=float(ws),
                                     first_surplus_violation=fs)
                    if fv is not None:
                        s['violating'] += 1
                        if float(wr) > s['worst']:
                            s['worst'] = float(wr)
                            s['worst_at'] = [K, d, [str(x) for x in w]]
                        if s['earliest'] is None or fv < s['earliest']:
                            s['earliest'] = fv
                    if fs is not None:
                        s['violating_surplus'] += 1
                        s['worst_surplus'] = max(s['worst_surplus'], float(ws))
                        if s['earliest_surplus'] is None or fs < s['earliest_surplus']:
                            s['earliest_surplus'] = fs
                    if fv is not None or fs is not None:
                        s['violating_either'] += 1
                if any(rec[r]['first_violation'] is not None for r in RULES):
                    rows.append(rec)
            print(f'K={K} d={d} checked={per_rule["largest_deficit"]["checked"]} '
                  f'{time.time()-t0:.0f}s', flush=True)

    for r in RULES:
        s = per_rule[r]
        s['fraction'] = s['violating'] / s['checked'] if s['checked'] else None
        s['fraction_surplus'] = (s['violating_surplus'] / s['checked']
                                 if s['checked'] else None)
        s['fraction_either'] = (s['violating_either'] / s['checked']
                                if s['checked'] else None)
    survivors = [r for r in RULES if per_rule[r]['violating'] == 0]
    survivors_both = [r for r in RULES if per_rule[r]['violating_either'] == 0]

    rows.sort(key=lambda x: -max(x[r]['worst_float'] for r in RULES))
    out = dict(provenance=_P.stamp(__file__),
               script='EXP_adaptive_rules.py',
               design='seven online allocation rules, four of them classical '
                      'apportionment divisor methods, run on every rational target '
                      'with K arms and denominator up to the limit, in exact rational '
                      'arithmetic; the question is whether any rule avoids the quota '
                      'failure rather than how badly one rule fails',
               master_seed=MASTER_SEED, rules=list(RULES),
               arms=list(range(3, a.kmax + 1)), denominators=f'K..{a.dmax}',
               horizon=a.horizon, per_rule=per_rule,
               rules_never_violating_deficit=survivors,
               rules_never_violating_either_direction=survivors_both,
               targets_with_some_violation=len(rows),
               self_check='PASS (published witness first exceeds at t=11)',
               top=rows[:30], wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out)
    for r in RULES:
        s = per_rule[r]
        print(f"  {r:17s} deficit {s['violating']:7d}/{s['checked']:<7d} "
              f"({100*(s['fraction'] or 0):5.1f}%) worst {s['worst']:7.4f} | "
              f"surplus {s['violating_surplus']:7d} "
              f"({100*(s['fraction_surplus'] or 0):5.1f}%) worst {s['worst_surplus']:7.4f}")
    print('never violated the deficit bound:', survivors or 'none')
    print('never violated either bound:', survivors_both or 'none')


if __name__ == '__main__':
    main()
