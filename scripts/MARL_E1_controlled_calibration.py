#!/usr/bin/env python3
"""E1 of MARL_FINAL_SCOPE: controlled calibration benchmark.

E1a  the EXACT model of LeanMarlRepairCalibrationV1 (T2): needle class, unit-Gaussian excess
     observations, uniform-gap gains so that every reachable non-prefix repair is ambiguous.
     Worst-case error (null world, needle worlds) of block tests with N total queries, versus
     the proved lower bound |Amb|((1-a)ln(1/a) - ln 2)/(beta^2/2) and the proved upper
     construction |Amb| ceil(8 ln(|Amb|/a)/beta^2).  Acquisition: targeted (queries only
     ambiguous repairs), uniform over ALL k-sets (symmetric proxy design), proxy-only
     (singleton / prefix queries, which carry no information in this class).
E1b  an executable-actor communication task (value generated, not assigned): senders observe
     x_j in {-1,+1}; the target is Y = sum_j g_j x_j + beta x_a x_b + sigma0 xi (a hidden pair
     (a,b) interacts, XOR-like: one member alone is worthless); the receiver is the Bayes
     decoder of Y from the heard signals; reward -(Y - Yhat)^2.  Hence
       f(S) = -sigma0^2 - sum_{j not in S} g_j^2 - beta^2 [ {a,b} not subset of S ].
     A calibration query is a PAIRED rollout of S against the prefix P on the same draw.
     The prefix is top-k by first-order importance g_j^2.  Methods output a set in F_R(P):
       proxy      spends N on singleton importance queries, then picks by first-order value
       uniform    spreads N over all of F_R(P) \\ {P}
       targeted   spreads N over the ambiguous repairs (first-order deficit < beta_max^2)
       adaptive   successive elimination over the ambiguous repairs, same N
       oracle     true best in F_R(P)
     Reported: global regret (vs best k-set) = geometric floor + reachable regret, by R and N.
Self-check (refuses to write results if it fails): the closed-form f matches Monte-Carlo
rollouts of the Bayes decoder for random sets.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
MIN_PER = 5          # minimum rollouts per scored candidate before an edit may be made


# ------------------------------------------------------------------------------------------ E1a
def e1a(rng, trials, alpha):
    settings = [(6, 3, 1), (8, 4, 1), (6, 3, 2), (8, 4, 2), (10, 5, 2)]
    out = []
    for m, k, R in settings:
        n_amb = sum(math.comb(k, r) * math.comb(m - k, r) for r in range(1, R + 1))
        gamma, eps = 1.0, 0.5
        beta = gamma * R + eps + 1.0
        n_ksets = math.comb(m, k)
        lower = n_amb * max(0.0, (1 - alpha) * math.log(1 / alpha) - math.log(2)) / (beta ** 2 / 2)
        upper = n_amb * math.ceil(8 * math.log(max(n_amb, 1) / alpha) / beta ** 2)
        curves = {}
        grid = sorted(set(int(x) for x in np.unique(np.round(np.geomspace(max(n_amb, 1), 400 * n_amb, 24)))))
        for method in ('targeted', 'uniform_all_ksets', 'proxy_only'):
            errs = []
            for N in grid:
                per = N // n_amb if method == 'targeted' else (N // n_ksets if method == 'uniform_all_ksets' else 0)
                if per == 0:
                    errs.append(dict(N=N, null=0.0, needle=1.0, worst=1.0)); continue
                sd = 1.0 / math.sqrt(per)
                null_means = rng.normal(0.0, sd, size=(trials, n_amb))
                null_err = float(np.mean((null_means > beta / 2).any(1)))
                nd = rng.normal(0.0, sd, size=(trials, n_amb)); nd[:, 0] += beta
                fired = nd > beta / 2
                ok = fired[:, 0] & ~fired[:, 1:].any(1)
                needle_err = float(1 - ok.mean())
                errs.append(dict(N=N, null=null_err, needle=needle_err, worst=max(null_err, needle_err)))
            curves[method] = errs
        first_ok = {mth: next((e['N'] for e in c if e['worst'] <= alpha), None) for mth, c in curves.items()}
        out.append(dict(m=m, k=k, R=R, n_amb=n_amb, n_ksets=n_ksets, beta=beta, gamma=gamma, eps=eps, alpha=alpha,
                        proved_lower=lower, proved_upper=upper, first_N_at_alpha=first_ok, curves=curves))
    return out


# ------------------------------------------------------------------------------------------ E1b
class Task:
    def __init__(self, g2, beta2, sigma0, pair):
        self.g = np.sqrt(np.asarray(g2, float)); self.g2 = np.asarray(g2, float)
        self.beta = math.sqrt(beta2); self.beta2 = beta2; self.sigma0 = sigma0; self.a, self.b = pair
        self.m = len(g2)

    def f(self, S):
        S = set(S)
        return (-self.sigma0 ** 2 - sum(self.g2[j] for j in range(self.m) if j not in S)
                - (0.0 if (self.a in S and self.b in S) else self.beta2))

    def rollouts(self, S, P, n, rng):
        """n paired rollout differences r(S) - r(P) of the Bayes decoder on common draws."""
        x = rng.choice([-1.0, 1.0], size=(n, self.m)); xi = rng.normal(size=n)
        pair = x[:, self.a] * x[:, self.b]
        def err(T):
            mask = np.zeros(self.m); mask[list(T)] = 1
            e = (x * self.g) @ (1 - mask) + self.sigma0 * xi
            if not (self.a in T and self.b in T):
                e = e + self.beta * pair
            return e
        return err(P) ** 2 - err(S) ** 2

    def reward_mc(self, S, n, rng):
        x = rng.choice([-1.0, 1.0], size=(n, self.m)); xi = rng.normal(size=n)
        Y = x @ self.g + self.beta * x[:, self.a] * x[:, self.b] + self.sigma0 * xi
        mask = np.zeros(self.m); mask[list(S)] = 1
        Yhat = (x * self.g) @ mask + (self.beta * x[:, self.a] * x[:, self.b] if (self.a in S and self.b in S) else 0.0)
        return float(np.mean(-(Y - Yhat) ** 2))


def reachable(P, m, k, R):
    P = tuple(sorted(P)); outside = [j for j in range(m) if j not in P]
    out = [frozenset(P)]
    for r in range(1, R + 1):
        for A in itertools.combinations(P, r):
            for B in itertools.combinations(outside, r):
                out.append(frozenset(set(P) - set(A) | set(B)))
    return out


def self_check(rng):
    t = Task(np.linspace(1.0, 0.1, 8), 1.2, 0.5, (2, 6))
    worst = 0.0
    for _ in range(6):
        S = rng.choice(8, size=4, replace=False)
        worst = max(worst, abs(t.reward_mc(S, 200000, rng) - t.f(S)))
    if worst > 0.05:
        raise AssertionError(f'closed-form value disagrees with Monte-Carlo Bayes-decoder rollouts: {worst}')
    return worst


def lcb_pick(pool, mean, se, P, alpha=0.05, dof=None):
    """Common conservative decision for every sampling method: edit to the candidate with the
    largest Bonferroni lower confidence bound, only if that bound is > 0; else keep the prefix.
    Student-t quantile with the per-candidate degrees of freedom (plug-in z was anti-conservative
    at 4 samples per candidate: the v1 run's N=400 spike)."""
    from scipy.stats import t as student_t
    if len(pool) == 0:
        return frozenset(P)
    dof = np.full(len(pool), 1e6) if dof is None else np.asarray(dof, float)
    z = student_t.ppf(1 - alpha / len(pool), np.maximum(dof, 1))
    lcb = np.asarray(mean) - z * np.asarray(se)
    j = int(np.argmax(lcb))
    return pool[j] if lcb[j] > 0 else frozenset(P)


def choose(method, t, P, cands, N, rng, beta2_max, eps):
    if method == 'oracle':
        return max(cands, key=t.f), 0
    if method == 'prefix' or N == 0:
        return frozenset(P), 0
    if method == 'proxy':
        # singleton importance g_j^2 from paired r({j}) - r({}); decide by first-order value only
        per = max(MIN_PER, N // t.m)
        smp = [t.rollouts({j}, set(), per, rng) for j in range(t.m)]
        est = np.array([x.mean() for x in smp]); var = np.array([x.var(ddof=1) / per for x in smp])
        pool = [S for S in cands if S != frozenset(P)]
        mean = [est[list(S - P)].sum() - est[list(P - S)].sum() for S in pool]
        se = [math.sqrt(var[list(S - P)].sum() + var[list(P - S)].sum()) for S in pool]
        return lcb_pick(pool, mean, se, P, dof=[per - 1] * len(pool)), per * t.m
    fo = lambda S: t.g2[list(S)].sum()
    base = fo(P)
    if method == 'uniform':
        pool = [S for S in cands if S != frozenset(P)]
    else:
        pool = [S for S in cands if S != frozenset(P) and base - fo(S) < beta2_max - eps]
    if not pool:
        return frozenset(P), 0
    if method in ('uniform', 'targeted'):
        per = N // len(pool)
        if per < MIN_PER:
            return frozenset(P), 0
        smp = [t.rollouts(S, P, per, rng) for S in pool]
        return lcb_pick(pool, [x.mean() for x in smp], [x.std(ddof=1) / math.sqrt(per) for x in smp], P,
                        dof=[per - 1] * len(pool)), per * len(pool)
    # adaptive successive elimination over the ambiguous pool, prefix known to have gain 0
    active = list(range(len(pool))); sums = np.zeros(len(pool)); sq = np.zeros(len(pool)); cnt = np.zeros(len(pool))
    used = 0
    batch = max(2, N // (len(pool) * 20))                  # about 20 elimination rounds at most
    while used + batch * len(active) <= N and len(active) > 0:
        for i in active:
            d = t.rollouts(pool[i], P, batch, rng); sums[i] += d.sum(); sq[i] += (d * d).sum(); cnt[i] += batch
        used += batch * len(active)
        mu = sums / np.maximum(cnt, 1)
        var = np.maximum(sq / np.maximum(cnt, 1) - mu ** 2, 1e-6)
        rad = np.sqrt(2 * var * np.log(4 * len(pool) * cnt ** 2 / 0.05) / np.maximum(cnt, 1))
        best_lcb = max(0.0, max(mu[i] - rad[i] for i in active))
        active = [i for i in active if mu[i] + rad[i] >= best_lcb]
        if len(active) == 1 and mu[active[0]] - rad[active[0]] > 0:
            break
    cand = [i for i in (active if active else range(len(pool))) if cnt[i] >= MIN_PER]
    if not cand:
        return frozenset(P), used
    mu = sums / np.maximum(cnt, 1); var = np.maximum(sq / np.maximum(cnt, 1) - mu ** 2, 1e-6)
    return lcb_pick([pool[i] for i in cand], [mu[i] for i in cand],
                    [math.sqrt(var[i] / cnt[i]) for i in cand], P, dof=[cnt[i] - 1 for i in cand]), used


def e1b(rng, instances, Ns):
    m, k, sigma0 = 10, 4, 0.5
    g2 = np.linspace(1.0, 0.1, m); beta2 = 1.6; eps = 0.05
    P = frozenset(range(k))
    pairs = list(itertools.combinations(range(m), 2))
    res = []
    inst_pairs = [pairs[i] for i in rng.integers(len(pairs), size=instances)]   # SAME instances for every method
    for R in (0, 1, 2):
        for method in ('oracle', 'prefix', 'proxy', 'uniform', 'targeted', 'adaptive'):
            for N in (Ns if method not in ('oracle', 'prefix') else [0]):
                glob, reach, acc, used = [], [], [], []
                for (a, b) in inst_pairs:
                    t = Task(g2, beta2, sigma0, (a, b))
                    cands = reachable(P, m, k, R)
                    best_all = max(t.f(S) for S in itertools.combinations(range(m), k))
                    best_R = max(t.f(S) for S in cands)
                    S, u = choose(method, t, P, cands, N, rng, beta2 * 1.25, eps)
                    glob.append(best_all - t.f(S)); reach.append(best_R - t.f(S))
                    acc.append(best_R - t.f(S) <= eps); used.append(u)
                res.append(dict(R=R, method=method, N=N, global_regret=float(np.mean(glob)),
                                reachable_regret=float(np.mean(reach)), p_acceptable=float(np.mean(acc)),
                                queries_used=float(np.mean(used)), n_candidates=len(reachable(P, m, k, R)),
                                se_global=float(np.std(glob) / math.sqrt(len(glob)))))
                print(f'  R={R} {method:9s} N={N:5d}: global regret {np.mean(glob):.3f}  reachable {np.mean(reach):.3f}  '
                      f'P(acc) {np.mean(acc):.2f}', flush=True)
    floor, floor_inst = {}, {}
    for R in (0, 1, 2):
        vals = []
        for (a, b) in inst_pairs:
            t = Task(g2, beta2, sigma0, (a, b))
            vals.append(max(t.f(S) for S in itertools.combinations(range(m), k)) - max(t.f(S) for S in reachable(P, m, k, R)))
        floor_inst[R] = float(np.mean(vals))
        vals = []
        for (a, b) in pairs:
            t = Task(g2, beta2, sigma0, (a, b))
            vals.append(max(t.f(S) for S in itertools.combinations(range(m), k)) - max(t.f(S) for S in reachable(P, m, k, R)))
        floor[R] = float(np.mean(vals))
    return dict(m=m, k=k, sigma0=sigma0, g2=g2.tolist(), beta2=beta2, eps=eps, pair_prior='uniform over all pairs',
                geometric_floor_exact=floor, geometric_floor_same_instances=floor_inst, curves=res)


def main(a):
    rng = np.random.default_rng(a.seed)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    t0 = time.perf_counter()
    chk = self_check(rng)
    print(f'self-check passed: max |MC - closed form| = {chk:.4f}', flush=True)
    A = e1a(rng, a.trials, a.alpha)
    for s in A:
        print(f'E1a m={s["m"]} k={s["k"]} R={s["R"]} |Amb|={s["n_amb"]}: lower {s["proved_lower"]:.0f}, '
              f'upper {s["proved_upper"]}, first N at alpha {s["first_N_at_alpha"]}', flush=True)
    B = e1b(rng, a.instances, a.N)
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (out / 'e1_results.json').write_text(json.dumps(dict(status='COMPLETE', self_check_max_abs=chk, seed=a.seed,
        source_sha256=src, E1a=A, E1b=B, seconds=time.perf_counter() - t0,
        evidence_class='CONTROLLED SIMULATION; E1a is the exact T2 model; E1b is an executable Bayes-decoder task'), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--trials', type=int, default=4000); p.add_argument('--alpha', type=float, default=0.05)
    p.add_argument('--instances', type=int, default=200)
    p.add_argument('--N', type=int, nargs='+', default=[100, 200, 400, 800, 1600, 3200, 6400, 12800, 25600, 51200])
    main(p.parse_args())
