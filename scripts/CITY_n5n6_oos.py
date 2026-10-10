#!/usr/bin/env python3
"""N5 / N6 out-of-sample commitment selection on the H3 branches (PROTOCOL_CITY_N5N6_OOS_20261005).  Offline; reads
m3h3_20261004/h3_results.json + br/*_I0_veh_s*.npz (agent / human denominators).  Two-fold cross-fitting by seed ({0,1} <-> {2,3}),
cluster bootstrap over the 8 (k, seed) episodes, within-situation permutation noise floor.  Writes m3h3_20261004/report_n5n6.txt + json."""
import json
from pathlib import Path
import numpy as np

D = Path(__file__).resolve().parents[1] / 'research/city_sim/m3h3_20261004'; OPTS = ('Z', 'H5', 'H10', 'H15', 'P'); ALL = ('I0',) + OPTS
FEAT = ('near', 'qgap', 'aqgap', 'rl_action', 'eligible', 'hD', 'th', 'k')


def load():
    R = json.loads((D / 'h3_results.json').read_text()); S = []; bad = []
    for r in R:
        z = np.load(D / 'br' / f"{r['sid']}_I0_veh_s{r['seed']}.npz", allow_pickle=True); na = int(z['agent'].sum()); nh = int(len(z['agent']) - na)
        g = {'I0': 0.0}; feas = {'I0': True}; tl = {'I0': (0.0, 0.0, 0.0)}
        for o in OPTS:
            x = r['opt'][o]; g[o] = -float(x['full']['fuel_agent']); a, h, c = x['dtl_ag_sum'] / na, x['dtl_hu_sum'] / nh, float(x['full']['tl'])
            tl[o] = (a, h, c); feas[o] = a <= 0.5 and h <= 0.5 and c <= 0.5
        if r['rl_action'] == 1 and abs(g['Z'] - g['P']) > 1e-9:
            bad.append(r['sid'])
        f = dict(near=r['near'], qgap=r['qgap'], aqgap=abs(r['qgap']), rl_action=r['rl_action'], eligible=float(r['eligible']), hD=r['hD'], th=r['t'] / 3600, k=r['k'])
        S.append(dict(sid=r['sid'], k=r['k'], seed=r['seed'], cl=(r['k'], r['seed']), group=r['group'], g=g, feas=feas, tl=tl, f=f))
    return S, bad


def best_opt(T, allow_i0=True):
    m = {o: np.mean([s['g'][o] for s in T]) for o in OPTS}; o = max(m, key=m.get)
    return o if (m[o] > 0 or not allow_i0) else 'I0'


def fit(rule, T):
    """Returns a function f(s) -> option, using only the training situations T."""
    if rule == 'I0':
        return lambda s: 'I0'
    if rule == 'FIXED':
        o = best_opt(T, allow_i0=False); return lambda s: o
    if rule in ('SENS', 'COST'):
        key, ge = ('near', True) if rule == 'SENS' else ('aqgap', False); best = (-1e9, None, None)
        for q in (0, .25, .5, .75):
            tau = float(np.quantile([s['f'][key] for s in T], q if ge else 1 - q))
            sub = [s for s in T if (s['f'][key] >= tau if ge else s['f'][key] <= tau)]
            if not sub:
                continue
            o = best_opt(sub, allow_i0=False); val = sum(s['g'][o] for s in sub) / len(T)
            if val > best[0]:
                best = (val, tau, o)
        _, tau, o = best
        return (lambda s: o if s['f'][key] >= tau else 'I0') if ge else (lambda s: o if s['f'][key] <= tau else 'I0')
    if rule == 'RC':
        mn, mq = np.median([s['f']['near'] for s in T]), np.median([s['f']['aqgap'] for s in T]); cell = {}
        for a in (0, 1):
            for b in (0, 1):
                sub = [s for s in T if (s['f']['near'] >= mn) == a and (s['f']['aqgap'] <= mq) == b]; cell[(a, b)] = best_opt(sub) if sub else 'I0'
        return lambda s: cell[(int(s['f']['near'] >= mn), int(s['f']['aqgap'] <= mq))]
    if rule == 'STRAT':
        cell = {a: (best_opt([s for s in T if s['f']['rl_action'] == a]) if any(s['f']['rl_action'] == a for s in T) else 'I0') for a in (0, 1)}
        return lambda s: cell[s['f']['rl_action']]
    if rule == 'LEARN':
        X = np.array([[s['f'][c] for c in FEAT] for s in T], float); mu, sd = X.mean(0), X.std(0) + 1e-9; Z = np.c_[np.ones(len(T)), (X - mu) / sd]; W = {}
        for o in OPTS:
            y = np.array([s['g'][o] for s in T]); A = Z.T @ Z + np.diag([0.0] + [1.0] * len(FEAT)); W[o] = np.linalg.solve(A, Z.T @ y)

        def f(s):
            z = np.r_[1.0, (np.array([s['f'][c] for c in FEAT], float) - mu) / sd]; p = {o: float(z @ W[o]) for o in OPTS}; o = max(p, key=p.get)
            return o if p[o] > 0 else 'I0'
        return f
    raise ValueError(rule)


RULES = ('I0', 'FIXED', 'SENS', 'COST', 'RC', 'LEARN', 'STRAT')


def crossfit(S):
    out = {r: {} for r in RULES}; picks = {r: {} for r in RULES}
    for tr, te in (({0, 1}, {2, 3}), ({2, 3}, {0, 1})):
        T = [s for s in S if s['seed'] in tr]; E = [s for s in S if s['seed'] in te]; assert not ({s['seed'] for s in T} & {s['seed'] for s in E})   # KN5-2
        for r in RULES:
            f = fit(r, T)
            for s in E:
                o = f(s); out[r][s['sid']] = s['g'][o]; picks[r][s['sid']] = o
    rnd = {s['sid']: float(np.mean([s['g'][o] for o in OPTS])) for s in S}
    return out, picks, rnd


def cboot(S, vals, B=4000, seed=0):
    cl = sorted({s['cl'] for s in S}); by = {c: [vals[s['sid']] for s in S if s['cl'] == c] for c in cl}; rng = np.random.default_rng(seed); m = []
    for _ in range(B):
        pick = rng.choice(len(cl), len(cl)); m.append(np.mean(np.concatenate([by[cl[i]] for i in pick])))
    sign = sum(np.mean(by[c]) > 0 for c in cl)
    return float(np.mean([vals[s['sid']] for s in S])), float(np.percentile(m, 2.5)), float(np.percentile(m, 97.5)), f'{sign}/{len(cl)}'


def fmt(t):
    return f'{t[0]:+.4f} [{t[1]:+.4f}, {t[2]:+.4f}] clusters>0 {t[3]}'


if __name__ == '__main__':
    S, bad = load(); out, picks, rnd = crossfit(S); L = ['== N5 / N6 out-of-sample commitment selection (H3 branches; 2-fold by seed; cluster bootstrap over 8 episodes). Gain = -(full-episode agent fuel % vs I0); + = saving']
    L.append(f'  KN5-1 situations {len(S)} with all branches + denominators: PASS'); L.append(f'  KN6-0 rl_action=1: P == Z outcomes: {"PASS" if not bad else "FAIL " + str(bad)}')
    L.append(f'  KN5-2 fold separation asserted: PASS')
    res = {}
    for grp in ('all', 'eligible', 'random'):
        G = [s for s in S if grp == 'all' or s['group'] == grp]; L.append(f'  -- {grp} (n {len(G)})')
        L.append(f'     RANDOM (mean over options) vs I0: {fmt(cboot(G, rnd))}')
        for r in RULES:
            v = out[r]; d = {k: v[k] - rnd[k] for k in v}; a, b = cboot(G, v), cboot(G, d); fe = np.mean([S_['feas'][picks[r][S_['sid']]] for S_ in G])
            from collections import Counter
            pc = Counter(picks[r][s['sid']] for s in G)
            L.append(f'     {r:6s} vs I0 {fmt(a)} | vs RANDOM {fmt(b)} | feasible {fe:.2f} | picks {dict(pc)}'); res[f'{grp}/{r}'] = dict(vs_i0=a, vs_random=b, picks=dict(pc))
    con = {}
    for x, y in (('LEARN', 'SENS'), ('RC', 'SENS'), ('COST', 'SENS'), ('RC', 'COST'), ('STRAT', 'FIXED'), ('LEARN', 'FIXED')):
        d = {k: out[x][k] - out[y][k] for k in out[x]}; con[f'{x}-{y}'] = cboot(S, d); L.append(f'  contrast {x} - {y} (all, OOS): {fmt(con[f"{x}-{y}"])}')
    # N6 descriptive: per rl_action stratum, option means (pooled, in-sample description)
    for a in (0, 1):
        G = [s for s in S if s['f']['rl_action'] == a]
        L.append(f'  N6 stratum rl_action={a} ({"would switch" if a else "would keep"}; n {len(G)}): ' + ' | '.join(f'{o} {cboot(G, {s["sid"]: s["g"][o] for s in G})[0]:+.4f}' for o in OPTS))
    # noise floor: within-situation permutation of option labels
    rng = np.random.default_rng(1); M = np.array([[s['g'][o] for o in OPTS] for s in S]); obs = M.mean(0).max(); null = []
    for _ in range(2000):
        P = np.array([rng.permutation(row) for row in M]); null.append(P.mean(0).max())
    L.append(f'  noise floor: observed best fixed-option mean {obs:+.4f} (option {OPTS[int(M.mean(0).argmax())]}); permutation null 95th pct {np.percentile(null, 95):+.4f}; p = {np.mean(np.array(null) >= obs):.3f}')
    L.append(f'  within-situation SD of option gains (mean) {np.mean(M.std(1)):.4f} vs SD of option means {M.mean(0).std():.4f}')
    best = max(('LEARN', 'RC'), key=lambda r: res[f'all/{r}']['vs_random'][1]); opp = res[f'all/{best}']['vs_random'][1] > 0
    n5 = con['LEARN-SENS'][1] > 0 or con['RC-SENS'][1] > 0; cost_only = con['COST-SENS'][1] > 0 and con['RC-COST'][1] <= 0 <= con['RC-COST'][2]
    st1 = {picks['STRAT'][s['sid']] for s in S if s['f']['rl_action'] == 1}; n6 = con['STRAT-FIXED'][1] > 0 and st1 <= {'Z', 'P'}
    L.append(f'  OOS OPPORTUNITY: {"YES" if opp else "NO"} (best of LEARN / RC = {best}, lower bound vs RANDOM {res[f"all/{best}"]["vs_random"][1]:+.4f})')
    L.append(f'  N5 VERDICT: {"SUPPORTED" if n5 else ("COST-ONLY SUFFICES" if cost_only else "REJECTED (no rule beats sensitivity-only out of sample)")}')
    L.append(f'  N6 VERDICT: {"SUPPORTED" if n6 else "REJECTED"} (STRAT - FIXED lower {con["STRAT-FIXED"][1]:+.4f}; STRAT picks in the would-switch stratum {sorted(st1)})')
    txt = '\n'.join(L); print(txt); (D / 'report_n5n6.txt').write_text(txt + '\n')
    (D / 'n5n6.json').write_text(json.dumps(dict(res=res, contrasts=con, picks=picks), indent=1, default=str))
