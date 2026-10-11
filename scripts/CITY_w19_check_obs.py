#!/usr/bin/env python3
"""KW19-4 (PROTOCOL_CITY_WAVE19_20261008): the deployed W19 light's observation, recomputed independently.  Run through CITY_w19_run.py.
For light k (its family set by light_spec), builds the evaluator's light (CITY_eval4.build_light; adapter raw, and q:1:0.25 where defined)
and runs one 600-s episode (traffic seed 0, all SUMO drivers).  Every 5 s, for every signal, the observation the light computes is compared
with a direct recomputation from lane / vehicle queries written here (not calling CITY_w19_obs); also the action the light takes equals the
policy's argmax on the recomputed observation.  Prints mismatches (must be 0), the share of switch actions and a sample observation.
Usage: CITY_w19_run.py scripts/CITY_w19_check_obs.py <k> [<k> ...]   (one family per process: pass lights of one family)"""
import sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_w19_obs as W  # noqa: E402


def expected(info, tid, kind, qa, qb):
    ls = CE.ls; d = info.tls[tid]; ph = ls.trafficlight.getPhase(tid); cur = d['greens'].index(ph) if ph in d['greens'] else -1
    sp = ls.trafficlight.getSpentDuration(tid); H, N, M1, M2, C = [], [], [], [], []
    for s in d['serve']:
        h = n = m1 = m2 = 0; c = [0, 0, 0, 0]
        for l in s:
            L = ls.lane.getLength(l)
            for v in ls.lane.getLastStepVehicleIDs(l):
                u = ls.vehicle.getSpeed(v); n += 1; h += u < 0.1; m1 += 0.1 <= u < 2.0; m2 += 2.0 <= u < 5.0
                x = L - ls.vehicle.getLanePosition(v); c[0 if x < 25 else 1 if x < 50 else 2 if x < 100 else 3] += 1
        H.append(h); N.append(n); M1.append(m1); M2.append(m2); C.append(c)
    q = [H[g] + qa * M1[g] + qb * M2[g] for g in range(2)]
    dh, dn, dt = {'A': (10, 20, 60), 'B1': (10, 20, 60), 'S05': (5, 10, 30), 'S2': (20, 40, 120)}.get(kind, (10, 20, 60))
    if kind == 'B2':
        return np.array([x / 10 for x in C[0]] + [x / 10 for x in C[1]] + [cur == 0, cur == 1, sp / 60], np.float32)
    o = [q[0] / dh, q[1] / dh, N[0] / dn, N[1] / dn, cur == 0, cur == 1, sp / dt]
    if kind == 'B1':
        o += [M1[0] / 10, M1[1] / 10, M2[0] / 10, M2[1] / 10]
    return np.array(o, np.float32)


def check(k, adapter):
    net, lck, _ = X2.light_spec(f'RL-H:{k}'); kind = W.obs_kind(); info = CE.NetInfo(Q7.NET_S)
    _n, light, _x, _i = E4.build_light(f'RL-H:{k}', info, adapter, None); pol = Q7.load_policy(lck)
    qa, qb = (float(adapter.split(':')[1]), float(adapter.split(':')[2])) if adapter.startswith('q:') else (0.0, 0.0)
    st = dict(n=0, bad=0, act_bad=0, sw=0, dec=0, sample=None); inner = light.policy

    def probe(O):
        a = np.asarray(inner(O)); b = pol(O); st['act_bad'] += int((a != b).sum()); st['dec'] += len(a); st['sw'] += int((a == 1).sum()); return a
    light.policy = probe

    class P:
        def step(self, t):
            if int(t) % CE.DT_L == 0:
                for tid in light.ids:
                    o, _h, _c = light.obs(tid); e = expected(info, tid, kind, qa, qb); st['n'] += 1
                    if o.shape != e.shape or not np.allclose(o, e, atol=1e-6):
                        st['bad'] += 1
                    if st['sample'] is None and o.sum() > 0:
                        st['sample'] = np.round(o, 3).tolist()
            light.step(t)
    CE.run_episode(Q7.NET_S, Q7.ROU.format(0), 0, P(), None, end=600)
    print(f'KW19-4 k{k} family {W.CUR["fam"]} obs {kind} adapter {adapter}: compared {st["n"]}, obs mismatches {st["bad"]}, action mismatches '
          f'{st["act_bad"]} of {st["dec"]} decisions, switch share {st["sw"] / max(1, st["dec"]):.3f}; sample obs {st["sample"]}', flush=True)
    return st['bad'] == 0 and st['act_bad'] == 0


if __name__ == '__main__':
    ok = True
    for k in [int(x) for x in sys.argv[1:]]:
        ad = ['raw'] + ([] if W.FAMS[W.fam_of(k)][1] == 'B2' else ['q:1:0.25'])
        for a in ad:
            ok &= check(k, a)
    print('KW19-4', 'PASS' if ok else 'FAIL'); sys.exit(0 if ok else 1)
