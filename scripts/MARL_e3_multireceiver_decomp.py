#!/usr/bin/env python3
"""F5b: MULTI-RECEIVER loss decomposition of the deployed E3 selectors (28/09, independent recheck §1 scope caveat).

F5 (MARL_e3_bridge_panel_v2.py) enumerated ONE receiver's subsets with every other receiver at its prefix.  That cannot
show that the loss of a selector that edits SEVERAL receivers at once is estimation.  This script works on the actual
multi-receiver development states and candidate families of the continuation labels (the B1 family edits any number of
receivers), with the deployed selectors' actual choices, and adds rollouts only where the labels are silent.

Per development state (value = declared continuation cont_3, gains y = cont(S) - cont(P); oracle diagnostics only):
  V_fam      max gain over the whole scored candidate family;
  V_famB     the same within the +84 B cap (no bid charged: the reference budget);
  V_famBb    within +84 B minus the 10 B bid (the bid arms' own feasible set);
  V_famR1    within +84 B and radius <= 1 at every receiver (the R1 restriction, geometry inside the family);
  realised   each arm's y[chosen] (the trainer's saved dev_chosen, mean over init seeds);
  V_LS       COVERAGE lower bound: best-improvement multi-receiver local search in the byte-feasible profile space
             (moves: one sender swap at ANY receiver, |S_i| = k_i kept, cap +84), from the family's best feasible profile;
  V_LSP      the same search started from the prefix P (how far rollout search from the committed order gets);
  additivity for the family's best profile when it edits >= 2 receivers: its gain against the sum of the gains of its
             single-receiver components (each receiver's edit alone, the others at the prefix).
Decomposition (per arm, all >= 0 except where noted):
  V_LS - realised = (V_LS - V_famB) coverage lower bound  +  (V_famB - V_famBb) bid bytes (bid arms)
                  + (V_famBb - realised) estimation/search loss of the arm's choice within its own feasible family.
Rollouts use MARL_e3_continuation_labels.replay (the label producer's function).  Self-checks (abort): the replayed
value of the prefix and of the family's best profile equal the stored labels; every searched profile is legal
(|S_i| = k_i, i not in S_i) and within the cap.  Development states only; never test seeds.
"""
from __future__ import annotations
import argparse, glob, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import profile_cost, prefix_sets
from scripts.MARL_e3_selector_train import load
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy, replay

SOURCES = ['scripts/MARL_e3_multireceiver_decomp.py', 'scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_e3_actor_train.py',
           'models/marl_comm_actor.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']
TEST_SEEDS = set(range(1301, 1317))
CAP, BID = 84, 10


def radius(S, P):
    return max(len(set(s) - set(p)) for s, p in zip(S, P))


class Evaluator:
    def __init__(self, sc, ck, st):
        self.sc, self.st = sc, st; self.seed, self.load = st['traffic_seed'], st['headway']
        env, topo, _, _ = sc.env(self.seed, self.load); self.pol = Policy(ck, topo, env.action_interval); self.cache = {}; self.n = 0

    def value(self, S):
        key = tuple(tuple(sorted(s)) for s in S)
        if key not in self.cache:
            order, K, q, _ = replay(self.sc, self.seed, self.load, self.pol, self.st['t'], [set(s) for s in S]); self.n += 1
            if list(order) != self.st['order'] or K != self.st['K']:
                raise AssertionError('SELF-CHECK FAIL: replay order or K differs from the label state')
            self.cache[key] = -float(sum(q))
        return self.cache[key]


def legal(S, st):
    return all(len(S[i]) == st['K'][i] and i not in S[i] for i in range(st['m']))


def search(ev, st, start, b0, max_iters):
    """Best-improvement local search over single sender swaps at any receiver, within the cap."""
    m = st['m']; order = st['order']; K = st['K']; cur = [frozenset(s) for s in start]; v = ev.value(cur); path = []
    for _ in range(max_iters):
        best = (v, None)
        for i in range(m):
            outside = [b for b in range(m) if b != i and b not in cur[i]]
            for a in sorted(cur[i]):
                for b in outside:
                    S = list(cur); S[i] = (cur[i] - {a}) | {b}
                    if profile_cost(order, K, [set(s) for s in S])[0] > b0 + CAP:
                        continue
                    if not legal(S, st):
                        raise AssertionError('SELF-CHECK FAIL: illegal searched profile')
                    val = ev.value(S)
                    if val > best[0] + 1e-9:
                        best = (val, (i, a, b, S))
        if best[1] is None:
            break
        v = best[0]; i, a, b, S = best[1]; cur = S; path.append((i, a, b))
    return v, cur, path


def main(a):
    D = Path(a.actor_dir); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    S_all, ck_set = load([D / 'labels_dev']); ckp = ck_set.pop()
    if any(st['traffic_seed'] in TEST_SEEDS for st in S_all):
        raise SystemExit('refusing: test seeds')
    arms = {}
    for spec in a.arm:
        name, pat = spec.split('=', 1); ch = []
        for mf in sorted(glob.glob(str(D / pat))):
            job = json.loads(Path(mf.replace('model_', 'job_').replace('.pt', '.json')).read_text())
            if job['actor_ckpt'] != ckp or job['results']['direct'].get('dev_chosen') is None or job['results']['direct']['eps'] != [st['episode_id'] for st in S_all]:
                raise SystemExit(f'SELF-CHECK FAIL: {mf}: wrong actor, no dev_chosen, or a different dev state order')
            ch.append(job['results']['direct']['dev_chosen'])
        arms[name] = dict(chosen=ch, bid=bool(json.loads(Path(mf.replace('model_', 'job_').replace('.pt', '.json')).read_text()).get('bid') or
                                              json.loads(Path(mf.replace('model_', 'job_').replace('.pt', '.json')).read_text()).get('qbid')))
    idx = list(range(len(S_all)))[a.shard::a.nshards]
    ck = torch.load(ckp, weights_only=False); sc = Scenarios(out); rows = []; t0 = time.perf_counter()
    for k in idx:
        st = S_all[k]; C = st['cands']; P = [frozenset(s) for s in C[0]['sets']]; b0 = st['b0']
        y = np.array([c['cont'] for c in C]) - C[0]['cont']; by = np.array([c['bytes'] for c in C])
        rad = np.array([radius(c['sets'], C[0]['sets']) for c in C])
        fB, fBb, fR1 = by <= b0 + CAP, by <= b0 + CAP - BID, (by <= b0 + CAP) & (rad <= 1)
        jB = int(np.argmax(np.where(fB, y, -np.inf)))
        ev = Evaluator(sc, ck, st)
        if abs(ev.value(P) - C[0]['cont']) > 1e-9 or abs(ev.value([frozenset(s) for s in C[jB]['sets']]) - C[jB]['cont']) > 1e-9:
            raise AssertionError('SELF-CHECK FAIL: replay differs from the stored label value')
        best = [frozenset(s) for s in C[jB]['sets']]
        vLS, sLS, pLS = search(ev, st, best, b0, a.max_iters)
        vLSP, sLSP, pLSP = search(ev, st, P, b0, a.max_iters)
        edited = [i for i in range(st['m']) if best[i] != P[i]]; add = None
        if len(edited) >= 2:
            comp = []
            for i in edited:
                S = list(P); S[i] = best[i]; comp.append(ev.value(S) - C[0]['cont'])
            add = dict(joint_gain=float(y[jB]), sum_single=float(sum(comp)), singles=[float(x) for x in comp])
        r = dict(episode=st['episode_id'], t=st['t'], V_fam=float(y.max()), V_famB=float(y[fB].max()), V_famBb=float(y[fBb].max()), V_famR1=float(y[fR1].max()),
                 V_LS=vLS - C[0]['cont'], V_LSP=vLSP - C[0]['cont'], LS_swaps=len(pLS), LSP_swaps=len(pLSP),
                 LSP_receivers=len({i for i, _, _ in pLSP}), best_family_receivers=len(edited), best_family_radius=int(rad[jB]), additivity=add,
                 rollouts=ev.n, arms={n: dict(realised=float(np.mean([y[c[k]] for c in v['chosen']])), bid=v['bid']) for n, v in arms.items()})
        rows.append(r)
        print(f'[{time.perf_counter() - t0:.0f}s] {st["episode_id"]} t{st["t"]}: famB {r["V_famB"]:+.0f} LS {r["V_LS"]:+.0f} ({r["LS_swaps"]} swaps) '
              f'LS-from-P {r["V_LSP"]:+.0f} ({r["LSP_swaps"]} swaps, {r["LSP_receivers"]} rx) | best family edits {len(edited)} rx | '
              + ' '.join(f'{n} {v["realised"]:+.1f}' for n, v in r['arms'].items()) + f' | rollouts {ev.n}', flush=True)
        (out / 'rows.json').write_text(json.dumps(rows, indent=1))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), actor_ckpt=ckp, source_hashes=h0,
                                                       states=len(rows), seconds=time.perf_counter() - t0), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--out', required=True)
    p.add_argument('--arm', action='append', required=True, help='name=<glob of v3+ model files relative to the actor dir>')
    p.add_argument('--max-iters', type=int, default=3); p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    main(p.parse_args())
