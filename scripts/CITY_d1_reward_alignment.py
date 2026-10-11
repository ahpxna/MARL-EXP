#!/usr/bin/env python3
"""D1 reward alignment (user guidance TWO_POPULATION_CAUSAL_DIAGNOSIS_20261004 §3; 04/10/2026).  Question: does the v8 reward B RANK known
behaviours like their physical outcomes?  For each policy, on its OWN trace (no counterfactual relabelling), FT light, TRAIN traffic 0-7:
  physical  agent fuel (mean per agent trip), agent / human / city time loss, teleports, unfinished (eval4 row)
  objective the SAME v8 PhaseRewardB on the same trace: per-episode sum of phase rewards, mean phase reward, R1-R4 shares, and the
            per-agent discounted return that GAE uses (gamma 0.99, credited to each agent's last zone-second per light interval;
            every agent zone-second counts as a 'decision', including SUMO-driven / released seconds), mean over agents
Policies (CLI): always | sigma0.3 | U:<v4-v7 fleet name> | P:<v8 fleet file>[:sto] | GLOSA.  Usage: CITY_d1_reward_alignment.py POLICY TAG OUT_DIR SEEDS...
The v8 trainer module is imported read-only; nothing that a running job imports is modified."""
import argparse, hashlib, json, os, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6 as E6  # noqa: E402,F401  (patches E4.load_fleet for P: and GLOSA)
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402

G = {}
_orig_step = E4.Logger.step


def step(self, t):
    _orig_step(self, t)
    ls = CE.ls
    if G.get('tr') is None:
        G['tr'] = V8.PhaseRewardB(G['stats'])
    G['tr'].step(t)
    for v in ls.simulation.getDepartedIDList():
        if G['sigma'] is not None and G['is_agent'](v):
            ls.vehicle.setImperfection(v, G['sigma'])
    for v in ls.vehicle.getIDList():
        if not G['is_agent'](v):
            continue
        try:
            nt = ls.vehicle.getNextTLS(v)
        except Exception:
            continue
        if not nt or nt[0][2] > V8.ZONE:
            continue
        rec = dict(vid=v, t=t, tid=nt[0][0], rew=0.0); G['dec'][v].append(rec); G['tr'].credit(nt[0][0], rec)


E4.Logger.step = step


def main():
    pol, tag, out, seeds = sys.argv[1], sys.argv[2], Path(sys.argv[3]), [int(x) for x in sys.argv[4:]]
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1); out.mkdir(parents=True, exist_ok=True)
    sto = pol.endswith(':sto'); spec = pol[:-4] if sto else pol
    fleet = {'always': 'L-ACT:0', 'sigma0.3': 'L-ACT:0'}.get(spec, spec); guard = 'always' if spec in ('always', 'sigma0.3') else 'none'
    if sto:                                                     # stochastic PPO evaluation (D2 item 4): same checkpoint, sampled actions
        _lf = E4.load_fleet
        def lf(s, seed, g):
            c, p = _lf(s, seed, g); c.det = False; return c, p
        E4.load_fleet = lf
    rows = []
    for s in seeds:
        G.clear(); G.update(stats={k: 0 for k in ('capped', 'b_invalid', 'b_empty', 'b_R1', 'b_R2', 'b_R3', 'b_R4')}, tr=None, dec=defaultdict(list),
                            sigma=0.3 if spec == 'sigma0.3' else None, is_agent=lambda v, s=s: V8._stable_u(s, v) < 0.5)
        a = argparse.Namespace(light='FT', light_obs='raw', light_fallback='none', fleet=fleet, guard=guard, record=None, replay=None, replay_dir=None,
                               discharge=False, delay_trace=False, swap_at=None, swap_light=None, swap_fleet=None, seeds=[s], smoke=False, tag=tag, out=str(out))
        r = E4.run(a, s, 5400); L = G['tr'].log
        rets = []
        for v, ds in G['dec'].items():
            ret = sum((V8.GAMMA ** k) * d['rew'] for k, d in enumerate(ds)); rets.append(ret)
        br = {b: G['stats']['b_' + b] for b in ('R1', 'R2', 'R3', 'R4')}; n = sum(br.values()) or 1
        row = dict(seed=s, fuel_agent=r['fuel_agent'], timeloss_agent=r['timeloss_agent'], timeloss_human=r['timeloss_human'], timeloss=r['timeloss'],
                   teleports=r['teleports'], unfinished=r['unfinished'], B_sum=float(sum(x[7] for x in L)), B_mean_phase=float(np.mean([x[7] for x in L])) if L else float('nan'),
                   B_agent_return=float(np.mean(rets)) if rets else float('nan'), n_intervals=len(L), branch_share={b: br[b] / n for b in br},
                   credited=int(sum(x[9] for x in L)), agents=len(G['dec']))
        rows.append(row)
        print(f"{tag} s{s}: fuel {row['fuel_agent']:.0f} TLa {row['timeloss_agent']:.2f} TLh {row['timeloss_human']:.2f} tele {row['teleports']} unf {row['unfinished']} | "
              f"B_sum {row['B_sum']:.0f} B_phase {row['B_mean_phase']:.2f} B_ret {row['B_agent_return']:.2f} R1 {row['branch_share']['R1']:.3f}", flush=True)
    (out / f'{tag}.json').write_text(json.dumps(dict(policy=pol, rows=rows, source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                                     v8_sha256=hashlib.sha256(Path(V8.__file__).read_bytes()).hexdigest()), indent=1))


if __name__ == '__main__':
    main()
