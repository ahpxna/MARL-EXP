#!/usr/bin/env python3
"""W6-2 / W6-3 trainer (PROTOCOL_CITY_WAVE6_20261005): the F1-B trainer's loop (CITY_fleet_train_f1b.py, copied; provider c2 at q, RL-H:k
frozen, v11 PPO update unchanged) with the registered changes only.
  --mode h4 : --init <R10 v11 checkpoint>; before the first update log_std <- -1.0 and the value head <- V8.Net(seed).v (fresh init).
  --mode h5 : --init scratch (as F1-B); the dense cost's own time term max(0, 1 - v/v_lim) is weighted by (1 + lam); after every episode
              lam <- max(0, lam + ETA * (TL_agent(ep) - TL_agent_R(seed) + 0.25)), lam0 = 0, ETA = 0.5; TL_agent(ep) = mean tripinfo time
              loss of the fleet's members (as CITY_eval4); TL_agent_R(seed) from --rref (R rows of TRAIN seeds 0-7 under RL-H:k).
Run with PYTHONHASHSEED=0, OMP_NUM_THREADS=1."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, tempfile, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_fleet_v9 as V9  # noqa: E402
import scripts.CITY_fleet_v10 as V10  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
SRC = sha(__file__); ETA = 0.5; LAM = [0.0]; _dense = V10.dense_cost


def dense_cost_h5(ls, v):
    """CITY_fleet_v10.dense_cost with the own time term weighted by (1 + lam)."""
    sp = ls.vehicle.getSpeed(v); vl = ls.vehicle.getAllowedSpeed(v); fu = ls.vehicle.getFuelConsumption(v)
    if not (V8.ok(sp) and V8.ok(vl) and vl > 0 and V8.ok(fu, nonneg=False)):
        return None
    c = (1.0 + LAM[0]) * max(0.0, 1.0 - sp / vl) + V9.KAPPA * max(fu, 0.0) / 1000.0
    fol = ls.vehicle.getFollower(v, 100.0)
    if fol and fol[0] and fol[1] >= 0:
        fs = ls.vehicle.getSpeed(fol[0]); fvl = ls.vehicle.getAllowedSpeed(fol[0])
        if V8.ok(fs) and V8.ok(fvl) and fvl > 0:
            c += V10.LAMBDA_F * max(0.0, 1.0 - fs / fvl)
    return c


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fin = out / f'{a.name}_fleet.pt'
    if fin.exists():
        print('skip', a.name); return
    table = json.loads(Path(a.table).read_text()); spat_fn, _F = C2.make_spat_c2(table, a.q)
    for m in (V8, ES, GL, LD, V11):
        m.spat = spat_fn
    _n, lck, _m = X2.light_spec(f'RL-H:{a.light_k}'); lpol = Q7.load_policy(lck); info = Q7.NetInfo(Q7.NET_S)
    if a.mode == 'h4':
        net = torch.load(a.init, weights_only=False)['net']; init_sha = sha(a.init)
        with torch.no_grad():
            net.log_std.fill_(-1.0)
        net.v = V8.Net(a.seed).v; reset = 'log_std=-1.0; value head re-initialised V8.Net(seed).v'
    else:
        net = V9.NetR(a.seed); init_sha = 'scratch'; reset = None
        V10.dense_cost = dense_cost_h5; reference = json.loads(Path(a.rref).read_text())
        assert reference['horizon'] == (300 if a.smoke else 3600), reference
        assert reference['light_k'] == a.light_k, reference
        rref = reference['timeloss_agent']
        assert sorted(int(s) for s in rref) == sorted(Q7.TRAIN_SEEDS), rref.keys()
    net.train(); opt = torch.optim.Adam(net.parameters(), lr=3e-4); rng = np.random.default_rng(a.seed); torch.manual_seed(a.seed); log = []
    end = 300 if a.smoke else 3600; t0 = time.perf_counter(); tmpd = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    for ep in range(a.episodes):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; te = time.perf_counter()
        cars = V11.CarPPOL(net, Q7.RHO, seed, deterministic=False, record=True); light = CE.LightRL(info, lpol)
        ti = str(Path(tmpd) / f'ti_{a.name}.xml') if a.mode == 'h5' else None
        m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, light, cars, end=end, tripinfo=ti); cars.finish(); tsim = time.perf_counter() - te
        batch = V8.gae(cars.segments, net)
        pl, vl, rdev = V8.ppo_update(net, opt, batch, rng=rng) if batch is not None else (float('nan'),) * 3
        segs = [s for s in cars.segments if s['dec']]; trip_ret = [sum(d['rew'] for d in s['dec']) for s in segs]; st = cars.stats
        row = dict(ep=ep, seed=seed, decisions=st['decisions'], segments=len(segs), teleports=m['teleports'], popped=st['popped'],
                   seg_return_mean=float(np.mean(trip_ret)) if trip_ret else float('nan'),
                   mean_r=float(np.mean([d['rew'] for s in segs for d in s['dec']])) if segs else float('nan'),
                   pi_loss=float(pl), v_loss=float(vl), ratio_dev=float(rdev), log_std=float(net.log_std.item()), t_sim=tsim, wall=time.perf_counter() - t0)
        if a.mode == 'h5':
            rows = CE.read_tripinfo(ti); os.remove(ti); tla = float(np.nanmean([r['timeloss'] for r in rows if cars.is_agent(r['id'])]))
            assert np.isfinite(tla) and np.isfinite(float(rref[str(seed)])), 'nonfinite dual update'
            row['unfinished_agent'] = sum(not r['finished'] for r in rows if cars.is_agent(r['id']))
            row['reference_horizon'] = end
            gap = tla - float(rref[str(seed)]) + 0.25; row.update(tl_agent=tla, tl_agent_R=float(rref[str(seed)]), lam=LAM[0]); LAM[0] = max(0.0, LAM[0] + ETA * gap)
        log.append(row)
        print(f"[{row['wall']:.0f}s] {a.name} ep {ep} seed {seed} dec {row['decisions']} segRet {row['seg_return_mean']:.2f} vloss {row['v_loss']:.3f} "
              f"std {np.exp(row['log_std']):.3f} tele {row['teleports']} sim {tsim:.1f}s" + (f" TLa {row['tl_agent']:.2f} (R {row['tl_agent_R']:.2f}) lam {LAM[0]:.3f}" if a.mode == 'h5' else ''), flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=net, kind='ppo_residual_glosaL', spat='on', reward='AD_tail' + ('+lagrangian_agentTL' if a.mode == 'h5' else ''), name=a.name, seed=a.seed,
                    episodes=a.episodes, light=f'RL-H:{a.light_k}', light_sha256=sha(lck), init=a.init, init_sha256=init_sha, reset=reset, mode=a.mode,
                    lam_final=LAM[0] if a.mode == 'h5' else None, provider=a.table, provider_sha256=sha(a.table), q=a.q, corrected=True, provider_version='c2',
                    source_sha256=SRC, v11_sha256=sha(V11.__file__), pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fin)
    print('saved', fin, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--mode', choices=('h4', 'h5'), required=True); p.add_argument('--seed', type=int, required=True); p.add_argument('--light-k', type=int, required=True)
    p.add_argument('--init', required=True); p.add_argument('--rref'); p.add_argument('--table', required=True); p.add_argument('--q', type=float, required=True)
    p.add_argument('--episodes', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
