#!/usr/bin/env python3
"""M3 prep and E trainer (PROTOCOL_CITY_M3_COMPAT_UPDATE_20261004 + A1 + A1b; 04/10/2026).
  prep  K OUT_DIR [--episodes 8]: RL-H:k (widened, greedy == RL-H:k) with the frozen DEV fleet L11_s13, fleet SPaT = the M2b table of
        RL-H:k (σ*-fitted), TRAIN 0-7 once.  Writes (i) prov_rlh<k>_cl.json = the CLOSED-LOOP provider refitted from these traces with
        CITY_spat_forecast.fit (unchanged) and (ii) scale_rlh<k>.json = per-type mean raw ticket weight on this common trace (+ zero share,
        p95, max, and the penalty / base-reward ratio per type at lam 1).
  train K ARM LAM OUT_DIR: fine-tune the widened RL-H:k (12 inputs, new columns zero) with the frozen DEV fleet, DQN recipe of Q7
        (gamma 0.9, 200 updates / episode, soft target 0.01, Adam 1e-3) with eps 0.05, buffer empty, DQN seed 11 + 100 k + 7 (all arms).
        ARM in E0q (queue reward, lam 0), E0p (physical, lam 0), uniform, eta, active, receiver (physical + lam * penalty).
        3 blocks x 20 episodes; provider frozen in a block; after blocks 1 and 2 the provider is refitted from 8 greedy TRAIN episodes of
        the current checkpoint with the fleet in the loop; block 3 trains with the deployed provider.  LAST checkpoint saved with the table."""
import argparse, hashlib, json, os, sys, time, tempfile
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_m3_core as M  # noqa: E402

P = ROOT / 'research/city_sim/spat_pilot_20261004'; DEV_FLEET = P / 'fleets_v11/L11_s13_fleet.pt'
WKEY = dict(E0q='uniform', E0p='uniform', uniform='uniform', eta='eta', active='active', receiver='receiver')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def rlh_net(k):
    _n, ck, _m = X2.light_spec(f'RL-H:{k}'); return torch.load(ck, weights_only=False)['net'], ck


def set_provider(table):
    spat_fc, F = FC.make_spat(table, 0.5)
    for m in (V8, ES, GL, LD, V11):
        m.spat = spat_fc
    return spat_fc, F


def fleet(seed):
    d = torch.load(DEV_FLEET, weights_only=False); n = d['net']; n.eval()
    return V11.CarPPOL(n, Q7.RHO, seed, deterministic=True, record=False)


def episode(policy, table, scale, seed, lam=0.0, wkey='uniform', record=False, base='physical', log_phases=False, log_decisions=False, end=3600):
    spat_fn, F = set_provider(table); cars = fleet(seed)
    L = M.LightE(Q7.NetInfo(Q7.NET_S), policy, F, spat_fn, scale, lam, wkey, record, cars, log_phases, log_decisions, base)
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, L, cars, end=end); L.finish(); return L, m


def save_trace(L, path):
    np.savez_compressed(path, ids=np.array(L.ids), phases=np.array(L.P, np.int16), spent=np.array(L.S, np.float64))


def refit(policy, table, scale, tdir, tag, n=8, end=3600):
    files = []
    for s in Q7.TRAIN_SEEDS[:n]:
        L, _ = episode(policy, table, scale, s, log_phases=True, end=end); f = Path(tdir) / f'{tag}_s{s}.npz'; save_trace(L, f); files.append(str(f))
    return FC.fit(files)


def prep(k, out, n, end):
    out = Path(out); out.mkdir(parents=True, exist_ok=True); net7, ck = rlh_net(k); net12 = M.widen(net7); pol = M.greedy(net12)
    t0 = json.loads((P / f'm2b/forecast_rlh{k}.json').read_text()); ones = {t: 1.0 for t in M.TYPES}; W, R, PEN = [], [], []
    files = []
    for s in Q7.TRAIN_SEEDS[:n]:
        L, m = episode(pol, t0, ones, s, log_phases=True, log_decisions=True, record=True, end=end)
        W += [k_['w'] for tk in L.tickets.T.values() for k_ in tk]; f = out / f'prep_rlh{k}_s{s}.npz'; save_trace(L, f); files.append(str(f))
        R += [x['r_phys'] for x in L.credit.log]; PEN += [(d['a'], d['t'], d['open']) for d in L.dlog]
        print(f'prep k{k} s{s}: tickets {L.tickets.stats} teleports {m["teleports"]}', flush=True)
    scale = {t: float(np.mean([w[t] for w in W])) for t in M.TYPES}
    stats = {t: dict(mean=scale[t], zero_share=float(np.mean([w[t] == 0 for w in W])), p95=float(np.percentile([w[t] for w in W], 95)),
                     max=float(np.max([w[t] for w in W]))) for t in M.TYPES}
    for t_ in M.TYPES:                                             # penalty / base-reward ratio at lam 1, with the NORMALISED weights
        pv = [M.penalty(a_, tt, [dict(That=o['That'], wn={t_: (min(M.CLIP, o['w'][t_] / scale[t_]) if scale[t_] > 0 else 0.0)}) for o in op], t_) for a_, tt, op in PEN]
        stats[t_]['pen_mean_lam1'] = float(np.mean(pv)) if pv else 0.0
        stats[t_]['pen_over_base'] = float(np.mean(pv) / np.mean(np.abs(R))) if pv and R else None
    table = FC.fit(files)
    (out / f'prov_rlh{k}_cl.json').write_text(json.dumps(table))
    (out / f'scale_rlh{k}.json').write_text(json.dumps(dict(scale=scale, stats=stats, n_tickets=len(W), mean_abs_r_phys=float(np.mean(np.abs(R))) if R else None,
                                                             source_sha256=sha(__file__), core_sha256=sha(M.__file__), rlh_ckpt=str(ck), rlh_sha256=sha(ck))))
    print('scale', json.dumps(stats), flush=True)


def train(k, arm, lam, out, episodes, block, end, prepdir):
    out = Path(out); out.mkdir(parents=True, exist_ok=True); name = f'E_{arm}_lam{lam:g}_k{k}'; t_start = time.perf_counter()
    net7, ck = rlh_net(k); net12 = M.widen(net7); agent = Q7.DQN(12, 2, 0.9, 11 + 100 * k + 7)
    agent.net.load_state_dict(net12.state_dict()); agent.tgt.load_state_dict(net12.state_dict())
    table = json.loads((Path(prepdir) / f'prov_rlh{k}_cl.json').read_text()); scale = json.loads((Path(prepdir) / f'scale_rlh{k}.json').read_text())['scale']
    base = 'queue' if arm == 'E0q' else 'physical'; wkey = WKEY[arm]; lamv = 0.0 if arm in ('E0q', 'E0p') else lam; log = []; tables = [table]
    tdir = Path(tempfile.mkdtemp(prefix=name + '_', dir=out))
    for ep in range(episodes):
        if ep and ep % block == 0 and ep < 3 * block:
            table = refit(M.greedy(agent.net), table, scale, tdir, f'refit_b{ep // block}', end=end); tables.append(table)
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; te = time.perf_counter()
        L, m = episode(agent.policy(0.05), table, scale, seed, lamv, wkey, record=True, base=base, end=end)
        agent.add(L.credit.trans); loss = agent.train(200)
        lg = L.credit.log; row = dict(ep=ep, seed=seed, n=len(lg), r_mean=float(np.mean([x['r'] for x in lg])) if lg else None,
                                      r_phys_mean=float(np.mean([x['r_phys'] for x in lg])) if lg else None, pen_mean=float(np.mean([x['pen'] for x in lg])) if lg else None,
                                      switches=L.stats['switches'], decisions=L.stats['decisions'], tickets=L.tickets.stats, invalid=L.stats['invalid'],
                                      loss=float(loss), teleports=m['teleports'], t_ep=time.perf_counter() - te)
        log.append(row); print(f"[{time.perf_counter() - t_start:.0f}s] {name} ep {ep} seed {seed} r {row['r_mean']:.4f} r_phys {row['r_phys_mean']:.4f} "
                               f"pen {row['pen_mean']:.4f} sw {row['switches']} tele {row['teleports']} loss {row['loss']:.4f} t {row['t_ep']:.1f}s", flush=True)
        (out / f'{name}.log.json').write_text(json.dumps(log))
    tsha = hashlib.sha256(json.dumps(table, sort_keys=True).encode()).hexdigest()
    torch.save(dict(net=agent.net, kind='m3E', arm=arm, lam=lamv, k=k, base=base, wkey=wkey, table=table, table_sha256=tsha, scale=scale, episodes=episodes,
                    block=block, end=end, source_sha256=sha(__file__), core_sha256=sha(M.__file__), forecast_sha256=sha(FC.__file__), rlh_ckpt=str(ck),
                    rlh_sha256=sha(ck), fleet_ckpt=str(DEV_FLEET), fleet_sha256=sha(DEV_FLEET), pythonhashseed=os.environ.get('PYTHONHASHSEED')), out / f'{name}.pt')
    print('saved', out / f'{name}.pt', flush=True)


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1)
    ap = argparse.ArgumentParser(); sub = ap.add_subparsers(dest='cmd')
    a1 = sub.add_parser('prep'); a1.add_argument('k', type=int); a1.add_argument('out'); a1.add_argument('--episodes', type=int, default=8); a1.add_argument('--end', type=int, default=3600)
    a2 = sub.add_parser('train'); a2.add_argument('k', type=int); a2.add_argument('arm', choices=list(WKEY)); a2.add_argument('lam', type=float); a2.add_argument('out')
    a2.add_argument('--prep', required=True); a2.add_argument('--episodes', type=int, default=60); a2.add_argument('--block', type=int, default=20); a2.add_argument('--end', type=int, default=3600)
    a = ap.parse_args()
    if a.cmd == 'prep':
        prep(a.k, a.out, a.episodes, a.end)
    else:
        train(a.k, a.arm, a.lam, a.out, a.episodes, a.block, a.end, a.prep)
