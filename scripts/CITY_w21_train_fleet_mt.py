#!/usr/bin/env python3
"""W21-L (PROTOCOL_CITY_WAVE21_20261015): a resumable F1-B-recipe fleet trainer for the full Midtown map in the MT-E setting.
Run as  DEMO_midtown.py scripts/CITY_w20_run.py scripts/CITY_w21_train_fleet_mt.py <args>  with MT_NET=midtown_full MT_BASE=actrest.
  * provider and light: scripts/CITY_w13_train_f1bt.py is imported (W13_N4 = "<q>:<table>:<model>", W13_AB = "0:0"), so the fleet trains
    with the deployed SPaT service (the N4 hybrid provider as adapted by DEMO_midtown, tracker stepped after the cars) and the frozen learned
    light without adapter (A = B = 0 is the raw light exactly);
  * the 56 multi-phase junctions run their actuated programs: every CE.run_episode call gets '-a midtown_full_act_rest.add.xml'
    (the F1-B loop calls CE.run_episode directly, which bypasses DEMO_midtown's build_light patch);
  * the loop is CITY_fleet_train_f1b.main line for line (PPO update, scratch init, TRAIN seeds = Midtown days 10-17, logging), plus a
    checkpoint every --ckpt episodes (net, optimiser, numpy / torch RNG states, log) and --resume from it.
Saves <name>_fleet.pt in the v11 format (usable as PL:<path>).  PYTHONHASHSEED=0, OMP_NUM_THREADS=1."""
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
assert os.environ.get('MT_BASE') == 'actrest' and os.environ.get('MT_NET') == 'midtown_full', 'W21-L needs MT_NET=midtown_full MT_BASE=actrest'
import scripts.CITY_w13_train_f1bt as W13  # noqa: E402  (provider + light patches, needs W13_N4 / W13_AB)
T = W13.T; CE = W13.CE; Q7 = T.Q7; X2 = T.X2; V8 = T.V8; V9 = T.V9; V11 = T.V11
ADD = ROOT / 'research/city_sim/net/midtown_full_act_rest.add.xml'; assert ADD.exists()
_rep = CE.run_episode


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    ex = list(kw.get('extra', ()))
    if str(ADD) not in ex:
        ex += ['-a', str(ADD)]
    kw['extra'] = tuple(ex); return _rep(net, rou, seed, light, cars, **kw)


CE.run_episode = run_episode
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()  # noqa: E731
SRC = sha(__file__)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fin = out / f'{a.name}_fleet.pt'; ck = out / f'{a.name}_ckpt.pt'
    if fin.exists():
        print('skip', a.name); return
    _n, lck, _m = X2.light_spec(f'RL-H:{a.light_k}'); lpol = Q7.load_policy(lck); info = Q7.NetInfo(Q7.NET_S)
    print(f'W21-L {a.name}: light RL-H:{a.light_k} ({lck}), {len(info.tls)} learned signals, TRAIN days {Q7.TRAIN_SEEDS}, provider {os.environ["W13_N4"]}', flush=True)
    net = V9.NetR(a.seed); net.train(); opt = torch.optim.Adam(net.parameters(), lr=3e-4); rng = np.random.default_rng(a.seed); torch.manual_seed(a.seed)
    log, ep0 = [], 0
    if a.resume and ck.exists():
        c = torch.load(ck, weights_only=False); net.load_state_dict(c['net']); opt.load_state_dict(c['opt']); rng.bit_generator.state = c['rng']
        torch.set_rng_state(c['torch_rng']); log = c['log']; ep0 = c['ep'] + 1; print(f'resumed from episode {c["ep"]}', flush=True)
    end = 300 if a.smoke else 3600; t0 = time.perf_counter()
    for ep in range(ep0, a.episodes):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; te = time.perf_counter()
        cars = V11.CarPPOL(net, Q7.RHO, seed, deterministic=False, record=True); light = CE.LightRL(info, lpol)
        m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, light, cars, end=end); cars.finish(); tsim = time.perf_counter() - te
        batch = V8.gae(cars.segments, net)
        pl, vl, rdev = V8.ppo_update(net, opt, batch, rng=rng) if batch is not None else (float('nan'),) * 3
        segs = [s for s in cars.segments if s['dec']]; trip_ret = [sum(d['rew'] for d in s['dec']) for s in segs]; st = cars.stats
        row = dict(ep=ep, seed=seed, decisions=st['decisions'], segments=len(segs), teleports=m['teleports'], popped=st['popped'],
                   seg_return_mean=float(np.mean(trip_ret)) if trip_ret else float('nan'),
                   mean_r=float(np.mean([d['rew'] for s in segs for d in s['dec']])) if segs else float('nan'),
                   pi_loss=float(pl), v_loss=float(vl), ratio_dev=float(rdev), log_std=float(net.log_std.item()), t_sim=tsim, wall=time.perf_counter() - t0)
        log.append(row)
        print(f"[{row['wall']:.0f}s] {a.name} ep {ep} seed {seed} dec {row['decisions']} segRet {row['seg_return_mean']:.2f} meanR {row['mean_r']:.3f} "
              f"vloss {row['v_loss']:.3f} std {np.exp(row['log_std']):.3f} tele {row['teleports']} sim {tsim:.1f}s", flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
        if (ep + 1) % a.ckpt == 0 or ep + 1 == a.episodes:
            tmp = ck.with_suffix('.tmp'); torch.save(dict(net=net.state_dict(), opt=opt.state_dict(), rng=rng.bit_generator.state, torch_rng=torch.get_rng_state(),
                                                          log=log, ep=ep), tmp); os.replace(tmp, ck)
    torch.save(dict(net=net, kind='ppo_residual_glosaL', spat='on', reward='AD_tail', name=a.name, seed=a.seed, episodes=a.episodes, light=f'RL-H:{a.light_k}',
                    light_sha256=sha(lck), init='scratch', init_sha256='scratch', provider=os.environ['W13_N4'], q=float(os.environ['W13_N4'].split(':')[0]),
                    corrected=True, provider_version='n4-hyb-midtown', w21_mt=dict(net=os.environ['MT_NET'], base=os.environ['MT_BASE'], add=str(ADD), days=list(Q7.TRAIN_SEEDS)),
                    source_sha256=SRC, f1b_sha256=sha(T.__file__), w13_sha256=sha(W13.__file__), v11_sha256=sha(V11.__file__),
                    pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fin)
    print('saved', fin, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--seed', type=int, required=True); p.add_argument('--light-k', type=int, required=True)
    p.add_argument('--episodes', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--ckpt', type=int, default=5); p.add_argument('--resume', action='store_true'); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
