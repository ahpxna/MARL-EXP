#!/usr/bin/env python3
"""W12-4 DCA-task tuner (PROTOCOL_CITY_WAVE12_20261006, Amendment A3): DCA3's DC-Ada search (CITY_w7_dca3_tune.py, unchanged search) with
(i) the transform of DCAS_MODE (info: RL-H input + TSI's speed-binned counts, 11 -> 7; raw: 7 -> 7), (ii) the full 5400-s horizon for references
and candidates, (iii) budget 352 full rollouts with parameters saved at 88 / 176 / 352 rollouts.  Rollouts run through CITY_w12_dcas.py.
Usage: CITY_w12_dcas_tune.py <t> <info|raw> <out dir>      DCAS_SMOKE=1: budget 9, checkpoints 3 / 6 / 9, horizon 600 s"""
import json, os, subprocess, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
PY = str(ROOT / 'external_envs/city_runtime/bin/python'); RUN = [PY, '-u', str(ROOT / 'scripts/CITY_f1a1_run.py'), 'scripts/CITY_w12_dcas.py']
TB = ROOT / 'research/city_sim/f1b_20261004/prep'; MOD = ROOT / 'research/city_sim/tsi_20261005/cmodel/c2'; P = ROOT / 'research/city_sim/spat_pilot_20261004/fleets_v11'
SEEDS = [660, 661, 662, 663]; M, SIGMA, TAU, STEP = 5, 0.05, 0.0, 1.0; KEYS = ('fuel_agent', 'timeloss', 'timeloss_agent', 'timeloss_human')
SMOKE = os.environ.get('DCAS_SMOKE') == '1'; END = 600 if SMOKE else 5400; BUDGET = 9 if SMOKE else 352; CKPT = (3, 6, 9) if SMOKE else (88, 176, 352)


def main(t, mode, out):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    import scripts.CITY_w12_dcas as DS
    out = Path(out); ro = out / f'roll_t{t}'; ro.mkdir(parents=True, exist_ok=True); fin = out / f'dcas_{mode}_t{t}.json'
    if fin.exists():
        raise SystemExit('Use a fresh output directory for an amended DCA3 study; no silent cache reuse')
    import scripts.CITY_q7_cross_version as Q7
    ids = sorted(Q7.NetInfo(Q7.NET_S).tls); params = {i: DS.new_layer(mode).get_params_vector().clone() for i in ids}
    F = ['--light', f'RL-H:{t}', '--fleet', f'PL:{P}/L11_s13_fleet.pt']
    N4 = ['scripts/CITY_eval_n4.py', '--n4', f'0.5:hyb:{TB}/prov_rlh{t}_cl.json:{MOD}/n2_k{t}.pt'] + F
    used = [0]; log = []; R = {}; nroll = [0]

    def roll(args, seed, tag, env):
        f = ro / f'{tag}.json'
        if not f.exists():
            e = dict(os.environ, DCAS_END=str(END), DCAS_MODE=mode, **env)
            r = subprocess.run(RUN + args + ['--seeds', str(seed), '--tag', tag, '--out', str(ro)], env=e, stdout=open(ro / 'run.log', 'a'), stderr=subprocess.STDOUT)
            if r.returncode != 0 or not f.exists():
                raise SystemExit(f'rollout failed: {tag}')
        doc = json.loads(f.read_text()); rr = doc['rows']; assert doc['status'] == 'COMPLETE' and len(rr) == 1 and rr[0]['seed'] == seed, tag
        assert rr[0].get('dcas_horizon_s') == END and rr[0].get('dcas_mode') == mode, (tag, rr[0].get('dcas_horizon_s'), END)
        used[0] += 1; return rr[0]

    def ret(seed, tag):
        p = ro / f'{tag}_params.pt'; torch.save({i: v.clone() for i, v in params.items()}, p)
        x = roll(N4, seed, tag, dict(DCAS_PARAMS=str(p))); r0 = R[seed]
        d = dict(fuel=100 * (x['fuel_agent'] / r0['fuel_agent'] - 1), **{q: x[q] - r0[q] for q in KEYS[1:]})
        return -(d['fuel'] + 4 * max(0.0, d['timeloss_agent'] + 0.25) + 4 * max(0.0, d['timeloss']) + 4 * max(0.0, d['timeloss_human'])), d
    gen = torch.Generator().manual_seed(2000 + t); rnd = 0; accepted = 0; saved = set()
    while used[0] < BUDGET:
        seed = SEEDS[rnd % len(SEEDS)]
        if seed not in R:
            R[seed] = roll(['scripts/CITY_eval_f1.py', '--spat-arm', 'none'] + F, seed, f'R_s{seed}', {}); log.append(dict(round=rnd, seed=seed, R=True))
        for i in ids:
            if used[0] >= BUDGET:
                break
            base, bd = ret(seed, f'r{rnd}_{i}_base'); best, best_eps = base, None; cur = params[i].clone()
            for m in range(M):
                if used[0] >= BUDGET:
                    break
                eps = torch.randn(cur.shape, generator=gen); params[i] = cur + SIGMA * eps; v, d = ret(seed, f'r{rnd}_{i}_c{m}'); params[i] = cur
                log.append(dict(round=rnd, seed=seed, robot=i, cand=m, ret=v, **d))
                if v > best:
                    best, best_eps = v, eps
            acc = best_eps is not None and (best - base) > TAU
            if acc:
                params[i] = cur + STEP * SIGMA * best_eps; accepted += 1
            log.append(dict(round=rnd, seed=seed, robot=i, base=base, base_d=bd, best=best, accepted=bool(acc), used=used[0]))
            print(f't{t} {mode} round {rnd} seed {seed} robot {i}: base {base:+.3f} best {best:+.3f} accepted {acc} used {used[0]}/{BUDGET}', flush=True)
            for b in CKPT:
                if used[0] >= b and b not in saved:
                    torch.save({k: v.clone() for k, v in params.items()}, out / f'dcas_{mode}_t{t}_b{b}.pt'); saved.add(b)
                    log.append(dict(checkpoint=b, used=used[0], accepted=accepted))
        rnd += 1
    for b in CKPT:
        if b not in saved:
            torch.save({k: v.clone() for k, v in params.items()}, out / f'dcas_{mode}_t{t}_b{b}.pt'); saved.add(b)
    fin.write_text(json.dumps(dict(t=t, mode=mode, checkpoints=list(CKPT), rollouts=used[0], budget=BUDGET, horizon_s=END, M=M, sigma=SIGMA, tau=TAU, step=STEP, rounds=rnd, accepted=accepted,
                                   param_norm=float(sum(v.norm() ** 2 for v in params.values()) ** 0.5), seeds=SEEDS, actual_seeds=sorted({x['seed'] for x in log if 'seed' in x}), declared_seconds=used[0]*END, revision='W12-4 DCA-task (A3); follow-up study after DCA3', log=log), indent=1))
    print(f't{t} done: rollouts {used[0]}, accepted {accepted}', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2], sys.argv[3])
