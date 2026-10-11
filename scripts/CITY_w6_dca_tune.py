#!/usr/bin/env python3
"""W6-1 DCA tuner (PROTOCOL_CITY_WAVE6_20261005): DC-Ada (Alqithami, IEEE Access 2026; accept/reject random search with common random
numbers, as ported in CITY_dcada_tune.py) over the affine transform o' = o*exp(s) + b of the FROZEN RL-H light's 7 inputs, with TSI's
fleet-side hybrid service unchanged.  Per light t: R on TUNE 660-663 (4 rollouts), then 4 rounds x (1 base + 9 candidates) under the round's
seed (CRN); best candidate accepted iff its return exceeds the base's (tau 0).  Budget 44 rollouts = TSI-2's tuning.  Return = -J,
J = dfuel_agent % + 4[dTL_agent + 0.25]+ + 4[dTL_city]+ + 4[dTL_human]+ vs R on the same seed.  Each rollout is one subprocess of the frozen
evaluators (CITY_eval_n4.py / CITY_eval_f1.py via CITY_f1a1_run.py).  Usage: CITY_w6_dca_tune.py <t> <out dir>"""
import json, os, subprocess, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]
PY = str(ROOT / 'external_envs/city_runtime/bin/python'); RUN = [PY, '-u', str(ROOT / 'scripts/CITY_f1a1_run.py')]
TB = ROOT / 'research/city_sim/f1b_20261004/prep'; MOD = ROOT / 'research/city_sim/tsi_20261005/cmodel/c2'; P = ROOT / 'research/city_sim/spat_pilot_20261004/fleets_v11'
SEEDS = [660, 661, 662, 663]; ROUNDS, M, SIGMA, TAU = 4, 9, 0.3, 0.0; KEYS = ('fuel_agent', 'timeloss', 'timeloss_agent', 'timeloss_human')
SMOKE = os.environ.get('DCA_SMOKE') == '1'
if SMOKE:                                                          # pipeline smoke: 1 seed, 1 round x (1 + 1), 300 s episodes
    SEEDS, ROUNDS, M = [660], 1, 1


def row(out, tag, args, seed):
    f = out / f'{tag}.json'
    if not f.exists():
        r = subprocess.run(RUN + args + ['--seeds', str(seed), '--tag', tag, '--out', str(out)] + (['--smoke'] if SMOKE else []), stdout=open(out / 'run.log', 'a'), stderr=subprocess.STDOUT)
        if r.returncode != 0 or not f.exists():
            raise SystemExit(f'rollout failed: {tag}')
    rr = json.loads(f.read_text())['rows']; assert len(rr) == 1 and rr[0]['seed'] == seed, tag
    return rr[0]


def main(t, out):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(out); ro = out / f'roll_t{t}'; ro.mkdir(parents=True, exist_ok=True); fin = out / f'dca_t{t}.json'
    if fin.exists():
        print('skip', fin); return
    F = ['--light', f'RL-H:{t}', '--fleet', f'PL:{P}/L11_s13_fleet.pt']
    N4 = ['scripts/CITY_eval_n4.py', '--n4', f'0.5:hyb:{TB}/prov_rlh{t}_cl.json:{MOD}/n2_k{t}.pt'] + F
    used = 0; log = []; R = {}
    for s in SEEDS:
        R[s] = row(ro, f'R_s{s}', ['scripts/CITY_eval_f1.py', '--spat-arm', 'none'] + F, s); used += 1

    def ret(theta, s, tag):
        nonlocal used
        p = ro / f'{tag}_theta.json'; p.write_text(json.dumps(dict(s=theta[:7].tolist(), b=theta[7:].tolist())))
        x = row(ro, tag, N4 + ['--light-obs', f'affine:{p}'], s); used += 1; r0 = R[s]
        d = dict(fuel=100 * (x['fuel_agent'] / r0['fuel_agent'] - 1), **{q: x[q] - r0[q] for q in KEYS[1:]})
        J = d['fuel'] + 4 * max(0.0, d['timeloss_agent'] + 0.25) + 4 * max(0.0, d['timeloss']) + 4 * max(0.0, d['timeloss_human'])
        return -J, d
    rng = np.random.default_rng(1000 + t); theta = np.zeros(14)
    for r in range(ROUNDS):
        s = SEEDS[r]; base, bd = ret(theta, s, f'r{r}_base'); best, best_eps, best_d = base, None, bd
        for m in range(M):
            eps = rng.standard_normal(14); v, d = ret(theta + SIGMA * eps, s, f'r{r}_c{m}')
            log.append(dict(round=r, seed=s, cand=m, ret=v, **d))
            if v > best:
                best, best_eps, best_d = v, eps, d
        acc = best_eps is not None and best - base > TAU
        if acc:
            theta = theta + SIGMA * best_eps
        log.append(dict(round=r, seed=s, base=base, base_d=bd, best=best, accepted=bool(acc)))
        print(f't{t} round {r} seed {s}: base {base:+.3f} best {best:+.3f} accepted {acc} used {used}', flush=True)
    assert used == len(SEEDS) + ROUNDS * (1 + M) == (3 if SMOKE else 44), used
    (out / f'affine_t{t}.json').write_text(json.dumps(dict(s=theta[:7].tolist(), b=theta[7:].tolist())))
    fin.write_text(json.dumps(dict(t=t, theta=theta.tolist(), rollouts=used, sigma=SIGMA, M=M, rounds=ROUNDS, tau=TAU, seeds=SEEDS, log=log), indent=1))
    print(f't{t} done: rollouts {used}; theta {np.round(theta, 3).tolist()}', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2])
