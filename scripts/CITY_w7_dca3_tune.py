#!/usr/bin/env python3
"""DCA3 AUDIT FIX, NOT A REGISTERED PERFORMANCE RESULT. Corrects DCA2 horizon and initialization.
W7-2 DCA2 tuner (PROTOCOL_CITY_WAVE7_20261005): DC-Ada's _adapt_accept_reject (github.com/alqithami/DC-ADA src/agents/methods.py) ported to
the 16 signal controllers of one frozen RL-H light checkpoint, the TSI hybrid fleet service unchanged.  Robots in fixed (sorted id) order;
per robot: 1 baseline + M = 5 candidates perturbing only that robot's transform by sigma 0.05 * eps; CRN: every rollout of a round uses the
round's TUNE seed; accept iff best - baseline > tau (0); update = step 1.0 * sigma * eps_best.  Rollouts truncated at 0.25 x 5400 s = 1350 s.
Return = -J vs R (same seed, same horizon), J = dfuel_agent % + 4[dTL_agent + 0.25]+ + 4[dTL_city]+ + 4[dTL_human]+.  Budget = 176 truncated
rollouts (= 44 x 5400 s), R references included.  Each rollout is one subprocess of CITY_eval_dca2.py via CITY_f1a1_run.py.
Usage: CITY_w7_dca3_tune.py <t> <out dir>      DCA3_SMOKE=1: budget 9, horizon 600 s (pipeline smoke only)"""
import json, os, subprocess, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
PY = str(ROOT / 'external_envs/city_runtime/bin/python'); RUN = [PY, '-u', str(ROOT / 'scripts/CITY_f1a1_run.py'), 'scripts/CITY_dca3_run.py']
TB = ROOT / 'research/city_sim/f1b_20261004/prep'; MOD = ROOT / 'research/city_sim/tsi_20261005/cmodel/c2'; P = ROOT / 'research/city_sim/spat_pilot_20261004/fleets_v11'
SEEDS = [660, 661, 662, 663]; M, SIGMA, TAU, STEP = 5, 0.05, 0.0, 1.0; KEYS = ('fuel_agent', 'timeloss', 'timeloss_agent', 'timeloss_human')
SMOKE = os.environ.get('DCA3_SMOKE') == '1'; END = 600 if SMOKE else 1350; BUDGET = 9 if SMOKE else 176


def main(t, out):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    import scripts.CITY_dcada_layer as DC
    out = Path(out); ro = out / f'roll_t{t}'; ro.mkdir(parents=True, exist_ok=True); fin = out / f'dca3_t{t}.json'
    if fin.exists():
        raise SystemExit('Use a fresh output directory for an amended DCA3 study; no silent cache reuse')
    import scripts.CITY_q7_cross_version as Q7
    ids = sorted(Q7.NetInfo(Q7.NET_S).tls); params = {i: DC.TransformationLayer().get_params_vector().clone() for i in ids}
    F = ['--light', f'RL-H:{t}', '--fleet', f'PL:{P}/L11_s13_fleet.pt']
    N4 = ['scripts/CITY_eval_n4.py', '--n4', f'0.5:hyb:{TB}/prov_rlh{t}_cl.json:{MOD}/n2_k{t}.pt'] + F
    used = [0]; log = []; R = {}; nroll = [0]

    def roll(args, seed, tag, env):
        f = ro / f'{tag}.json'
        if not f.exists():
            e = dict(os.environ, DCA3_END=str(END), **env)
            r = subprocess.run(RUN + args + ['--seeds', str(seed), '--tag', tag, '--out', str(ro)], env=e, stdout=open(ro / 'run.log', 'a'), stderr=subprocess.STDOUT)
            if r.returncode != 0 or not f.exists():
                raise SystemExit(f'rollout failed: {tag}')
        doc = json.loads(f.read_text()); rr = doc['rows']; assert doc['status'] == 'COMPLETE' and len(rr) == 1 and rr[0]['seed'] == seed, tag
        assert rr[0].get('dca3_horizon_s') == END, (tag, rr[0].get('dca3_horizon_s'), END)
        used[0] += 1; return rr[0]

    def ret(seed, tag):
        p = ro / f'{tag}_params.pt'; torch.save({i: v.clone() for i, v in params.items()}, p)
        x = roll(N4, seed, tag, dict(DCA3_PARAMS=str(p))); r0 = R[seed]
        d = dict(fuel=100 * (x['fuel_agent'] / r0['fuel_agent'] - 1), **{q: x[q] - r0[q] for q in KEYS[1:]})
        return -(d['fuel'] + 4 * max(0.0, d['timeloss_agent'] + 0.25) + 4 * max(0.0, d['timeloss']) + 4 * max(0.0, d['timeloss_human'])), d
    gen = torch.Generator().manual_seed(2000 + t); rnd = 0; accepted = 0
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
            print(f't{t} round {rnd} seed {seed} robot {i}: base {base:+.3f} best {best:+.3f} accepted {acc} used {used[0]}/{BUDGET}', flush=True)
        rnd += 1
    torch.save(params, out / f'dca3_params_t{t}.pt')
    fin.write_text(json.dumps(dict(t=t, rollouts=used[0], budget=BUDGET, horizon_s=END, M=M, sigma=SIGMA, tau=TAU, step=STEP, rounds=rnd, accepted=accepted,
                                   param_norm=float(sum(v.norm() ** 2 for v in params.values()) ** 0.5), seeds=SEEDS, actual_seeds=sorted({x['seed'] for x in log}), declared_seconds=used[0]*END, revision='DCA3 audit correction; not yet confirmed', log=log), indent=1))
    print(f't{t} done: rollouts {used[0]}, accepted {accepted}', flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2])
