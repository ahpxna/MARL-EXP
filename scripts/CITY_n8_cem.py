#!/usr/bin/env python3
"""N8 CEM tuner (PROTOCOL_CITY_N8_CDC_20261005).  Tunes theta of the CDC light on TRAIN seeds with common random numbers (every candidate
runs the same seeds), fleet R10 L11_s13, through CITY_eval_n8.py subprocesses (LANES parallel, nice 5).
  variant m3  : CDC + fleet (program SPaT); J = agent fuel % vs R + W * sum_g max(0, dTL_g)   (g = city, agent, human; dTL in s/veh vs R)
  variant city: CDC + fleet without SPaT (sigma*); J = city TL (s/veh)   -- a light tuned for traffic alone
R = RL-H k0 + no SPaT on the same TRAIN seeds (computed first).  Writes <out>/cem_<variant>.json (all candidates, the final mean / best).
Usage: CITY_n8_cem.py <variant> <out_dir> [--iters 5 --pop 12 --elite 3 --seeds 0 1 2 --lanes 4]"""
import argparse, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; PY = str(ROOT / 'external_envs/city_runtime/bin/python'); FLEET = 'PL:research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt'
LO = np.array([5.0, 0.0, -3.0, -3.0]); HI = np.array([40.0, 3.0, 0.0, 0.0]); W = 5.0


def run(tag, light, spat, seeds, out):
    f = out / f'{tag}.json'
    if not f.exists():
        cmd = ['nice', '-n', '5', PY, '-u', str(ROOT / 'scripts/CITY_eval_n8.py'), '--spat', spat, '--light', light, '--fleet', FLEET, '--seeds', *map(str, seeds), '--tag', tag, '--out', str(out)]
        with open(out / 'run.log', 'a') as lg:
            subprocess.run(cmd, cwd=ROOT, stdout=lg, stderr=subprocess.STDOUT, check=True, env={**os.environ, 'PYTHONHASHSEED': '0', 'OMP_NUM_THREADS': '1', 'XPLAY_TMP': str(out)})
    J = json.loads(f.read_text()); assert J['status'] == 'COMPLETE', tag
    return {r['seed']: r for r in J['rows']}


def score(var, rows, R):
    if var == 'city':
        return float(np.mean([rows[s]['timeloss'] for s in R]))
    fa = 100 * (np.mean([rows[s]['fuel_agent'] for s in R]) / np.mean([R[s]['fuel_agent'] for s in R]) - 1)
    pen = sum(max(0.0, np.mean([rows[s][k] - R[s][k] for s in R])) for k in ('timeloss', 'timeloss_agent', 'timeloss_human'))
    return float(fa + W * pen)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('variant', choices=('m3', 'city')); p.add_argument('out')
    p.add_argument('--iters', type=int, default=5); p.add_argument('--pop', type=int, default=12); p.add_argument('--elite', type=int, default=3)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2]); p.add_argument('--lanes', type=int, default=4); a = p.parse_args()
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); spat = 'program' if a.variant == 'm3' else 'none'
    R = run('R_train', 'RL-H:0', 'none', a.seeds, out); rng = np.random.default_rng(0)
    mu = np.array([20.0, 1.0, -0.5, -0.5]); sd = np.array([8.0, 0.8, 0.8, 0.8]); hist = []
    for it in range(a.iters):
        TH = np.clip(mu + sd * rng.standard_normal((a.pop, 4)), LO, HI); TH[0] = np.clip(mu, LO, HI)       # candidate 0 = the current mean
        tags = [f'{a.variant}_i{it}_c{j}' for j in range(a.pop)]
        with ThreadPoolExecutor(a.lanes) as ex:
            res = list(ex.map(lambda x: run(x[0], 'CDC:' + ','.join(f'{v:.4f}' for v in x[1]), spat, a.seeds, out), zip(tags, TH)))
        J = np.array([score(a.variant, r, R) for r in res]); el = TH[np.argsort(J)[:a.elite]]
        hist += [dict(it=it, theta=TH[j].tolist(), J=float(J[j]), tag=tags[j]) for j in range(a.pop)]
        mu, sd = el.mean(0), np.maximum(el.std(0), np.array([1.0, 0.05, 0.05, 0.05]))
        print(f'iter {it}: best J {J.min():+.3f} theta {np.round(TH[J.argmin()], 3).tolist()} | mean J {J.mean():+.3f} | new mu {np.round(mu, 3).tolist()}', flush=True)
    best = min(hist, key=lambda h: h['J'])
    (out / f'cem_{a.variant}.json').write_text(json.dumps(dict(variant=a.variant, seeds=a.seeds, mean=np.clip(mu, LO, HI).tolist(), best=best, hist=hist), indent=1))
    print('final mean', np.round(np.clip(mu, LO, HI), 3).tolist(), 'best', best)
