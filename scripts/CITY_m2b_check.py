#!/usr/bin/env python3
"""M2b checks (Amendment M2b).  Exit 1 on failure.  Traffic 0 unless stated, 5400 s eval rows (|diff| <= 1e-9).
  KM2b-0  the new wrapper with --spat-arm program under FT == CITY_eval6_m2 naive under FT, F0a (theta_s2): the wrapper does not perturb
  KM2b-1  online inputs == offline inputs: in a σ* run under RL-H:0 with --record, the (phase, spent) that a fleet-step probe reads at
          every second equal the recorded trace row (P[t-1], spent[t-1]) -> the offline validation scores what the fleet sees
  KM2b-2  under RL-H:0, F0a with fc50: forecast SPaT is published (valid calls > 0) and the fleet commands (> 0 vehicle-seconds)
  KM2b-3  under RL-H:0, F0a with none == the σ* fleet (eval4_sigma 0.3): no SPaT -> no command (as KM2-2)"""
import json, os, subprocess, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); PY = sys.executable
TH = 'research/city_sim/spat_pilot_20261004/lane_d/theta_s2.json'; KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports')


def run(args, tag, out, light, seed=0):
    subprocess.run([PY, '-u', *args, '--light', light, '--seeds', str(seed), '--tag', tag, '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; bad = []; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    a = run(['scripts/CITY_eval6_m2b.py', '--spat-arm', 'program', '--fleet', f'ESLD:{TH}'], 'b_prog', out, 'FT')
    b = run(['scripts/CITY_eval6_m2.py', '--spat-label', 'naive', '--fleet', f'ESLD:{TH}'], 'a_naive', out, 'FT')
    c = run(['scripts/CITY_eval6_m2b.py', '--spat-arm', 'none', '--fleet', f'ESLD:{TH}'], 'b_none', out, 'RL-H:0')
    d = run(['scripts/CITY_eval4_sigma.py', '--sigma', '0.3', '--fleet', 'L-ACT:0', '--guard', 'always'], 's03', out, 'RL-H:0')
    for nm, x, y in (('KM2b-0', a, b), ('KM2b-3', c, d)):
        print(nm, {k: x[k] for k in KEYS}); print(' ' * len(nm), {k: y[k] for k in KEYS})
        if any(abs(x[k] - y[k]) > 1e-9 for k in KEYS):
            bad.append(f'{nm} identity')
    e = run(['scripts/CITY_eval6_m2b.py', '--spat-arm', 'fc50', '--fleet', f'ESLD:{TH}'], 'b_fc50', out, 'RL-H:0')
    sc = json.loads((Path(out) / 'b_fc50_m2b.json').read_text()); print('KM2b-2 sidecar', sc)
    if not (sc['valid'] > 0 and sc['commanded'] > 0):
        bad.append('KM2b-2 forecast not published or no command')
    print(f"smoke RL-H:0 fc50 F0a vs σ*: fuel {100 * (e['fuel_agent'] / d['fuel_agent'] - 1):+.2f} %, agent TL {e['timeloss_agent'] - d['timeloss_agent']:+.2f}, "
          f"human TL {e['timeloss_human'] - d['timeloss_human']:+.2f} (not an endpoint)")
    # KM2b-1: probe inside a σ* run with --record
    import scripts.CITY_eval4 as E4
    import scripts.CITY_env as CE
    import scripts.CITY_fleet_v8 as V8
    import argparse
    seen = []

    class Probe(V8.CarGLOSA):
        def step(self, t):
            ls = CE.ls
            for v in ls.simulation.getDepartedIDList():
                if self.is_agent(v):
                    self.agents.add(v); ls.vehicle.setImperfection(v, 0.3)
            if int(t) % 7 == 0:
                for tid in ls.trafficlight.getIDList():
                    seen.append((int(t), tid, ls.trafficlight.getPhase(tid), ls.trafficlight.getSpentDuration(tid)))
    E4.load_fleet = lambda spec, seed, guard: (Probe(E4.Q7.RHO, seed), 'probe')
    rec = Path(out) / 'probe_s{seed}.npz'
    ns = argparse.Namespace(light='RL-H:0', light_obs='raw', light_fallback='none', fleet='probe', guard='none', record=str(rec), replay=None, replay_dir=None,
                            discharge=False, delay_trace=False, swap_at=None, swap_light=None, swap_fleet=None, seeds=[100], smoke=False, tag='probe', out=out)
    E4.run(ns, 100, 1800); z = np.load(str(rec).replace('{seed}', '100'), allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']
    mism = sum(1 for t, tid, ph, sp in seen if t - 1 < len(P) and (int(P[t - 1, ids.index(tid)]) != ph or abs(float(S[t - 1, ids.index(tid)]) - sp) > 1e-9))
    print(f'KM2b-1: {len(seen)} probe reads, {mism} mismatches with the recorded trace')
    if mism or not seen:
        bad.append('KM2b-1 online vs recorded inputs')
    print('M2B CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
