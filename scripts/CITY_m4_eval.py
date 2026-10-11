#!/usr/bin/env python3
"""M4 evaluator (PROTOCOL_CITY_M4_ARTERIAL_20261004): RESCO arterial4x4, light FT (net programs) or RLK:<checkpoint path>; fleet base (all SUMO)
or sig0.3 (agents _stable_u(seed, id) < 0.5 at σ 0.3).  Route file = SUMO seed = file index; run to 5400 s with unfinished trips counted.
Row: timeloss (all), timeloss_agent / timeloss_human, fuel_agent (mean mg), fuel (mean), teleports, unfinished, n."""
import argparse, hashlib, json, os, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
import scripts.CITY_m4_train_light as T  # noqa: E402
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class Fleet:
    def __init__(self, seed, sigma=None):
        self.seed, self.sigma, self.agents = seed, sigma, set()

    def step(self, t):
        for v in CE.ls.simulation.getDepartedIDList():
            if CE._stable_u(self.seed, v) < 0.5:
                self.agents.add(v)
                if self.sigma is not None:
                    CE.ls.vehicle.setImperfection(v, self.sigma)


def run(a, seed):
    light = None if a.light == 'FT' else LightRLK(NetInfoK(T.NET), Q7.load_policy(a.light.split(':', 1)[1]))
    fl = Fleet(seed, 0.3 if a.fleet == 'sig0.3' else None); fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    rou = T.ROU.format(seed) if a.demand == 1.0 else str(T.VAR.parent / f'arterial4x4_p{a.demand:g}' / f'arterial4x4_{seed}.rou.xml')
    m = CE.run_episode(T.NET, rou, seed, light, fl, end=600 if a.smoke else 5400, tripinfo=ti); rows = CE.read_tripinfo(ti); os.remove(ti)
    ag = [r for r in rows if CE._stable_u(seed, r['id']) < 0.5]; hu = [r for r in rows if CE._stable_u(seed, r['id']) >= 0.5]
    mean = lambda xs, k: float(np.nanmean([x[k] for x in xs])) if xs else float('nan')
    return dict(light=a.light, fleet=a.fleet, demand=a.demand, seed=seed, timeloss=mean(rows, 'timeloss'), timeloss_agent=mean(ag, 'timeloss'), timeloss_human=mean(hu, 'timeloss'),
                fuel=mean(rows, 'fuel'), fuel_agent=mean(ag, 'fuel'), teleports=m['teleports'], unfinished=int(sum(not r['finished'] for r in rows)), n=len(rows))


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    p = argparse.ArgumentParser(); p.add_argument('--light', default='FT'); p.add_argument('--fleet', default='base', choices=['base', 'sig0.3'])
    p.add_argument('--seeds', type=int, nargs='+', default=list(range(100, 110))); p.add_argument('--smoke', action='store_true'); p.add_argument('--demand', type=float, default=1.0)
    p.add_argument('--tag', required=True); p.add_argument('--out', required=True); a = p.parse_args(); Path(a.out).mkdir(parents=True, exist_ok=True)
    R = []
    for s in a.seeds:
        r = run(a, s); R.append(r); print(f"{a.tag} s{s}: TL {r['timeloss']:.2f} agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f} tele {r['teleports']} unf {r['unfinished']} n {r['n']}", flush=True)
    Path(a.out, f'{a.tag}.json').write_text(json.dumps(dict(status='COMPLETE', rows=R, source_sha256=SRC)))
