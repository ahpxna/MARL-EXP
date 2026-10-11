#!/usr/bin/env python3
"""cologne8 evaluator (PROTOCOL_CITY_G4_COLOGNE8_20261004): light FT (net programs) or RLK:<checkpoint name in research/city_sim/g4_cologne8>;
fleet base | sig0.3 | ctrl | acc (agents: _stable_u(seed, id) < 0.5).  Scenario [25200, 28800], tripinfo with unfinished trips.
Row: timeloss (all), timeloss_agent / timeloss_human (means), fuel_agent / fuel_human (sums, mg), teleports, unfinished, n.  Run with PYTHONHASHSEED=0."""
import argparse, hashlib, json, os, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402

R8 = ROOT / 'external_assets/RESCO/resco_benchmark/environments/cologne8'; NET = str(R8 / 'cologne8.net.xml'); ROU = str(R8 / 'cologne8.rou.xml')
VAR = ROOT / 'external_assets/RESCO_variants_20261004'; G4 = ROOT / 'research/city_sim/g4_cologne8'; BEGIN, END = 25200, 28800
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class Fleet:
    """Marks agent vehicles at departure; sig0.3 sets their imperfection.  No speed control."""
    def __init__(self, seed, sigma=None):
        self.seed, self.sigma, self.agents = seed, sigma, set()

    def step(self, t):
        for v in CE.ls.simulation.getDepartedIDList():
            if CE._stable_u(self.seed, v) < 0.5:
                self.agents.add(v)
                if self.sigma is not None:
                    CE.ls.vehicle.setImperfection(v, self.sigma)


def run(a, seed):
    rou = ROU if a.fleet in ('base', 'sig0.3') else str(VAR / a.fleet / f'rou_s{seed}.xml')
    light = None if a.light == 'FT' else LightRLK(NetInfoK(NET), Q7.load_policy(G4 / f"{a.light.split(':', 1)[1]}.pt"))
    fl = Fleet(seed, 0.3 if a.fleet == 'sig0.3' else None)
    with tempfile.TemporaryDirectory(dir=os.environ.get('XPLAY_TMP')) as td:
        ti = str(Path(td) / 'ti.xml'); end = BEGIN + 300 if a.smoke else END
        m = CE.run_episode(NET, rou, seed, light, fl, end=end, tripinfo=ti, extra=('--begin', str(BEGIN)))
        rows = CE.read_tripinfo(ti, fl.agents)
    ag = [r for r in rows if r['agent']]; hu = [r for r in rows if not r['agent']]
    return dict(seed=seed, timeloss=float(np.mean([r['timeloss'] for r in rows])), timeloss_agent=float(np.mean([r['timeloss'] for r in ag])),
                timeloss_human=float(np.mean([r['timeloss'] for r in hu])), fuel_agent=float(np.nansum([r['fuel'] for r in ag])),
                fuel_human=float(np.nansum([r['fuel'] for r in hu])), teleports=m['teleports'], unfinished=sum(not r['finished'] for r in rows), n=len(rows), n_agent=len(ag))


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.tag}.json'
    if fn.exists() and json.loads(fn.read_text()).get('status') == 'COMPLETE':
        print('skip', a.tag); return
    rows = []
    for s in a.seeds:
        r = run(a, s); rows.append(r)
        print(f"{a.tag} s{s}: TL {r['timeloss']:.2f} (agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f}) fuel_agent {r['fuel_agent']:.0f} tele {r['teleports']} unf {r['unfinished']}", flush=True)
    fn.write_text(json.dumps(dict(status='COMPLETE', rows=rows, args=vars(a), source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED')), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', default='FT'); p.add_argument('--fleet', default='base', choices=['base', 'sig0.3', 'ctrl', 'acc'])
    p.add_argument('--seeds', type=int, nargs='+', default=list(range(100, 110))); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag', required=True); p.add_argument('--out', required=True)
    main(p.parse_args())
