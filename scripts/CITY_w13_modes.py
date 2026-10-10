#!/usr/bin/env python3
"""W13-1b (PROTOCOL_CITY_WAVE13_20261006): fuel by driving mode.  Wraps any CITY_eval4-based target (no existing file is edited): a Logger
subclass reads, every second and for every vehicle in the network, speed v, acceleration a and libsumo's getFuelConsumption (the emission
class in force, so it composes with CITY_w9_run em:<class>), and accumulates fuel and vehicle-seconds in a grid
    acceleration class  {a < -0.1, |a| <= 0.1, a > 0.1} (m/s^2)  x  speed band  {[0,0.1), [0.1,2), [2,5), [5,10), [10,inf)} (m/s)
separately for agents and humans.  Self-check KM13-1b (in the row): the grid total over all vehicles against the tripinfo fuel total of the
same run (sum of finite fuel_abs), ratio fields modes_ratio_all; a report refuses rows outside [0.98, 1.02].
Usage: CITY_w13_modes.py <target script> <its args>   (e.g. CITY_w9_run.py em:PHEMlight5/PC_EU4_G scripts/CITY_w13_modes.py scripts/CITY_eval_n4.py ...)"""
import hashlib, math, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402

SB = (0.1, 2.0, 5.0, 10.0)          # speed band edges (m/s)
ST = dict(grid=None, cars=None, rows=None)


def _new():
    return {g: [[[0.0, 0] for _ in range(5)] for _ in range(3)] for g in ('agent', 'human')}


def _sb(v):
    for i, e in enumerate(SB):
        if v < e:
            return i
    return 4


class MLogger(E4.Logger):
    def __init__(self, info, cars, *a, **k):
        super().__init__(info, cars, *a, **k); ST['grid'] = _new(); ST['cars'] = cars

    def step(self, t):
        super().step(t)
        ls = CE.ls; G = ST['grid']; cars = ST['cars']
        for v in ls.vehicle.getIDList():
            sp = ls.vehicle.getSpeed(v); ac = ls.vehicle.getAcceleration(v); fc = ls.vehicle.getFuelConsumption(v)
            ab = 0 if ac < -0.1 else (1 if ac <= 0.1 else 2)
            cell = G['agent' if (cars is not None and cars.is_agent(v)) else 'human'][ab][_sb(sp)]; cell[0] += fc; cell[1] += 1


E4.Logger = MLogger
_read = E4.read_tripinfo


def read_tripinfo(path):
    rows = _read(path); ST['rows'] = rows; return rows


E4.read_tripinfo = read_tripinfo
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); G = ST['grid']; rows = ST['rows'] or []
    tot_grid = sum(c[0] for g in G.values() for r in g for c in r)
    tot_trip = sum(r['fuel'] for r in rows if isinstance(r.get('fuel'), float) and math.isfinite(r['fuel']))
    out.update(modes=G, modes_speed_edges=list(SB), modes_total_grid=tot_grid, modes_total_trip=tot_trip,
               modes_ratio_all=(tot_grid / tot_trip) if tot_trip > 0 else None,
               modes_runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w13modes"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
