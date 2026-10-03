#!/usr/bin/env python3
"""NYC 16x3 scenarios for the E3 pipeline (02/10/2026 22:4x EDT; PROTOCOL_E3_NYC16X3_20261002.md).

Road network: CoLight's roadnet_16_3.json (Manhattan, 16 x 3 signalised intersections; CityFlow-generator structure: 8 roads per
intersection, 3 lanes per road (left / straight / right), 9 phases; blocks 100 m north-south x 350 m east-west, 11.1 m/s).  It is
a STYLISED grid with Manhattan block spacing, not surveyed geometry.  Demand: the 903 routes of CoLight's
anon_16_3_newyork_real.json (taxi-derived, 2 824 vehicles per hour, flat over the hour) with their empirical frequencies; per
traffic seed, each route gets Poisson arrivals at rate mu(load) * n_route / 3600 (the real route mix, re-drawn arrivals).
Intensity rule (fixed before any run): mu(load) makes the per-intersection crossing rate (vehicles x (route length - 1) /
intersections / s) equal to the E3 grids' at the same load parameter, 8 / load (measured 0.49-0.52 at load 16 and 0.94-1.08 at
load 8 on 3x3 and 4x4); the real level mu = 1 is load REAL_LOAD (descriptive only).
Data files are read, never redistributed (no licence on the CoLight data); their sha256 are asserted.
"""
from __future__ import annotations
import hashlib, json, os
from collections import Counter
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'research/city_sim/data/nyc_colight_16x3'
ROADNET, FLOW = DATA / 'roadnet_16_3.json', DATA / 'anon_16_3_newyork_real.json'
SHA = {'roadnet': '918fe133', 'flow': 'f8cbaaae'}


def _load():
    rb, fb = ROADNET.read_bytes(), FLOW.read_bytes()
    hs = {'roadnet': hashlib.sha256(rb).hexdigest(), 'flow': hashlib.sha256(fb).hexdigest()}
    for k in SHA:
        if not hs[k].startswith(SHA[k]):
            raise SystemExit(f'NYC {k} sha {hs[k]} does not match the recorded {SHA[k]}…')
    return json.loads(rb), json.loads(fb), hs


_ROADNET, _FLOW, HASHES = _load()
ROUTES = Counter(tuple(v['route']) for v in _FLOW)
N_INT = sum(not i['virtual'] for i in _ROADNET['intersections'])
REAL_CROSS = sum(n * (len(r) - 1) for r, n in ROUTES.items()) / N_INT / 3600.0       # crossings per intersection per s, mu = 1
REAL_LOAD = 8.0 / REAL_CROSS
VEHICLE = dict(_FLOW[0]['vehicle'])
assert N_INT == 48


def mu(load: float) -> float:
    return (8.0 / float(load)) / REAL_CROSS


def coords():
    """agent index (the env's order: non-virtual intersections sorted by id string) -> (x, y) grid index from 'intersection_x_y'."""
    ids = sorted(str(i['id']) for i in _ROADNET['intersections'] if not i['virtual'])
    return [tuple(int(v) for v in s.split('_')[1:3]) for s in ids]


def nearest_slots(n_slots=8):
    """models.marl_relay_v3.nearest_slots with the grid index read from the ids (Manhattan distance, ties by agent index)."""
    c = coords(); m = len(c); out = {}
    for k in range(m):
        others = sorted((j for j in range(m) if j != k), key=lambda j: (abs(c[j][0] - c[k][0]) + abs(c[j][1] - c[k][1]), j))
        out[k] = frozenset(others[:n_slots])
    return out


def make_nyc_scenario(out_dir: Path, rows: int, cols: int, traffic_seed: int, horizon_s: int,
                      mean_headway_s: float = 12.0, turn: bool = True) -> dict:
    """Drop-in for envs.external.cityflow_budgeted.make_grid_scenario (rows x cols must be 16 x 3); refuses to overwrite."""
    if rows * cols != 48:
        raise ValueError(f'NYC 16x3 scenario asked for a {rows}x{cols} grid')
    out_dir = Path(out_dir)
    if out_dir.exists():
        raise FileExistsError(f'refusing to overwrite scenario dir {out_dir}')
    out_dir.mkdir(parents=True)
    rng = np.random.default_rng([int(traffic_seed), 0xC17, int(round(1000 * float(mean_headway_s)))]); m_ = mu(mean_headway_s); flows = []
    for route in sorted(ROUTES):
        lam = m_ * ROUTES[route] / 3600.0; t = float(rng.exponential(1.0 / lam))
        while t < horizon_s:
            ts = int(t)
            flows.append({'vehicle': dict(VEHICLE), 'route': list(route), 'interval': 1.0, 'startTime': ts, 'endTime': ts})
            t += float(rng.exponential(1.0 / lam))
    flows.sort(key=lambda f: (f['startTime'], f['route']))
    config = {'interval': 1.0, 'seed': int(traffic_seed), 'dir': str(out_dir) + os.sep, 'roadnetFile': 'roadnet.json',
              'flowFile': 'flow.json', 'rlTrafficLight': True, 'laneChange': False, 'saveReplay': False}
    paths = {}
    for name, obj in (('roadnet.json', _ROADNET), ('flow.json', flows), ('config.json', config)):
        p = out_dir / name; p.write_text(json.dumps(obj), encoding='utf-8')
        paths[name] = {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
    return {'dir': str(out_dir), 'files': paths, 'n_vehicles': len(flows), 'rows': rows, 'cols': cols, 'network': 'nyc16x3',
            'traffic_seed': int(traffic_seed), 'horizon_s': int(horizon_s), 'mean_headway_s': mean_headway_s, 'mu': m_,
            'source_sha256': HASHES, 'turn': bool(turn)}


if __name__ == '__main__':
    print(f'routes {len(ROUTES)}, real crossings per intersection per s {REAL_CROSS:.4f}, real load {REAL_LOAD:.1f}, '
          f'mu(16) {mu(16):.3f}, mu(8) {mu(8):.3f}; slots of agent 0: {sorted(nearest_slots()[0])}; coords[:4] {coords()[:4]}')
