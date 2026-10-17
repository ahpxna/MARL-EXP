#!/usr/bin/env python3
"""W22 wrapper (PROTOCOL_CITY_WAVE22_20261017): fleet-side randomisation of SPaT use.  No file is edited.
  W22_ASSIGN = all | none | veh:<p> | swb:<W>:<p> | nsw:<W>:<p> | nswa:<W>
    all       every fleet vehicle uses the published SPaT (identity check: = the SV arm)
    none      no fleet vehicle uses it (identity check: = the R arm)
    veh:p     fleet vehicle v uses it iff u('veh', seed, v) < p          (per-vehicle Bernoulli(p); the propensity is known)
    swb:W:p   fleet vehicles use the SPaT of light j during window w = floor(t / W) iff u('swb', seed, j, w) < p   (switchback per light)
    nsw:W:p   every fleet vehicle uses SPaT during window w = floor(t / W) iff u('nsw', seed, w) < p (network-wide switchback; W22-B).
              Rows also get w22.nsw: fleet time loss / fuel of trips departing >= W22_NB s (default 120) into a treated vs a control window.
    nswa:W    alternating network switchback (W22-D): window w treated iff (w + b) is even, b = 1[u('nswa', seed) < 0.5]; same w22.nsw.
  The provider is called for every query (it broadcasts to all; a control vehicle ignores the answer and is released to its base driver,
  exactly as under no SPaT), so the provider's own state is the SV arm's.
  W22_PROBE=1: read-only, per (light, window of W22_W s, default 300): number and summed duration of green intervals (a phase whose state has
    'G'/'g' and no 'y'), all greens and greens starting >= W22_B s (default 60) into the window; distinct treated / control fleet vehicles
    seen within the zone on a red link of the light during those greens; the window's switchback assignment.
Rows get w22_assign, w22 (treated / control fleet time loss, fuel and counts), w22_win (probe).
Usage: ... CITY_w20_run.py scripts/CITY_w22_assign.py scripts/<evaluator> <args>"""
import hashlib, os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
ASSIGN = os.environ.get('W22_ASSIGN', 'all'); KIND, _, PAR = ASSIGN.partition(':'); assert KIND in ('all', 'none', 'veh', 'swb', 'nsw', 'nswa'), ASSIGN
if KIND == 'veh':
    P = float(PAR); WS = None
elif KIND in ('swb', 'nsw'):
    WS, P = (float(x) for x in PAR.split(':'))
elif KIND == 'nswa':
    WS, P = float(PAR), 0.5
else:
    P = 1.0 if KIND == 'all' else 0.0; WS = None
PROBE = os.environ.get('W22_PROBE') == '1'; WP = float(os.environ.get('W22_W', WS or 300.0)); BURN = float(os.environ.get('W22_B', 60.0))
ST = dict(seed=0, cur=None, cars=None, q=0, withheld=0)


def U(*k):
    return int.from_bytes(hashlib.sha256('|'.join(map(str, k)).encode()).digest()[:8], 'big') / 2 ** 64


def treated_veh(seed, v):
    return U('veh', seed, v) < P


def treated_swb(seed, tid, w):
    return U('swb', seed, tid, int(w)) < P


def treated_nsw(seed, w):
    if KIND == 'nswa':
        return (int(w) + int(U('nswa', seed) < 0.5)) % 2 == 0
    return U('nsw', seed, int(w)) < P


_gnt = CE.ls.vehicle.getNextTLS


def _getnexttls(v):                                                  # records the vehicle whose SPaT is queried next (V11 calls spat right after)
    ST['cur'] = v; return _gnt(v)


if isinstance(CE.ls.vehicle.__dict__.get('getNextTLS'), staticmethod):
    CE.ls.vehicle.getNextTLS = staticmethod(_getnexttls)
else:
    CE.ls.vehicle.getNextTLS = _getnexttls


def gate(inner):
    def spat(tid, link):
        s = inner(tid, link); ST['q'] += 1
        if KIND == 'all':
            return s
        if KIND == 'none':
            ok = False
        elif KIND == 'veh':
            ok = treated_veh(ST['seed'], ST['cur'])
        elif KIND == 'swb':
            ok = treated_swb(ST['seed'], tid, CE.ls.simulation.getTime() // WS)
        else:
            ok = treated_nsw(ST['seed'], CE.ls.simulation.getTime() // WS)
        if ok:
            return s
        ST['withheld'] += 1; return dict(ttg=0.0, ttr=0.0, valid=False, source='w22-control')
    return spat


W = {}                                                               # (tid, window) -> [n_all, dur_all, n_late, dur_late, set_T, set_C]
CUR = {}                                                             # tid -> [green?, start, set_T, set_C]


def _isgreen(s):
    return ('G' in s or 'g' in s) and 'y' not in s


def _close(tid, t, c):
    if not c[0]:
        return
    w = int(c[1] // WP); r = W.setdefault((tid, w), [0, 0.0, 0, 0.0, set(), set()]); d = t - c[1]
    r[0] += 1; r[1] += d
    if c[1] - w * WP >= BURN:
        r[2] += 1; r[3] += d
    r[4] |= c[2]; r[5] |= c[3]


_rep = E4.run_episode


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    inner = light

    class Probe:
        def step(self, t):
            if inner is not None:
                inner.step(t)
            if not PROBE:
                return
            ls = CE.ls; c = ST['cars']
            for tid in ls.trafficlight.getIDList():
                g = _isgreen(ls.trafficlight.getRedYellowGreenState(tid)); x = CUR.get(tid)
                if x is None or g != x[0]:
                    if x is not None:
                        _close(tid, t, x)
                    CUR[tid] = x = [g, t, set(), set()]
            if c is None:
                return
            for v in list(getattr(c, 'agents', ())):
                try:
                    nt = _gnt(v)
                except Exception:
                    continue
                if not nt or nt[0][2] > CE.ZONE or nt[0][3] not in 'rR':
                    continue
                x = CUR.get(nt[0][0])
                if x is not None and x[0]:                         # veh: split by the vehicle's assignment; otherwise every fleet vehicle in x[2]
                    (x[2] if (KIND != 'veh' or treated_veh(ST['seed'], v)) else x[3]).add(v)
    return _rep(net, rou, seed, Probe(), cars, **kw)


E4.run_episode = run_episode
_rt = E4.read_tripinfo
TI = {}


def read_tripinfo(path, agents=None):
    rows = _rt(path) if agents is None else _rt(path, agents); TI['rows'] = rows      # greens still open at the end are not counted
    if KIND in ('nsw', 'nswa'):
        import sumolib
        TI['dep'] = {x.id: float(x.depart) for x in sumolib.xml.parse(str(path), 'tripinfo')}
    return rows


E4.read_tripinfo = read_tripinfo
_run = E4.run


def run(a, seed, end):
    ST.update(seed=int(seed), cur=None, cars=None, q=0, withheld=0); W.clear(); CUR.clear(); TI.clear()
    lf0 = E4.load_fleet; sp0 = V11.spat                             # rebind at run time (the evaluator sets V11.spat / load_fleet at import)

    def lf(spec, seed_, guard):
        c, p = lf0(spec, seed_, guard); ST['cars'] = c; return c, p
    E4.load_fleet = lf; V11.spat = gate(sp0)
    try:
        out = _run(a, seed, end)
    finally:
        E4.load_fleet = lf0; V11.spat = sp0
    c = ST['cars']; rows = TI.get('rows', [])
    ag = [r for r in rows if c is not None and c.is_agent(r['id'])]
    T = [r for r in ag if treated_veh(seed, r['id'])]; C = [r for r in ag if not treated_veh(seed, r['id'])]
    m = lambda xs, k: float(np.nanmean([x[k] for x in xs])) if xs else float('nan')  # noqa: E731
    out.update(w22_assign=ASSIGN, w22=dict(n_T=len(T), n_C=len(C), tl_T=m(T, 'timeloss'), tl_C=m(C, 'timeloss'), fuel_T=m(T, 'fuel'), fuel_C=m(C, 'fuel'),
                                           queries=ST['q'], withheld=ST['withheld'], p=P, W=WS))
    if KIND in ('nsw', 'nswa'):
        NB = float(os.environ.get('W22_NB', 120.0)); dep = TI.get('dep', {}); g = {0: [], 1: []}
        for r in ag:
            d = dep.get(r['id']); w = int(d // WS) if d is not None else None
            if d is not None and d - w * WS >= NB:
                g[int(treated_nsw(seed, w))].append(r)
        out['w22']['nsw'] = dict(burn=NB, n_T=len(g[1]), n_C=len(g[0]), tl_T=m(g[1], 'timeloss'), tl_C=m(g[0], 'timeloss'), fuel_T=m(g[1], 'fuel'), fuel_C=m(g[0], 'fuel'))
    if PROBE:
        out['w22_win'] = dict(W=WP, burn=BURN, rows=[[tid, w, r[0], r[1], r[2], r[3], len(r[4]), len(r[5]),
                                                      int(treated_swb(seed, tid, w)) if KIND == 'swb' else (int(treated_nsw(seed, w)) if KIND in ('nsw', 'nswa') else -1)]
                                                     for (tid, w), r in sorted(W.items())])
    return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w22:{ASSIGN}:{int(PROBE)}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:12]}"
print(f'W22 assignment wrapper: {ASSIGN}, probe {PROBE} (W {WP}, burn {BURN})', flush=True)
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
