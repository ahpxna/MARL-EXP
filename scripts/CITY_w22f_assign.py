#!/usr/bin/env python3
"""W22-F wrapper (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-F): CITY_w22_assign.py (kept unchanged for the earlier waves) plus a same-day
two-share kind, an area kind and two read-only probes.  No file is edited.
  W22_ASSIGN = all | none | veh:<p> | swb:<W>:<p> | nsw:<W>:<p> | nswa:<W> | vt:<switch> | area:<K>:<m>
    all / none / veh / swb / nsw / nswa   exactly as CITY_w22_assign.py
    vt:S      same-day two shares (F1): a fleet vehicle departing before S s uses SPaT iff u('veh', seed, v) < pa, later iff < pb, with
              (pa, pb) = (0.3, 0.7) on even days and (0.7, 0.3) on odd days.  Rows get w22.vt: per departure window [900, 1800) and
              [2700, 3600) the treated / control fleet counts and time-loss sums (W22_VTW = "900,1800,2700,3600").
    area:K:m  area randomisation (F4): the signals are split into K strips of equal count along the principal axis of their stop-line
              positions; the m strips with the smallest u('area', seed, strip) are treated; a fleet vehicle uses the SPaT of signal j iff j's
              strip is treated.  Rows get w22.area (strip of every signal, treated strips, axis coordinate of every signal).
  The provider is called for every query; a control vehicle ignores the answer and is released to its base driver.
  W22_PROBE=1  as CITY_w22_assign.py (greens per signal-window).
  W22_PROBE=2  (F3; small networks) greens per (signal, window, 60-s offset bin); every approach passage (vehicle x signal j, on j's controlled
               incoming lanes) with halted (speed < 0.1 at any second), j's assignment at entry, the upstream signal's assignment at entry
               (-1 if the edge does not start at a signal) and the class (agent / human); vehicles in the network per window.
  W22_PROBE=3  (F4) per signal: time-loss seconds (1 - v / v_allowed) and passages on its controlled incoming lanes, for agents (split
               treated / control under veh) and humans.
Usage: ... CITY_w20_run.py scripts/CITY_w22f_assign.py scripts/<evaluator> <args>"""
import hashlib, os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
ASSIGN = os.environ.get('W22_ASSIGN', 'all'); KIND, _, PAR = ASSIGN.partition(':')
assert KIND in ('all', 'none', 'veh', 'swb', 'nsw', 'nswa', 'vt', 'area'), ASSIGN
AK = AM = None; SW = None
if KIND == 'veh':
    P = float(PAR); WS = None
elif KIND in ('swb', 'nsw'):
    WS, P = (float(x) for x in PAR.split(':'))
elif KIND == 'nswa':
    WS, P = float(PAR), 0.5
elif KIND == 'vt':
    SW = float(PAR); P = 0.5; WS = None
elif KIND == 'area':
    AK, AM = (int(x) for x in PAR.split(':')); P = AM / AK; WS = None
else:
    P = 1.0 if KIND == 'all' else 0.0; WS = None
PROBE = os.environ.get('W22_PROBE', '0'); WP = float(os.environ.get('W22_W', WS or 300.0)); BURN = float(os.environ.get('W22_B', 60.0))
VTW = [float(x) for x in os.environ.get('W22_VTW', '900,1800,2700,3600').split(',')]
ST = dict(seed=0, cur=None, cars=None, q=0, withheld=0)
DEP = {}; AREA = {}


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


def vt_shares(seed):
    return (0.3, 0.7) if int(seed) % 2 == 0 else (0.7, 0.3)


def treated_vt(seed, v, dep):
    pa, pb = vt_shares(seed); return U('veh', seed, v) < (pa if dep < SW else pb)


def _dep(v):
    if v not in DEP:
        try:
            DEP[v] = float(CE.ls.vehicle.getDeparture(v))
        except Exception:
            DEP[v] = float(CE.ls.simulation.getTime())
    return DEP[v]


def _area_setup(seed):
    ls = CE.ls; ids = sorted(ls.trafficlight.getIDList()); pos = []
    for tid in ids:
        pts = [ls.lane.getShape(l)[-1] for l in dict.fromkeys(ls.trafficlight.getControlledLanes(tid))]
        pos.append(np.mean(pts, axis=0) if pts else np.zeros(2))
    X = np.array(pos); Xc = X - X.mean(axis=0); ax = np.linalg.svd(Xc, full_matrices=False)[2][0]; s = Xc @ ax
    order = np.argsort(s, kind='stable'); strip = {}
    for r, i in enumerate(order):
        strip[ids[i]] = int(r * AK // len(ids))
    tr = sorted(range(AK), key=lambda k: U('area', seed, k))[:AM]
    AREA.update(strip=strip, treated=sorted(tr), coord={ids[i]: float(s[i]) for i in range(len(ids))}, setup=True)


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
        elif KIND == 'vt':
            ok = treated_vt(ST['seed'], ST['cur'], _dep(ST['cur']))
        elif KIND == 'area':
            if not AREA.get('setup'):
                _area_setup(ST['seed'])
            ok = AREA['strip'].get(tid, -1) in AREA['treated']
        else:
            ok = treated_nsw(ST['seed'], CE.ls.simulation.getTime() // WS)
        if ok:
            return s
        ST['withheld'] += 1; return dict(ttg=0.0, ttr=0.0, valid=False, source='w22-control')
    return spat


def z_signal(seed, tid, t):
    """the signal's assignment at time t for the probes: 1 treated, 0 control (all / none: 1 / 0; veh / vt: -1, vehicle-level)."""
    if KIND == 'all':
        return 1
    if KIND == 'none':
        return 0
    if KIND == 'swb':
        return int(treated_swb(seed, tid, t // WS))
    if KIND in ('nsw', 'nswa'):
        return int(treated_nsw(seed, t // WS))
    if KIND == 'area':
        return int(AREA['strip'].get(tid, -1) in AREA['treated']) if AREA.get('setup') else -1
    return -1


W = {}; CUR = {}; WB = {}                                            # probe 1 windows; current green per signal; probe 2 offset bins
P2 = dict(pas={}, veh={}, open={}); P3 = {}; LANES = {}; VMAXL = {}; FROMJ = {}


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
    if PROBE == '2':
        b = WB.setdefault((tid, w, int((c[1] - w * WP) // 60)), [0, 0.0]); b[0] += 1; b[1] += d


def _lanes(tid):
    if tid not in LANES:
        LANES[tid] = list(dict.fromkeys(CE.ls.trafficlight.getControlledLanes(tid)))
    return LANES[tid]


def _fromj(lane):
    if lane not in FROMJ:
        try:
            FROMJ[lane] = CE.ls.edge.getFromJunction(CE.ls.lane.getEdgeID(lane))
        except Exception:
            FROMJ[lane] = None
    return FROMJ[lane]


def _p2_finish(v):
    o = P2['open'].pop(v, None)
    if o is not None:
        k = o[0]; r = P2['pas'].setdefault(k, [0, 0]); r[0] += 1; r[1] += int(o[1])


_rep = E4.run_episode


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    inner = light

    class Probe:
        def step(self, t):
            if inner is not None:
                inner.step(t)
            if PROBE == '0':
                return
            ls = CE.ls; c = ST['cars']; tls = ls.trafficlight.getIDList()
            if PROBE in ('1', '2'):
                for tid in tls:
                    g = _isgreen(ls.trafficlight.getRedYellowGreenState(tid)); x = CUR.get(tid)
                    if x is None or g != x[0]:
                        if x is not None:
                            _close(tid, t, x)
                        CUR[tid] = x = [g, t, set(), set()]
                if PROBE == '1' and c is not None:
                    for v in list(getattr(c, 'agents', ())):
                        try:
                            nt = _gnt(v)
                        except Exception:
                            continue
                        if not nt or nt[0][2] > CE.ZONE or nt[0][3] not in 'rR':
                            continue
                        x = CUR.get(nt[0][0])
                        if x is not None and x[0]:
                            (x[2] if (KIND != 'veh' or treated_veh(ST['seed'], v)) else x[3]).add(v)
            if PROBE == '2':
                w = int(t // WP); vv = P2['veh'].setdefault(w, [0, 0]); vv[0] += ls.vehicle.getIDCount(); vv[1] += 1
                tset = set(tls); seen = set()
                for tid in tls:
                    for lane in _lanes(tid):
                        for v in ls.lane.getLastStepVehicleIDs(lane):
                            seen.add(v); o = P2['open'].get(v)
                            if o is None or o[2] != tid:
                                if o is not None:
                                    _p2_finish(v)
                                i = _fromj(lane); zi = z_signal(ST['seed'], i, t) if (i in tset) else -1
                                cls = 'a' if (c is not None and c.is_agent(v)) else 'h'
                                P2['open'][v] = o = [(cls, z_signal(ST['seed'], tid, t), zi), False, tid]
                            if ls.vehicle.getSpeed(v) < 0.1:
                                o[1] = True
                for v in [v for v in P2['open'] if v not in seen]:
                    _p2_finish(v)
            if PROBE == '3':
                for tid in tls:
                    r = P3.get(tid)
                    if r is None:
                        r = P3[tid] = [0.0, 0, 0.0, 0, 0.0, 0, 0.0, 0, {}]          # agent tl, pass; human tl, pass; agentT tl, pass; agentC tl, pass; last
                    for lane in _lanes(tid):
                        for v in ls.lane.getLastStepVehicleIDs(lane):
                            va = ls.vehicle.getAllowedSpeed(v); x = max(0.0, 1.0 - ls.vehicle.getSpeed(v) / va) if va > 0 else 0.0
                            ag = c is not None and c.is_agent(v); new = r[8].get(v) != t - 1; r[8][v] = t
                            if ag:
                                r[0] += x; r[1] += new
                                if KIND == 'veh':
                                    if treated_veh(ST['seed'], v):
                                        r[4] += x; r[5] += new
                                    else:
                                        r[6] += x; r[7] += new
                            else:
                                r[2] += x; r[3] += new
    return _rep(net, rou, seed, Probe(), cars, **kw)


E4.run_episode = run_episode
_rt = E4.read_tripinfo
TI = {}


def read_tripinfo(path, agents=None):
    rows = _rt(path) if agents is None else _rt(path, agents); TI['rows'] = rows      # greens still open at the end are not counted
    if KIND in ('nsw', 'nswa', 'vt'):
        import sumolib
        TI['dep'] = {x.id: float(x.depart) for x in sumolib.xml.parse(str(path), 'tripinfo')}
    return rows


E4.read_tripinfo = read_tripinfo
_run = E4.run


def run(a, seed, end):
    ST.update(seed=int(seed), cur=None, cars=None, q=0, withheld=0); W.clear(); CUR.clear(); TI.clear(); WB.clear(); DEP.clear(); AREA.clear()
    P2.update(pas={}, veh={}, open={}); P3.clear(); LANES.clear(); FROMJ.clear()
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
    if KIND == 'vt':
        dep = TI.get('dep', {}); pa, pb = vt_shares(seed); acc = {'a': [0, 0.0, 0, 0.0], 'b': [0, 0.0, 0, 0.0]}
        for r in ag:
            d = dep.get(r['id'])
            if d is None:
                continue
            k = 'a' if VTW[0] <= d < VTW[1] else ('b' if VTW[2] <= d < VTW[3] else None)
            if k is None:
                continue
            j = 0 if treated_vt(seed, r['id'], d) else 2; acc[k][j] += 1; acc[k][j + 1] += r['timeloss']
        out['w22']['vt'] = dict(switch=SW, pa=pa, pb=pb, windows=VTW, a=acc['a'], b=acc['b'])
    if KIND == 'area':
        out['w22']['area'] = dict(K=AK, m=AM, treated=AREA.get('treated'), strip=AREA.get('strip'), coord=AREA.get('coord'))
    if PROBE == '1':
        out['w22_win'] = dict(W=WP, burn=BURN, rows=[[tid, w, r[0], r[1], r[2], r[3], len(r[4]), len(r[5]),
                                                      int(treated_swb(seed, tid, w)) if KIND == 'swb' else (int(treated_nsw(seed, w)) if KIND in ('nsw', 'nswa') else -1)]
                                                     for (tid, w), r in sorted(W.items())])
    if PROBE == '2':
        for v in list(P2['open']):
            _p2_finish(v)
        out['w22_win'] = dict(W=WP, burn=BURN, rows=[[tid, w, r[0], r[1], r[2], r[3], 0, 0, z_signal(seed, tid, w * WP)] for (tid, w), r in sorted(W.items())])
        out['w22_p2'] = dict(bins=[[tid, w, b, x[0], x[1], z_signal(seed, tid, w * WP)] for (tid, w, b), x in sorted(WB.items())],
                             passages=[[k[0], k[1], k[2], x[0], x[1]] for k, x in sorted(P2['pas'].items())],
                             vehicles=[[w, x[0], x[1]] for w, x in sorted(P2['veh'].items())])
    if PROBE == '3':
        out['w22_p3'] = {tid: r[:8] for tid, r in sorted(P3.items())}
    return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w22f:{ASSIGN}:{PROBE}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:12]}"
print(f'W22-F assignment wrapper: {ASSIGN}, probe {PROBE} (W {WP}, burn {BURN})', flush=True)
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
