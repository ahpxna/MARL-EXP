#!/usr/bin/env python3
"""N8 grid4 evaluator (PROTOCOL_CITY_N8_CDC_20261005): CITY_eval_f1 (UNCHANGED, imported with --spat-arm none) plus a committed-duration
light controller (a predictable split controller, the structural baseline of HONEST-CAV / DHCP type; not a new method):
  --light CDC:th0,th1,th2,th3   at the onset of every green phase of a light (static program, net NET_S), commit its duration
                                d = clip(th0 + th1*n_cur + th2*n_oth + th3*h_oth, DMIN, DMAX) once via setPhaseDuration; yellow phases follow
                                the program.  n = vehicles, h = halting, on the lanes served by the starting (cur) / the other (oth) green.
  --spat program | none         fleet SPaT = CITY_spat_feature.spat (static program + committed remaining time: exact by construction) or
                                unavailable (fleet -> sigma*).
KN8-1 (SPaT exactness, every run): a 1-in-10 sample of the fleet's queries is compared with the realized link-state change (per-second
phase log of every light); the sidecar <tag>_n8.json holds the counts.  Other lights (--light FT / RL-H:k) pass through unchanged."""
import argparse, hashlib, json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat', default='program', choices=('program', 'none')); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_eval_f1 as EF  # noqa: E402
sys.argv = _argv
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_feature as SF  # noqa: E402
E4 = EF.E4; sha = lambda b: hashlib.sha256(b).hexdigest(); E4.SRC = f"{E4.SRC}+n8:{sha(Path(__file__).read_bytes())}"
DMIN, DMAX = 5.0, 60.0; LOG = dict(q=[], ph={}, n=0); CHK = {}


class CDC:
    """the next green's duration is decided (and committed) at the onset of the yellow that precedes it, from the counts at that second;
    at the green onset it is applied with setPhaseDuration.  The very first green (t = 0) is decided at its onset."""
    def __init__(self, info, th):
        self.info = info; self.th = np.array(th, float); self.last = {}; self.ids = list(info.tls); self.durs = []; self.plan = {}

    def rule(self, tid, g):
        ls = CE.ls; d = self.info.tls[tid]; cur = d['greens'].index(g); oth = 1 - cur
        h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve'][:2]]
        n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve'][:2]]
        return float(round(np.clip(self.th[0] + self.th[1] * n[cur] + self.th[2] * n[oth] + self.th[3] * h[oth], DMIN, DMAX)))

    def step(self, t):
        ls = CE.ls
        if 'states' not in CHK:
            CHK['states'] = {tid: [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases] for tid in self.ids}
        for tid in self.ids:
            d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); n_ph = d['n_phases']
            if self.last.get(tid) != ph:
                if ph in d['greens']:
                    dur = self.plan.pop(tid, None)
                    if dur is None:
                        dur = self.rule(tid, ph)
                    ls.trafficlight.setPhaseDuration(tid, max(1.0, dur - ls.trafficlight.getSpentDuration(tid))); self.durs.append(dur)
                else:                                              # a yellow: commit the duration of the next green now
                    nxt = (ph + 1) % n_ph
                    if nxt in d['greens']:
                        self.plan[tid] = self.rule(tid, nxt)
            self.last[tid] = ph
            LOG['ph'].setdefault(tid, {})[int(t)] = ph


def spat_cdc(tid, link):
    """CITY_spat_feature.spat, with every future GREEN phase's duration taken from the committed plan; a future green without a committed
    duration makes the answer unavailable (yellows are static, hence exact)."""
    L = CHK.get('light'); ls = CE.ls; t = ls.simulation.getTime()
    if L is None or tid not in L.info.tls:
        return SF.spat(tid, link)
    ph = ls.trafficlight.getAllProgramLogics(tid)[0].phases; k = ls.trafficlight.getPhase(tid); n = len(ph); rem = ls.trafficlight.getNextSwitch(tid) - t
    G = L.info.tls[tid]['greens']; green = lambda j: ph[j].state[link] in 'Gg'

    def dur(j):
        if j not in G:
            return ph[j].duration
        return L.plan[tid] if (tid in L.plan and j == (k + 1) % n) else None
    if green(k):
        acc, j = rem, (k + 1) % n
        for _ in range(n - 1):
            if not green(j):
                return dict(ttg=0.0, ttr=float(acc) + SF.OBS, valid=True, source='cdc')
            dj = dur(j)
            if dj is None:
                return dict(ttg=0.0, ttr=0.0, valid=False, source='cdc-uncommitted')
            acc += dj; j = (j + 1) % n
        return dict(ttg=0.0, ttr=SF.ALWAYS, valid=True, source='always-green')
    acc, j = rem, (k + 1) % n
    for _ in range(n):
        if green(j):
            return dict(ttg=float(acc) + SF.OBS, ttr=0.0, valid=True, source='cdc')
        dj = dur(j)
        if dj is None:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='cdc-uncommitted')
        acc += dj; j = (j + 1) % n
    return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('CDC:'):
        L = CDC(info, [float(x) for x in spec[4:].split(',')]); CHK['light'] = L; return E4.Q7.NET_S, L, [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light


def spat_n8(tid, link):
    if A0.spat == 'none':
        return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
    s = spat_cdc(tid, link) if 'light' in CHK else SF.spat(tid, link); LOG['n'] += 1
    if s['valid'] and LOG['n'] % 10 == 0:
        LOG['q'].append((CE.ls.simulation.getTime(), tid, link, s['ttg'], s['ttr']))
    return s


EF.BASE = spat_n8
_run = E4.run


def check(seed):
    """realized time to the queried link's state change, from the per-second phase log {t: phase} of every CDC light."""
    bad = 0; n = 0; cens = 0
    for t, tid, link, ttg, ttr in LOG['q']:
        P = LOG['ph'].get(tid); st = CHK['states'][tid]; i0 = int(t); want_green = ttg > 0; target = ttg if want_green else ttr; hit = None
        if P is None:
            continue
        for i in range(i0 + 1, max(P) + 1):
            if i not in P:
                continue
            g = st[P[i]][link] in 'Gg'
            if (want_green and g) or ((not want_green) and not g):
                hit = i - i0; break
        if hit is None:
            cens += 1; continue
        n += 1; bad += abs(hit - target) > 0.5
    return dict(seed=seed, checked=n, mismatches=bad, censored=cens)


def run(a, seed, end):
    LOG['q'].clear(); LOG['ph'].clear(); LOG['n'] = 0; CHK.pop('states', None)
    out = _run(a, seed, end)
    if A0.spat == 'program' and LOG['q'] and LOG['ph']:
        CHK.setdefault('runs', []).append(check(seed))
    if 'light' in CHK:
        CHK.setdefault('durs', []).extend(CHK['light'].durs); CHK['light'].durs = []
    return out


E4.run = run
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    d = CHK.get('durs', []); runs = CHK.get('runs', [])
    Path(a.out, f'{a.tag}_n8.json').write_text(json.dumps(dict(spat=A0.spat, light=a.light, kn8_1=runs, mism=sum(r['mismatches'] for r in runs), checked=sum(r['checked'] for r in runs),
                                                          dur_mean=float(np.mean(d)) if d else None, dur_p90=float(np.percentile(d, 90)) if d else None, n_greens=len(d))))
