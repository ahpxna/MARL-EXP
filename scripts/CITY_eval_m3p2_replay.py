#!/usr/bin/env python3
"""M3′-D H2 open-loop step (PROTOCOL_CITY_M3P_DIAG_20261004): CITY_eval_m3 (unchanged, --spat-arm none) with the light REPLAYED from the
recorded (F1, M1) phases (--replay-dir; CITY_eval4.Replay) and the fleet's SPaT rebuilt from that run's commitment list (<rec>_m3p2.json):
  --msg withdraw   (M1) t_issue <= t < T_c: the registered RPC message (current-green links ttr = T_c - t; others ttg = T_c - t + YELLOW + OBS)
  --msg keep       (M0) as M1, plus T_c <= t < T_c + YELLOW + OBS: links served by the next green (and not green now) ttg = onset - t
The light schedule is identical in both, so the paired difference isolates the message change.  Check KD-3: withdraw == closed-loop (F1, M1)."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--msg', choices=['withdraw', 'keep'], required=True); pre.add_argument('--commits', required=True)
A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none']
import scripts.CITY_eval_m3 as W  # noqa: E402
sys.argv = _argv
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import YELLOW  # noqa: E402
E4 = W.E4; E4.SRC = f"{E4.SRC}+m3p2replay{A0.msg}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
OBS = W.OBS; COM = {s: v['commits'] for s, v in json.loads(Path(A0.commits).read_text())['per_seed'].items()}
CUR = dict(seed=None, by=None); ST = {}; INFO = E4.NetInfo(E4.Q7.NET_S); N = dict(pending=0, kept=0)
UNAV = dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')


def states(tid):
    if tid not in ST:
        ST[tid] = [p.state for p in CE.ls.trafficlight.getAllProgramLogics(tid)[0].phases]
    return ST[tid]


def msg(tid, link):
    t = CE.ls.simulation.getTime(); st = states(tid); ph = CE.ls.trafficlight.getPhase(tid)
    for t0, Tc in CUR['by'].get(tid, ()):
        if t0 <= t < Tc:
            N['pending'] += 1
            return dict(ttg=0.0, ttr=Tc - t, valid=True, source='commitment') if st[ph][link] in 'Gg' else dict(ttg=Tc - t + YELLOW + OBS, ttr=0.0, valid=True, source='commitment')
        if A0.msg == 'keep' and Tc <= t < Tc + YELLOW + OBS:
            gs = INFO.tls[tid]['greens']; j = ph
            while j not in gs:
                j = (j + 1) % len(st)
            if ph not in gs and st[j][link] in 'Gg':
                N['kept'] += 1; return dict(ttg=Tc + YELLOW + OBS - t, ttr=0.0, valid=True, source='commitment-onset')
            return UNAV
    return UNAV


W.BASE = msg
_run = E4.run


def run(a, seed, end):
    by = {}
    for tid, t0, Tc in COM[str(seed)]:
        by.setdefault(tid, []).append((t0, Tc))
    CUR.update(seed=seed, by=by); return _run(a, seed, end)


E4.run = run
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a); Path(a.out, f'{a.tag}_rep.json').write_text(json.dumps(dict(msg=A0.msg, **N)))
