#!/usr/bin/env python3
"""W6-6 SPIDER-3 evaluator (PROTOCOL_CITY_WAVE6_20261005): CITY_m4s_tsi_eval.py (UNCHANGED, imported with --tk fk:0.5:<table>) with the fleet
service restricted to the DETERMINED cells: a yellow whose next green serves the link, -> forecast-K at q 0.5 (exact onset); a link served by every program phase -> ttg 0 / ttr 999; everything else -> unavailable (no N2K, no forecast).
Counters (sidecar <tag>_tk.json, key provider): valid determined answers fk_direct / always (fk_multi retained as zero for historical comparison), refused (undetermined) queries, exceptions.
Usage: CITY_m4s_tsi3_eval.py --tk3 fkd:<table> [CITY_m4s_tsi_eval args ...]"""
import argparse, json, sys, hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--tk3', required=True); B0, REST3 = pre.parse_known_args()
kind, _, TABLE = B0.tk3.partition(':'); assert kind == 'fkd', B0.tk3
sys.argv = [sys.argv[0], '--tk', f'fk:0.5:{TABLE}'] + REST3
import scripts.CITY_m4s_tsi_eval as T  # noqa: E402
from scripts.CITY_n2k import cur_index  # noqa: E402
T.E4.SRC += '+m4s_tsi3:' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
TRACE = {}; QUERIES = []; REALIZED = []
FKS = T.SPAT; ST = dict(valid=0, fk_direct=0, fk_multi=0, always=0, refused=0, exc=0); STC = {}


def direct_only(tid, link):
    try:
        if tid not in T.INFO.tls:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
        ls = T.CE.ls
        if tid not in STC:
            STC[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = STC[tid]; gs = list(T.INFO.tls[tid]['greens']); serve = [gk for gk, g in enumerate(gs) if st[g][link] in 'Gg']
        if all(p[link] in 'Gg' for p in st):
            ST['always'] += 1; ST['valid'] += 1; return dict(ttg=0.0, ttr=999.0, valid=True, source='always')
        if not serve:
            return dict(ttg=0.0, ttr=0.0, valid=False, source='never-green')
        ph = ls.trafficlight.getPhase(tid); ci, yel = cur_index(gs, ph); nx = (ci + 1) % len(gs)
        if yel and nx in serve and st[ph][link] not in 'Gg':
            s = FKS(tid, link)
            assert s['valid'] and s['ttg'] > 0, s
            ST['fk_direct'] += 1; ST['valid'] += 1
            QUERIES.append((int(ls.simulation.getTime()), tid, link, s['ttg']))
            return s
        # The old fk_multi branch returned valid=False: it is not a determined end time.
        ST['refused'] += 1; return dict(ttg=0.0, ttr=0.0, valid=False, source='undetermined')
    except Exception:
        ST['exc'] += 1; raise


class VerifiedLogger(T.E4.Logger):
    def step(self, t):
        super().step(t)
        for tid in self.ids_f:
            TRACE.setdefault(tid, {})[int(t)] = T.CE.ls.trafficlight.getPhase(tid)

T.E4.Logger = VerifiedLogger
_run = T.E4.run

def run(a, seed, end):
    TRACE.clear(); QUERIES.clear()
    out = _run(a, seed, end)
    from scripts.CITY_w6_spat_trace import check_queries
    c = check_queries(TRACE, STC, QUERIES); c['seed'] = seed; REALIZED.append(c)
    if c['mismatches']:
        raise AssertionError(f'SP3 timing disagrees with realized phase trace: {c}')
    return out

T.E4.run = run
T.SPAT = direct_only; T.STATS['provider'] = ST
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[0]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(T.REST); T.E4.main(a)
    Path(a.out, f'{a.tag}_tk.json').write_text(json.dumps(dict(tk3=B0.tk3, light=a.light, fleet=a.fleet, **T.STATS, realized_checks=REALIZED, queries=int(sum(T.QC.values())))))
