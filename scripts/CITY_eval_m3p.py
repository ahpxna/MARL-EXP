#!/usr/bin/env python3
"""M3′ evaluation wrapper (PROTOCOL_CITY_M3P_PRECISION_COMMIT_20261004): CITY_eval_m3 (imported with --spat-arm none; unchanged) plus the light
spec RPC:<k>:<trigger>[:<rate json>] (trigger receiver | eta | random | measure | none) whose fleet SPaT is the light's own commitment-or-
unavailable message.  Sidecar <tag>_m3p.json per seed: commitments, decisions, overridden decisions, violations of the promised green END
(observed change out of the green at T_c) and green ONSET (observed change into a serving phase at T_c + YELLOW + OBS), censored,
eligible-tick counts (measure mode), commanded vehicle-seconds."""
import argparse, hashlib, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none']
import scripts.CITY_eval_m3 as W  # noqa: E402
sys.argv = _argv
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_m3p_rpc as RPC  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import torch  # noqa: E402
E4 = W.E4; E4.SRC = f"{E4.SRC}+m3p:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
SIDE = {}
_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RPC:'):
        parts = spec.split(':'); k, trig = int(parts[1]), parts[2]; rate = json.loads(Path(':'.join(parts[3:])).read_text())[str(k)] if len(parts) > 3 else None
        _n, ck, _m = X2.light_spec(f'RL-H:{k}'); q = torch.load(ck, weights_only=False)['net']; q.eval()
        L = RPC.LightRPC(info, q, trig, rate, seed=k); W.CUR.update(light=L); return W.Q7.NET_S, L, [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light


def spat_rpc(tid, link):
    L = W.CUR.get('light'); s = L.spat(tid, link) if isinstance(L, RPC.LightRPC) else dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')
    W.LOG['total'] += 1; W.LOG['valid'] += bool(s['valid']); return s


for m in (W.V8, W.ES, W.GL, W.LD, W.V11):
    m.spat = spat_rpc
_run = W.run


def run(a, seed, end):
    out = _run(a, seed, end); L = W.CUR.get('light'); S = {}
    if isinstance(L, RPC.LightRPC):
        ch = W.realise(); t_last = W.PHASES[-1][0] if W.PHASES else 0.0; ve = vo = cens = 0
        for tid, t0, Tc in L.log['commits']:
            ends = [tt for tt, a_, b_ in ch.get(tid, []) if tt >= t0]
            if not ends and Tc > t_last:
                cens += 1; continue
            if not ends or abs(ends[0] - Tc) > 1e-9:
                ve += 1
            on = next((tt for tt, a_, b_ in ch.get(tid, []) if tt > Tc and b_ in L.info.tls[tid]['greens']), None)
            if on is None and Tc + RPC.YELLOW + RPC.OBS > t_last:
                continue
            if on is None or abs(on - (Tc + RPC.YELLOW + RPC.OBS)) > 1e-9:
                vo += 1
        S = dict(commits=len(L.log['commits']), decisions=L.log['decisions'], overridden=L.log['overridden'], viol_end=ve, viol_onset=vo, censored=cens,
                 ticks_total=L.log['ticks_total'], ticks_eligible=L.log['ticks_eligible'], per_light=L.log['per_light'])
    c = W.CUR.get('cars'); S['commanded'] = int(c.decisions if isinstance(c, V11.CarPPOL) else getattr(c, 'fired', 0)) if c is not None else 0
    SIDE[str(seed)] = S; return out


E4.run = run
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(); E4.main(a); Path(a.out, f'{a.tag}_m3p.json').write_text(json.dumps(dict(light=a.light, fleet=a.fleet, per_seed=SIDE)))
