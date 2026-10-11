#!/usr/bin/env python3
"""W18 runner (PROTOCOL_CITY_WAVE18_20261008): the W17 field-matched world (CITY_w17_world, imported: every car the W17-0 joint IDM, KW17-0)
plus the fleet-design switches (no file is edited):
  W18_DEMAND=p4   Q7.ROU -> research/city_sim/demand/grid4_p4/rou_s{}.xml (half demand, randomTrips period 4.0 s); its route files are mapped
                  to field-matched copies in demand/grid4_p4_w17 (the W17 mapping generalised to grid4_* demand directories).
  W18_RHO=<r>     fleet share Q7.RHO (default 0.5); applies to every arm of the run (OFF uses the same membership).
  W18_FLEET=Q     the fleet trainer builds CITY_fleet_w18.CarPPOLQ instead of CarPPOL (D2 training).
  fleet specs     PLQ:<ckpt> (CarPPOLQ, deterministic), GENTLE:<accel> (always-SUMO fleet with setAccel at departure).
Usage: CITY_w18_world.py scripts/<x>.py <args>"""
import hashlib, os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w17_world as W  # noqa: E402  (W17 world patches)
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import scripts.CITY_fleet_w18 as F18  # noqa: E402
import torch  # noqa: E402
DEM = os.environ.get('W18_DEMAND', ''); RHO = os.environ.get('W18_RHO'); FLT = os.environ.get('W18_FLEET', '')
if DEM:
    Q7.ROU = str(ROOT / f'research/city_sim/demand/grid4_{DEM}/rou_s{{}}.xml')
if RHO:
    Q7.RHO = float(RHO); E4.Q7.RHO = float(RHO)
_idm = W.idm_rou


def idm_rou(rou):
    p = Path(rou)
    if p.parent.name.startswith('grid4_') and not p.parent.name.endswith('_w17') and p.parent.parent.name == 'demand':
        q = p.parent.parent / f'{p.parent.name}_w17' / p.name
        if not q.exists():
            q.parent.mkdir(parents=True, exist_ok=True); src = p.read_text(); tag = '<vType id="v_passenger" vClass="passenger"/>'
            assert src.count(tag) == 1, f'KW18-R FAIL: vType line not found once in {p}'
            tmp = q.with_suffix(f'.tmp{os.getpid()}'); tmp.write_text(src.replace(tag, f'<vType id="v_passenger" vClass="passenger" {W.IDMV}/>')); os.replace(tmp, q)
        return str(q)
    return _idm(rou)


W.idm_rou = idm_rou
if FLT == 'Q':
    V11.CarPPOL = F18.CarPPOLQ
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    if spec.startswith('PLQ:'):
        p = Path(spec[4:]); d = torch.load(p, weights_only=False); net = d['net']; net.eval()
        return F18.CarPPOLQ(net, E4.Q7.RHO, seed, deterministic=True, record=False), p
    if spec.startswith('GENTLE:'):
        acc = float(spec[7:]); c, p = _lf('L-ACT:0', seed, 'always'); orig = c.step

        def step(t, c=c, orig=orig, acc=acc):
            orig(t)
            for v in CE.ls.simulation.getDepartedIDList():
                if c.is_agent(v):
                    CE.ls.vehicle.setAccel(v, acc)
        c.step = step; return c, p
    return _lf(spec, seed, guard)


E4.load_fleet = load_fleet
E4.SRC = f"{E4.SRC}+w18:{DEM or 'peak'}:{RHO or '0.5'}:{FLT or '-'}:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()[:12]}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
