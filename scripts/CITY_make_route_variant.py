#!/usr/bin/env python3
"""Route variants for B6-AC (PROTOCOL_CITY_B6 §B6-AC, 04/10/2026 wake 9): copy research/city_sim/demand/grid4/rou_s<seed>.xml and give the AGENT
vehicles (exact eval membership: CITY_env._stable_u(seed, vid) < Q7.RHO) a new vType; every other byte is kept.
  ctrl  vType v_agent = copy of v_passenger (identity check: must reproduce always-SUMO exactly)
  acc   vType v_acc, vClass passenger, carFollowModel ACC (SUMO defaults)
Output research/city_sim/demand/grid4_var/<variant>/rou_s<seed>.xml (refuses to overwrite).  Usage: CITY_make_route_variant.py VARIANT SEED..."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_env import _stable_u  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

VT = {'ctrl': ('v_agent', '<vType id="v_agent" vClass="passenger"/>'),
      'acc': ('v_acc', '<vType id="v_acc" vClass="passenger" carFollowModel="ACC"/>')}


def main(variant, seeds):
    tid, decl = VT[variant]; out = ROOT / 'research/city_sim/demand/grid4_var' / variant; out.mkdir(parents=True, exist_ok=True)
    for s in seeds:
        src = Path(Q7.ROU.format(s)); dst = out / f'rou_s{s}.xml'
        if dst.exists():
            print('exists, kept', dst); continue
        txt = src.read_text(); n = [0, 0]
        anchor = '<vType id="v_passenger" vClass="passenger"/>'
        assert txt.count(anchor) == 1, 'unexpected vType block'
        txt = txt.replace(anchor, anchor + '\n    ' + decl, 1)

        def sub(m):
            vid = m.group(1); n[1] += 1
            if _stable_u(s, vid) < Q7.RHO:
                n[0] += 1; return f'<vehicle id="{vid}" type="{tid}"'
            return m.group(0)
        txt = re.sub(r'<vehicle id="([^"]+)" type="v_passenger"', sub, txt)
        dst.write_text(txt); print(f'{dst}: {n[0]} / {n[1]} vehicles -> {tid}')


if __name__ == '__main__':
    main(sys.argv[1], [int(x) for x in sys.argv[2:]])
