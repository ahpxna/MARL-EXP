#!/usr/bin/env python3
"""cologne8 route variants (PROTOCOL_CITY_G4_COLOGNE8_20261004): agent trips (_stable_u(seed, id) < 0.5) get vType pkw_agent (ctrl: identical
copy of pkw) or pkw_acc (pkw attributes + carFollowModel ACC).  Output external_assets/RESCO_variants_20261004/<variant>/rou_s<seed>.xml
(excluded from git; CC BY-NC-SA data, never redistributed).  Usage: CITY_g4_make_variants.py VARIANT SEED..."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_env import _stable_u  # noqa: E402

SRC = ROOT / 'external_assets/RESCO/resco_benchmark/environments/cologne8/cologne8.rou.xml'; OUT = ROOT / 'external_assets/RESCO_variants_20261004'
BASE = '<vType id="pkw" vClass="passenger" speedDev="0.1" length="4.3" minGap="1.5"/>'
VT = {'ctrl': ('pkw_agent', '<vType id="pkw_agent" vClass="passenger" speedDev="0.1" length="4.3" minGap="1.5"/>'),
      'acc': ('pkw_acc', '<vType id="pkw_acc" vClass="passenger" speedDev="0.1" length="4.3" minGap="1.5" carFollowModel="ACC"/>')}

if __name__ == '__main__':
    v = sys.argv[1]; tid, decl = VT[v]; txt0 = SRC.read_text(); assert txt0.count(BASE) == 1
    (OUT / v).mkdir(parents=True, exist_ok=True)
    for s in map(int, sys.argv[2:]):
        dst = OUT / v / f'rou_s{s}.xml'
        if dst.exists():
            print('exists, kept', dst); continue
        n = [0, 0]

        def sub(m):
            n[1] += 1
            if _stable_u(s, m.group(1)) < 0.5:
                n[0] += 1; return f'<trip id="{m.group(1)}" type="{tid}"'
            return m.group(0)
        txt = re.sub(r'<trip id="([^"]+)" type="pkw"', sub, txt0.replace(BASE, BASE + '\n\t' + decl, 1))
        dst.write_text(txt); print(f'{dst.name} [{v}]: {n[0]} / {n[1]} trips -> {tid}')
