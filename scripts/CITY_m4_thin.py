#!/usr/bin/env python3
"""M4-A1 demand thinning: write arterial4x4_<i>.rou.xml thinned to keep vehicles with _stable_u(0, id) < p into
external_assets/RESCO_variants_20261004/arterial4x4_p<p>/ (local only).  Usage: CITY_m4_thin.py P FILE_INDEX..."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import xml.etree.ElementTree as ET  # noqa: E402
SRC = ROOT / 'external_assets/RESCO_variants_20261004/arterial4x4'
if __name__ == '__main__':
    p = float(sys.argv[1]); out = ROOT / f'external_assets/RESCO_variants_20261004/arterial4x4_p{p:g}'; out.mkdir(parents=True, exist_ok=True)
    for i in sys.argv[2:]:
        tree = ET.parse(SRC / f'arterial4x4_{i}.rou.xml'); root = tree.getroot(); n0 = n1 = 0
        for v in list(root):
            if v.tag == 'vehicle':
                n0 += 1
                if CE._stable_u(0, v.get('id')) >= p:
                    root.remove(v)
                else:
                    n1 += 1
        tree.write(out / f'arterial4x4_{i}.rou.xml'); print(f'file {i}: kept {n1} / {n0}', flush=True)
