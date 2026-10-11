#!/usr/bin/env python3
"""M4 stage 3 (complete) evaluator (PROTOCOL_CITY_M4_STAGE3_20261004): CITY_m4s_f1k_eval UNCHANGED (imported; it pre-parses --spat-arm none |
fck:<q>:<table>, patches spider, RLK lights and fleet SPaT) plus a SPaT-source counter (forecast / unavailable / unavailable:ambiguous-end /
never-green) written to <tag>_s3.json next to its own <tag>_f1k.json.  Usage as CITY_m4s_f1k_eval.py."""
import json, sys
from collections import Counter
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m4s_f1k_eval as FE  # noqa: E402
SRC = Counter(); _spat = FE.spat_f


def spat_c(tid, link):
    s = _spat(tid, link); SRC[s.get('source', '?').split(':')[0] if not s.get('source', '').startswith('unavailable') else s['source']] += 1; return s


for m in (FE.V8, FE.ES, FE.GL, FE.LD, FE.V11):
    m.spat = spat_c
if __name__ == '__main__':
    import runpy, argparse
    a = argparse.ArgumentParser(add_help=False); a.add_argument('--tag'); a.add_argument('--out'); k, _ = a.parse_known_args()
    sys.argv = [str(ROOT / 'scripts/CITY_m4s_f1k_eval.py')] + sys.argv[1:]
    # run the evaluator's own __main__ in THIS process (modules already imported, so the patches above stay active)
    src = (ROOT / 'scripts/CITY_m4s_f1k_eval.py').read_text().split("if __name__ == '__main__':", 1)[1]
    exec(compile('if True:' + src, 'CITY_m4s_f1k_eval.__main__', 'exec'), FE.__dict__)
    Path(k.out, f'{k.tag}_s3.json').write_text(json.dumps(dict(sources=dict(SRC))))
