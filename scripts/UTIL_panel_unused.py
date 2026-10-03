#!/usr/bin/env python3
"""Exit 0 iff no manifest / config under research/marl_budget lists any traffic seed in [lo, lo + 64) (02/10/2026 15:2x).
Usage: UTIL_panel_unused.py <lo>"""
import json, os, sys
lo = int(sys.argv[1]); want = set(range(lo, lo + 64)); hit = []
for dp, dn, fn in os.walk('research/marl_budget'):
    for f in ('manifest.json', 'config.json'):
        if f in fn:
            try:
                j = json.loads(open(os.path.join(dp, f)).read())
            except Exception:
                continue
            st = [j]
            while st:
                o = st.pop()
                if isinstance(o, dict):
                    for k, v in o.items():
                        if k in ('traffic_seeds', 'seeds', 'panel') and isinstance(v, list) and set(x for x in v if isinstance(x, int)) & want:
                            hit.append(os.path.join(dp, f))
                        else:
                            st.append(v)
                elif isinstance(o, list):
                    st.extend(o)
print(f'panel {lo}: ' + ('UNUSED' if not hit else f'USED in {len(hit)} files, e.g. {hit[:2]}'), flush=True)
sys.exit(0 if not hit else 1)
