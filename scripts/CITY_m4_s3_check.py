#!/usr/bin/env python3
"""M4 stage 3 checks KM4-3a..e (Amendment M4-A5; exit 1 on failure), on rows in spider/s3/check (seed 100) and spider/s2a."""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
SP = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider'; C = rows(SP / 's3/check'); A = rows(SP / 's2a'); s = 100
Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports')
same = lambda x, y: all(x.get(q) == y.get(q) for q in Q)
out = ['== M4 stage 3 checks (spider seed 100)']
r = {}
r['KM4-3a OFF via the M2 wrapper == 2a OFF_FT'] = same(C['OFFm2_FT'][s], A['OFF_FT'][s])
r['KM4-3b F0 FT naive == labelled == 2a GLOSALS'] = same(C['F0_FT_naive'][s], C['F0_FT_labelled'][s]) and same(C['F0_FT_naive'][s], A['GLOSALS'][s])
r['KM4-3c RLK_sp11 labelled F0 == σ* (eval4_sigma 0.3)'] = same(C['F0_RLK11_labelled'][s], C['S03_RLK11'][s])
sp = json.loads((SP / 's3/check/F0_RLK11_naive_spat.json').read_text()); r[f'KM4-3d naive RLK_sp11 valid SPaT calls > 0 ({sp["valid"]} / {sp["total"]})'] = sp['valid'] > 0
r['KM4-3e RLK patch live: OFF under RLK_sp11 != OFF under FT'] = not same(C['OFFm2_RLK11'][s], A['OFF_FT'][s])
for k, v in r.items():
    out.append(f'  {k}: {"PASS" if v else "FAIL"}')
out.append(f'  rows: OFF FT TL {A["OFF_FT"][s]["timeloss"]:.2f} | OFF RLK11 TL {C["OFFm2_RLK11"][s]["timeloss"]:.2f} | σ* RLK11 TL {C["S03_RLK11"][s]["timeloss"]:.2f}')
ok = all(r.values()); out.append(f'M4 STAGE 3 CHECK: {"PASS" if ok else "FAIL"}'); t = '\n'.join(out) + '\n'; (SP / 's3/check_s3.txt').write_text(t); print(t); sys.exit(0 if ok else 1)
