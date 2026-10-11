#!/usr/bin/env python3
"""M4 stage 3 checks KS3-2, KS3-3, KS3-5 (exit 1 on failure) on spider/s3b/check (seed 100, sp11, locked q)."""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider/s3b/check'; C = rows(D); s = 100
Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports'); same = lambda a, b: all(C[a][s][q] == C[b][s][q] for q in Q)
side = json.loads((D / 'KS_glosal_f1k.json').read_text()); src = json.loads((D / 'KS_glosal_s3.json').read_text())['sources']
r = {'KS3-2 RULE0 + forecast == F0 (GLOSAL) + forecast': same('KS_rule0', 'KS_glosal'),
     'KS3-3 F1k trainer with 0 episodes == F0 + forecast': same('KS_zero', 'KS_glosal'),
     f'KS3-5 valid SPaT calls > 0 ({side["valid"]} / {side["total"]}; sources {src})': side['valid'] > 0}
out = ['== M4 stage 3 checks (seed 100, sp11)'] + [f'  {k}: {"PASS" if v else "FAIL"}' for k, v in r.items()]
ok = all(r.values()); out.append(f'M4 STAGE 3 CHECK: {"PASS" if ok else "FAIL"}'); t = '\n'.join(out) + '\n'; (D / 'check_s3full.txt').write_text(t); print(t); sys.exit(0 if ok else 1)
