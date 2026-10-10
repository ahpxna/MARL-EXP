#!/usr/bin/env python3
"""M3-NC checks KN-1..KN-3 (exit 1 on failure) on m3nc_20261004/check (light t4, fleet s213 / s313, traffic 510)."""
import json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m3nc_20261004/check'; C = rows(D); s = 510; out = ['== M3-NC checks (light t4, traffic 510)']
Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports')
wc = json.loads((D / 'WC5_t4_213_m3.json').read_text())['per_seed'][str(s)]; rp = json.loads((D / 'RPC_t4_213_m3p.json').read_text())['per_seed'][str(s)]
cc = json.loads((D / 'WC5c_t4_213_m3.json').read_text()); r = {}
r[f'KN-1 WC5 violations 0 (commits {wc["commits"]}, violations {wc["violations"]}, censored {wc["censored"]})'] = wc['commits'] > 0 and wc['violations'] == 0
r[f'KN-1 RPC violations 0 (commits {rp["commits"]}, end {rp["viol_end"]}, onset {rp["viol_onset"]})'] = rp['commits'] > 0 and rp['viol_end'] == 0 and rp['viol_onset'] == 0
r[f'KN-2 WC5-c uses both sources {cc["source_counts"]}; violations {cc["per_seed"][str(s)]["violations"]}'] = all(v > 0 for v in cc['source_counts'].values()) and cc['per_seed'][str(s)]['violations'] == 0
r['KN-3 R rows identical across fleets (s213 vs s313)'] = all(C['R_t4_213'][s][q] == C['R_t4_313'][s][q] for q in Q)
for k, v in r.items():
    out.append(f'  {k}: {"PASS" if v else "FAIL"}')
ok = all(r.values()); out.append(f'M3-NC CHECK: {"PASS" if ok else "FAIL"}'); t = '\n'.join(out) + '\n'; (D / 'check.txt').write_text(t); print(t); sys.exit(0 if ok else 1)
