import json, sys
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V
from scripts.CITY_w6_validation import rows
from scripts.CITY_w10_report import order
D = ROOT / 'research/city_sim/w10_20261005/dca3'; S = list(range(840, 860)); LT = (4, 5, 6, 7, 8); FL = ('s213', 's313', 's413', 's513'); Rt = rows(D / 'conf')
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')
print('early DCA3 read (matched budget only; DCA3X4 still running)')
for a in ('TSI2', 'DCA3'):
    r = V.paired(Rt, K(a), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
    print(V.line(f'{a} - R', r)); print(f'  {a}: all M3 limits: {ok}; {tl}')
d = V.paired(Rt, K('TSI2'), K('DCA3'), LT, FL, S); print(V.line('TSI2 - DCA3', d)); print('  ordering:', order(d))
for l in LT:
    p = D / 'tune' / f'dca3_t{l}.json'
    if p.exists():
        th = json.loads(p.read_text()); print(f'  t{l} rollouts {th["rollouts"]}/{th["budget"]} horizon {th["horizon_s"]} accepted {th["accepted"]} |theta| {th["param_norm"]:.3f}')
