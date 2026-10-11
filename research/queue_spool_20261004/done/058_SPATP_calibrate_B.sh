# 058 reward-B calibration (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendment R2; rule frozen before the run): FT, traffic 0-7, policies
# always-SUMO / sigma0.3 / random; summary with the frozen degeneracy rule.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/calib
mkdir -p $D
{ for p in always sigma0.3 random; do for s in 0 1 2 3 4 5 6 7; do echo "$p $s"; done; done; } |
  xargs -P 8 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_v8_calibrate_B.py $0 $1 '"$D"'/$0_s$1.json >> '"$D"'/run.log 2>&1 || echo "FAIL $0 $1"'
$PY - <<'PY'
import json, glob
D = 'research/city_sim/spat_pilot_20261004/calib'; out = []
for p in ('always', 'sigma0.3', 'random'):
    R = [json.load(open(f)) for f in sorted(glob.glob(f'{D}/{p}_s*.json'))]
    br = {b: sum(r['branch'][b] for r in R) for b in ('R1', 'R2', 'R3', 'R4')}; n = sum(br.values()) or 1
    cap = sum(r['stats']['capped'] for r in R); emp = sum(r['stats']['b_empty'] for r in R); fmax = max(r['f_q'][-1] for r in R)
    out.append(f"{p}: runs {len(R)}, intervals {n}, shares " + ', '.join(f'{b} {br[b]/n:.3f}' for b in br) + f"; capped {cap}; empty {emp}; f max {fmax:.5f} L/s; "
               f"reward median {sorted(r['r_q'][2] for r in R)[len(R)//2]:.2f}")
    if p == 'random':
        sh = [br[b] / n for b in br]; deg = max(sh) >= 0.99 or sum(x > 0 for x in sh) <= 1
        out.append('DEGENERACY (frozen rule, random policy): ' + ('DEGENERATE -> B not trained this round' if deg else 'not degenerate -> B may be trained'))
r4 = sum(json.load(open(f))['branch']['R4'] for f in glob.glob(f'{D}/*.json'))
out.append('R4 (fuel branch) active in ' + str(r4) + ' intervals over all calibration policies' + (' -> "fuel enters only through the delta threshold" (registered reading)' if r4 == 0 else ''))
open(f'{D}/SUMMARY.txt', 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))
PY
