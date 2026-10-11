#!/usr/bin/env bash
# M3-H3 (PROTOCOL_CITY_M3_H3_OPPORTUNITY_20261004): smoke + KH-1 -> 8 scans -> sampling -> 96 situations x 7 branches -> analysis.  At most 4 processes.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/m3h3_20261004; P=research/city_sim/spat_pilot_20261004/fleets_v11
export XPLAY_TMP=$PWD/$D/tmp; mkdir -p $D/smoke $D/scan $D/br $D/tmp; FL0=$P/L11_s13_fleet.pt; FL1=$P/L11_s113_fleet.pt
echo "H3 start $(date)"
$PY -u scripts/CITY_m3_h3.py --light ONE:0:scan --fleet PL:$FL0 --seeds 0 --smoke --tag smoke_scan --out $D/smoke || exit 1
T=$($PY -c "import json; sc=json.load(open('$D/smoke/smoke_scan_h3.json'))['per_seed']['0']['scan']; x=[s for s in sc if s[0]>=300] or sc; print(int(x[0][0]), x[0][1])") || exit 1
set -- $T; for o in I0 PLACEBO H10; do $PY -u scripts/CITY_m3_h3.py --light ONE:0:$o:$1:$2 --fleet PL:$FL0 --seeds 0 --smoke --tag smoke_$o --out $D/smoke || exit 1; done
$PY -c "
import numpy as np
a=np.load('$D/smoke/smoke_I0_veh_s0.npz'); b=np.load('$D/smoke/smoke_PLACEBO_veh_s0.npz'); c=np.load('$D/smoke/smoke_H10_veh_s0.npz')
same=(a['fuel']==b['fuel']).all() and (a['tl']==b['tl']).all(); print('smoke KH-1 PLACEBO == I0:', same, '| H10 affected vehicles:', int(((a['fuel']!=c['fuel'])|(a['tl']!=c['tl'])).sum()))
raise SystemExit(0 if same else 1)" || { echo "smoke KH-1 FAIL"; exit 1; }
for k in 0 1; do F=$FL0; [ $k = 1 ] && F=$FL1; for s in 0 1 2 3; do echo "$k $s $F"; done; done | xargs -P 4 -L 1 bash -c '[ -f '"$D"'/scan/scan_k$0_s$1.json ] || nice -n 5 '"$PY"' -u scripts/CITY_m3_h3.py --light ONE:$0:scan --fleet PL:$2 --seeds $1 --tag scan_k$0_s$1 --out '"$D"'/scan >> '"$D"'/scan/run.log 2>&1 || echo "FAIL scan $0 $1"'
$PY scripts/CITY_m3_h3_sample.py || exit 1
$PY -c "
import json
S=json.load(open('$D/situations.json')); P='$P'
with open('$D/branches.txt','w') as f:
    for i,s in enumerate(S):
        fl=P+'/L11_s13_fleet.pt' if s['k']==0 else P+'/L11_s113_fleet.pt'
        for o in ('I0','PLACEBO','Z','H5','H10','H15','P'):
            f.write(f\"S{i:03d}_{o} ONE:{s['k']}:{o}:{s['t']}:{s['light']} PL:{fl} {s['seed']}\n\")
print('branches', sum(1 for _ in open('$D/branches.txt')))"
xargs -P 4 -L 1 bash -c '[ -f '"$D"'/br/$0.json ] || nice -n 5 '"$PY"' -u scripts/CITY_m3_h3.py --light $1 --fleet $2 --seeds $3 --tag $0 --out '"$D"'/br >> '"$D"'/br/run.log 2>&1 || echo "FAIL $0"' < $D/branches.txt
echo "branches done $(date)"; $PY scripts/CITY_m3_h3_analyze.py; echo "H3 done $(date)"
