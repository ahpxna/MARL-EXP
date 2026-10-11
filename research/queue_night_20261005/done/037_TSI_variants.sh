#!/usr/bin/env bash
# TSI variants (PROTOCOL_CITY_TSI_VARIANTS_20261005): KV-0 smoke (counters) -> SELECT 6 jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/tsiv_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; TB=research/city_sim/m3_20261004/prep; echo "TSIV start $(date)"
$PY -u scripts/CITY_eval_n5.py --n4 0.5:hybdnl:$TB/prov_rlh0_cl.json:$M/n2_k0.pt --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --light-obs q:2:0 --seeds 0 --smoke --tag KV0 --out $D/check > $D/check/kv0.log 2>&1 || { echo "SMOKE FAIL"; tail -5 $D/check/kv0.log; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/KV0_n5.json'));print('KV-0 hybrid', x['hybrid'], 'noleft', x['noleft'], 'valid', x['valid']);raise SystemExit(0 if x['noleft']>0 and x['hybrid']>0 else 1)" || { echo "KV-0 FAIL"; exit 1; }
J=$D/jobs.txt; : > $J
for k in 0 1; do for v in HYBD:hybd HYBNL:hybnl HYBDNL:hybdnl; do N=${v%%:*}; G=${v##*:}
  echo "${N}_k$k --n4 0.5:$G:$TB/prov_rlh${k}_cl.json:$M/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_s13_fleet.pt --light-obs q:2:0" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/sel/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n5.py "$@" --seeds 650 651 652 653 654 655 --tag $T --out $D/sel >> $D/sel/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_tsiv_report.py; echo "TSIV done $(date)"
