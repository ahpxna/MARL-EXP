#!/usr/bin/env bash
# HYB / HYBQ (PROTOCOL_CITY_N4_SERVICE_GATE Amendment A2): DEV 8 jobs -> report (KH-0: smoke seed 600 runs; hybrid share > 0).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n4_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; TB=research/city_sim/m3_20261004/prep; echo "HYB start $(date)"
$PY -u scripts/CITY_eval_n4.py --n4 0.5:hyb:$TB/prov_rlh0_cl.json:$M/n2_k0.pt --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --seeds 600 --smoke --tag K_hyb --out $D/check > $D/check/khyb.log 2>&1 || { echo "SMOKE FAIL"; tail -5 $D/check/khyb.log; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/K_hyb_n4.json'));print('KH-0 hybrid answers', x['hybrid'], 'of', x['valid']);raise SystemExit(0 if x['hybrid']>0 else 1)" || { echo "KH-0 FAIL"; exit 1; }
J=$D/hyb_jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do F="--light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt"; G="0.5:hyb:$TB/prov_rlh${k}_cl.json:$M/n2_k$k.pt"
  echo "HYB_k${k}_${fl} --n4 $G $F" >> $J; echo "HYBQ_k${k}_${fl} --n4 $G $F --light-obs q:1:0" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/hyb/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n4.py "$@" --seeds 600 601 602 603 604 605 606 607 608 609 610 611 --tag $T --out $D/hyb >> $D/hyb/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_hyb_report.py; echo "HYB done $(date)"
