#!/usr/bin/env bash
# GQ (PROTOCOL_CITY_N4_SERVICE_GATE Amendment A1): G* gate + light-obs q:1:0, DEV 4 jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n4_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; echo "GQ start $(date)"
[ -f $D/sel/choice.json ] || { echo "no N4 choice"; exit 1; }; GS=$($PY -c "import json;print(json.load(open('$D/sel/choice.json'))['G'])"); J=$D/gq_jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do echo "GQ_k${k}_${fl} --n4 0.5:$GS:$M/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt --light-obs q:1:0" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/gq/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n4.py "$@" --seeds 600 601 602 603 604 605 606 607 608 609 610 611 --tag $T --out $D/gq >> $D/gq/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_gq_report.py; echo "GQ done $(date)"
