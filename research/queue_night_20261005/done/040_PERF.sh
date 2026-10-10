#!/usr/bin/env bash
# PERF (PROTOCOL_CITY_PERF_20261005): pub / shadow with the light adapter q:2:0, DEV 8 jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/perf_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; J=$D/jobs.txt; : > $J; echo "PERF start $(date)"
for k in 0 1; do for fl in s13 s113; do F="--light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt --light-obs q:2:0"
  echo "Apub_k${k}_${fl} --n3 0.5:pub:$M/n2_k$k.pt $F" >> $J; echo "Ash_k${k}_${fl} --n3 0.5:shadow:$M/n2_k$k.pt $F" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n3.py "$@" --seeds 600 601 602 603 604 605 606 607 608 609 610 611 --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_perf_report.py; echo "PERF done $(date)"
