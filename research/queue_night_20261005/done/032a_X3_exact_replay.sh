#!/usr/bin/env bash
# X3 (PROTOCOL_CITY_N2M_MECHANISM Amendment X3): exact-future fleet on R's replayed schedule, 4 jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n2m_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; echo "X3 start $(date)"; J=$D/x3_jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do echo "RPex_k${k}_${fl} --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt --replay-dir $D/rec_k$k" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u scripts/CITY_m3_headroom.py "$@" --seeds 600 601 602 603 604 605 606 607 608 609 610 611 --tag $T --out $D/dev >> $D/dev/x3.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_x3_report.py; echo "X3 done $(date)"
