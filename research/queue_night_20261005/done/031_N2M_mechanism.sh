#!/usr/bin/env bash
# N2M (PROTOCOL_CITY_N2M_MECHANISM_20261005): record R phases -> KM-1 -> smoke (replay N2, seed 600) -> panel 28 jobs (4 parallel) -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n2m_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/m3_20261004/prep; M=research/city_sim/n2_20261005/model; echo "N2M start $(date)"
SS="600 601 602 603 604 605 606 607 608 609 610 611"
for k in 0 1; do [ -f $D/dev/Rrec_k$k.json ] || nice -n 5 $PY -u scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet PL:$P/L11_s13_fleet.pt --record "$D/rec_k$k/phases_s{seed}.npz" --seeds $SS --tag Rrec_k$k --out $D/dev > $D/dev/rec_k$k.log 2>&1 & done; wait
for k in 0 1; do [ "$(ls $D/rec_k$k/phases_s*.npz | wc -l)" -eq 12 ] || { echo "recording incomplete k$k"; exit 1; }; done; echo "recorded $(date)"
$PY -u scripts/CITY_eval_n2.py --n2 0.5:$M/n2_k0.pt --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --replay-dir $D/rec_k0 --seeds 600 --smoke --tag SMK_RPn2 --out $D/check > $D/check/smoke.log 2>&1 || { echo "SMOKE FAIL (replay N2)"; tail -5 $D/check/smoke.log; exit 1; }
echo "smoke ok $(date)"
J=$D/jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do F="--light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt"
  echo "RPsig_k${k}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F --replay-dir $D/rec_k$k" >> $J
  echo "RPn2_k${k}_${fl} scripts/CITY_eval_n2.py --n2 0.5:$M/n2_k$k.pt $F --replay-dir $D/rec_k$k" >> $J
  echo "RPc2_k${k}_${fl} scripts/CITY_eval_n1.py --n1 all:0.1:$TB/prov_rlh${k}_cl.json $F --replay-dir $D/rec_k$k" >> $J
  for ab in 10 11; do A=${ab:0:1}; B=${ab:1:1}
    echo "Rq${ab}_k${k}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F --light-obs q:$A:$B" >> $J
    echo "N2q${ab}_k${k}_${fl} scripts/CITY_eval_n2.py --n2 0.5:$M/n2_k$k.pt $F --light-obs q:$A:$B" >> $J; done; done; done
export PY D SS; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u "$@" --seeds $SS --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_n2m_report.py; echo "N2M done $(date)"
