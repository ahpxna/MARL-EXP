#!/usr/bin/env bash
# N2 (PROTOCOL_CITY_N2_STATE_FORECAST_20261005): collect 16 TRAIN episodes -> fit k0 / k1 -> KN2 parity -> DEV endpoints (12 jobs) -> report.  4 parallel.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n2_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/m3_20261004/prep; echo "N2 start $(date)"
[ -f research/city_sim/n1_20261005/report_n1.txt ] || { echo "N1 rows missing (R / c2 q0.1): run 020 first"; exit 1; }
J=$D/collect.txt; : > $J; for k in 0 1; do F=s13; [ $k = 1 ] && F=s113; for s in 0 1 2 3 4 5 6 7; do echo "$k $F $s" >> $J; done; done
export PY D P TB; xargs -P 4 -L 1 bash -c '[ -f $D/data/k$0/feat_s$2.npz ] || nice -n 5 $PY -u scripts/CITY_n2_collect.py --featlog $D/data/k$0 --spat-arm fc2:0.1:$TB/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$P/L11_$1_fleet.pt --seeds $2 --tag C_k$0_s$2 --out $D/data/k$0 >> $D/data/run.log 2>&1 || echo "FAIL collect $0 $2"' < $J
for k in 0 1; do [ "$(ls $D/data/k$k/feat_s*.npz | wc -l)" -eq 8 ] || { echo "collection incomplete k$k"; exit 1; }; done; echo "collected $(date)"
for k in 0 1; do $PY -u scripts/CITY_n2_fit.py $k $D/data/k$k $D/model > $D/model/fit_k$k.log 2>&1 & done; wait; tail -1 $D/model/fit_k0.log | cut -c1-200
for k in 0 1; do F=s13; [ $k = 1 ] && F=s113; mkdir -p $D/check/par$k; echo '{"q": 0.1}' > $D/check/par$k/q.json
  $PY -u scripts/CITY_eval_n2.py --n2 0.1:$D/model/n2_k$k.pt --featlog $D/check/par$k --light RL-H:$k --fleet PL:$P/L11_${F}_fleet.pt --seeds 0 --smoke --tag PAR$k --out $D/check/par$k > $D/check/par$k.log 2>&1
  $PY scripts/CITY_n2_parity.py $D/check/par$k 0 $D/model/n2_k$k.pt | tee -a $D/check/parity.txt; done
grep -q FAIL $D/check/parity.txt && { echo "KN2 FAIL: stop"; exit 1; }
J=$D/jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do echo "C2q05_k${k}_${fl} scripts/CITY_eval_n1.py --n1 all:0.5:$TB/prov_rlh${k}_cl.json --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt" >> $J
  echo "N2q01_k${k}_${fl} scripts/CITY_eval_n2.py --n2 0.1:$D/model/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt" >> $J
  echo "N2q05_k${k}_${fl} scripts/CITY_eval_n2.py --n2 0.5:$D/model/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt" >> $J; done; done
xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u "$@" --seeds 600 601 602 603 604 605 606 607 608 609 610 611 --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_n2_report.py; echo "N2 done $(date)"
